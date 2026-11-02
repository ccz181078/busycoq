(* BB(2,5) prefix-safety family. Mechanically assembled from the checked
   development modules by bb25_merge_family.pl. *)

(* BB25FamilyWord.v *)
From Coq Require Import List ZArith Lia.
Import ListNotations.
Open Scope Z_scope.

Module BB25FamilyWord.

Inductive digit := Y | V | D.
Definition rstep (b : digit) (a : Z) : Z :=
  match b with Y => 2*a+1 | V => 2*a | D => a/2-1 end.
Fixpoint rrun (w : list digit) (a : Z) : Z :=
  match w with [] => a | b::w => rrun w (rstep b a) end.
Definition qout (b : digit) (a : Z) : digit :=
  match b with Y | V => Y | D => if Z.eqb (a mod 2) 1 then V else D end.
Fixpoint trun (w : list digit) (a c : Z) : Z :=
  match w with [] => c | b::w => trun w (rstep b a) (rstep (qout b a) c) end.
Fixpoint bal (w : list digit) : Z :=
  match w with [] => 0 | Y::w => bal w+1 | _::w => bal w-1 end.
Definition DyckPre (w : list digit) : Prop :=
  forall p s, w=p++s -> 0 <= bal p.
Definition Bal (w : list digit) : Prop := DyckPre w /\ bal w=0.
Definition HasCl (w : list digit) : Prop := In V w \/ In D w.
Definition qstep (b : digit) (a : Z) : nat :=
  match b with Y => 0%nat | V => 1%nat
  | D => if Z.eqb (a mod 2) 1 then 1%nat else 0%nat end.
Fixpoint qcnt (w : list digit) (a : Z) : nat :=
  match w with [] => 0%nat | b::w => (qstep b a + qcnt w (rstep b a))%nat end.
Fixpoint wpow (b : Z) (n : nat) : Z :=
  match n with O => 1 | S n => b * wpow b n end.
Definition pow2 := wpow 2.
Definition pow4 := wpow 4.
Fixpoint qloss (q : nat) : Z :=
  match q with O => 0 | S q => 4*qloss q+1 end.
Definition qgain (q : nat) (c : Z) : Z := pow4 q*(c+1)-qloss q.

Lemma rrun_app w v a : rrun (w++v) a=rrun v (rrun w a).
Proof. revert a; induction w; intros; simpl; auto. Qed.
Lemma trun_app w v a c : trun (w++v) a c=trun v (rrun w a) (trun w a c).
Proof. revert a c; induction w; intros; simpl; auto. Qed.
Lemma qcnt_app w v a : qcnt (w++v) a=(qcnt w a+qcnt v (rrun w a))%nat.
Proof. revert a; induction w; intros; simpl; rewrite ?IHw; lia. Qed.
Lemma bal_app w v : bal (w++v)=bal w+bal v.
Proof. induction w as [|b w IH]; simpl; [lia|destruct b; simpl; rewrite IH; lia]. Qed.
Lemma rstep_mono b a a' : a<=a' -> rstep b a<=rstep b a'.
Proof. destruct b; unfold rstep; intros H; try lia. apply Z.sub_le_mono_r, Z.div_le_mono; lia. Qed.
Lemma rrun_mono w a a' : a<=a' -> rrun w a<=rrun w a'.
Proof. revert a a'; induction w; simpl; auto using rstep_mono. Qed.
Lemma div2_bounds a : 2*(a/2)<=a /\ a<2*(a/2)+2.
Proof. pose proof (Z.div_mod a 2 ltac:(lia)); pose proof (Z.mod_pos_bound a 2 ltac:(lia)); lia. Qed.
Lemma rstep_neg b a : a<0 -> rstep b a<0.
Proof. destruct b; unfold rstep; pose proof (div2_bounds a); lia. Qed.
Lemma rrun_neg w a : a<0 -> rrun w a<0.
Proof. revert a; induction w; simpl; auto using rstep_neg. Qed.
Lemma rrun_nonneg_of_nonneg w v a : 0<=rrun (w++v) a -> 0<=rrun w a.
Proof. rewrite rrun_app; intros H; destruct (Z_lt_ge_dec (rrun w a) 0) as [Hl|Hl]; [pose proof (rrun_neg v _ Hl)|]; lia. Qed.
Lemma rrun_nonneg_head b w a : 0<=rrun (b::w) a -> 0<=rstep b a.
Proof. apply (rrun_nonneg_of_nonneg [b] w a). Qed.

Lemma dyck_nil : DyckPre [].
Proof. intros p s H; destruct p; simpl in *; [lia|discriminate]. Qed.
Lemma dyck_prefix p s : DyckPre (p++s) -> DyckPre p.
Proof. intros H q r E; apply (H q (r++s)); subst; symmetry; apply app_assoc. Qed.
Lemma dyck_nonneg w : DyckPre w -> 0<=bal w.
Proof. intro H; apply (H w []); now rewrite app_nil_r. Qed.
Lemma prefix_app_cases (p w v : list digit) :
  (exists s,w++v=p++s) ->
  (exists s,w=p++s) \/ (exists q,p=w++q /\ exists s,v=q++s).
Proof.
  revert p; induction w as [|b w IH]; intros p [s H].
  - right; exists p; split; auto; now exists s.
  - destruct p as [|x p].
    + left; exists (b::w); reflexivity.
    + simpl in H; injection H as E H; subst x.
      destruct (IH p (ex_intro _ s H)) as [[r Hr]|[q [Hp [r Hr]]]].
      * left; exists r; simpl; now rewrite Hr.
      * right; exists q; split; [simpl; now rewrite Hp|now exists r].
Qed.
Lemma prefix_singleton (p : list digit) b :
  (exists s,[b]=p++s) -> p=[] \/ p=[b].
Proof. destruct p as [|x [|y p]]; intros [s H]; simpl in H; try discriminate; [auto|injection H as E; subst; auto]. Qed.
Lemma dyck_app w v : DyckPre w -> DyckPre v -> DyckPre (w++v).
Proof.
  intros Hw Hv p s H; destruct (prefix_app_cases p w v (ex_intro _ s H)) as [[r Hr]|[q [-> [r Hr]]]].
  - exact (Hw p r Hr).
  - rewrite bal_app; pose proof (dyck_nonneg _ Hw); pose proof (Hv q r Hr); lia.
Qed.
Lemma dyck_Y w : DyckPre w -> DyckPre (Y::w).
Proof. intros H [|b p] s E; simpl; [lia|]. simpl in E; injection E as Eb E; subst b; specialize (H p s E); simpl; lia. Qed.
Lemma dyck_wrap e b : Bal e -> b<>Y -> DyckPre (Y::(e++[b])).
Proof.
  intros [Hd He] Hb [|x p] s E; simpl; [lia|].
  simpl in E; injection E as Ex E; subst x; simpl.
  destruct (prefix_app_cases p e [b] (ex_intro _ s E)) as [[r Hr]|[q [-> Hq]]].
  - specialize (Hd p r Hr); lia.
  - destruct (prefix_singleton q b Hq) as [Eq|Eq]; subst q; rewrite bal_app, He; destruct b; simpl; congruence || lia.
Qed.
Lemma no_close_repeat w : ~HasCl w -> w=repeat Y (length w).
Proof.
  induction w as [|b w IH]; simpl; auto; intros H.
  assert (Hw : ~HasCl w) by (unfold HasCl in *; simpl in H; tauto).
  destruct b; simpl; [f_equal; exact (IH Hw)|exfalso; apply H; left; now left|exfalso; apply H; right; now left].
Qed.
Lemma bal_repeat_Y n : bal (repeat Y n)=Z.of_nat n.
Proof. induction n; [reflexivity|cbn [repeat bal]; rewrite IHn, Nat2Z.inj_succ; lia]. Qed.
Lemma bal_has_close w : Bal w -> w<>[] -> HasCl w.
Proof.
  intros [_ Hb] Hn; destruct (in_dec (fun a b:digit => ltac:(decide equality)) V w), (in_dec (fun a b:digit => ltac:(decide equality)) D w); try (unfold HasCl; tauto).
  assert (E : w=repeat Y (length w)) by (apply no_close_repeat; unfold HasCl; tauto).
  rewrite E, bal_repeat_Y in Hb; destruct w; simpl in *; congruence || lia.
Qed.
Lemma wpow_add b n m : wpow b (n+m)=wpow b n*wpow b m.
Proof. induction n; cbn [Nat.add wpow]; [ring|rewrite IHn; ring]. Qed.
Lemma wpow_pos b n : 1<=b -> 1<=wpow b n.
Proof. intros H; induction n; cbn [wpow]; nia. Qed.
Lemma wpow_mono b n m : 1<=b -> (n<=m)%nat -> wpow b n<=wpow b m.
Proof. intros Hb H; induction H; [lia|cbn [wpow]; pose proof (wpow_pos b m Hb); nia]. Qed.
Lemma pow2_pos n : 1<=pow2 n.
Proof. apply wpow_pos; lia. Qed.
Lemma pow4_pos n : 1<=pow4 n.
Proof. apply wpow_pos; lia. Qed.
Lemma pow2_succ n : pow2 (S n)=2*pow2 n. Proof. reflexivity. Qed.
Lemma pow4_succ n : pow4 (S n)=4*pow4 n. Proof. reflexivity. Qed.
Lemma pow2_add n m : pow2 (n+m)=pow2 n*pow2 m. Proof. apply wpow_add. Qed.
Lemma pow4_add n m : pow4 (n+m)=pow4 n*pow4 m. Proof. apply wpow_add. Qed.
Lemma pow2_mono n m : (n<=m)%nat -> pow2 n<=pow2 m. Proof. apply wpow_mono; lia. Qed.
Lemma pow2_lt n m : pow2 n<pow2 m -> (n<m)%nat.
Proof. intro H; destruct (le_lt_dec m n); [pose proof (pow2_mono m n l); lia|assumption]. Qed.
Lemma pow4_two n : pow4 n=pow2 (2*n).
Proof. induction n; [reflexivity|replace (2*S n)%nat with (S (S (2*n))) by lia; rewrite pow4_succ, !pow2_succ, IHn; ring]. Qed.
Lemma rrun_repeat_Y n a : rrun (repeat Y n) a=pow2 n*(a+1)-1.
Proof. revert a; induction n; intros; cbn [repeat rrun]; [change (a=1*(a+1)-1); ring|rewrite IHn, pow2_succ; unfold rstep; ring]. Qed.
Lemma qloss_nonneg q : 0<=qloss q. Proof. induction q; cbn [qloss]; lia. Qed.
Lemma qloss_pos q : (1<=q)%nat -> 1<=qloss q.
Proof. destruct q; cbn [qloss]; [lia|pose proof (qloss_nonneg q); lia]. Qed.
Lemma qloss_add i j : qloss (i+j)=pow4 j*qloss i+qloss j.
Proof. induction j; [rewrite Nat.add_0_r; change (qloss i=1*qloss i+0); ring|rewrite Nat.add_succ_r; cbn [qloss]; rewrite IHj, pow4_succ; ring]. Qed.
Lemma qgain_zero c : qgain 0 c=c+1. Proof. unfold qgain; change (1*(c+1)-0=c+1); ring. Qed.
Lemma qgain_succ q c : qgain (S q) c=4*qgain q c-1.
Proof. unfold qgain; rewrite pow4_succ; cbn [qloss]; ring. Qed.
Lemma qgain_pos q c : 0<=c -> 1<=qgain q c.
Proof. intro H; induction q; [rewrite qgain_zero|rewrite qgain_succ]; lia. Qed.
Lemma qgain_mono q Q c : 0<=c -> (q<=Q)%nat -> qgain q c<=qgain Q c.
Proof. intros Hc H; induction H; [lia|rewrite qgain_succ; pose proof (qgain_pos m c Hc); lia]. Qed.
Lemma qgain_add i j c : qgain (i+j) c=pow4 j*qgain i c-qloss j.
Proof. unfold qgain; rewrite qloss_add, pow4_add; ring. Qed.
Lemma qgain_double j c : qgain j (2*c+1)=2*(pow4 j*(c+1))-qloss j.
Proof. unfold qgain; ring. Qed.
Lemma three_qloss q : 3*qloss q=pow4 q-1.
Proof. induction q; [reflexivity|cbn [qloss]; rewrite pow4_succ; lia]. Qed.

Lemma list_snoc (w : list digit) : w=[] \/ exists p b,w=p++[b].
Proof. induction w using rev_ind; [now left|right; eauto]. Qed.
Lemma dyck_split_aux n : forall p, (length p<=n)%nat -> DyckPre p -> 1<=bal p ->
  exists q e,p=q++Y::e /\ DyckPre q /\ Bal e.
Proof.
  induction n as [|n IH]; intros p Hl Hd Hb.
  - destruct p; simpl in *; lia.
  - destruct (list_snoc p) as [->|[u [b ->]]]; [simpl in Hb; lia|].
    assert (Hu : DyckPre u) by (eapply dyck_prefix; eassumption).
    assert (Hlu : (length u<=n)%nat) by (rewrite app_length in Hl; simpl in Hl; lia).
    destruct b.
    + exists u,[]; repeat split; auto using dyck_nil.
    + assert (Hb' : 2<=bal u) by (rewrite bal_app in Hb; simpl in Hb; lia).
      destruct (IH u Hlu Hu ltac:(lia)) as [q [e [Eu [Hq [He Be]]]]].
      assert (Hq' : 1<=bal q) by (rewrite Eu, bal_app in Hb'; simpl in Hb'; lia).
      assert (Hlq : (length q<=n)%nat) by (rewrite Eu, app_length in Hlu; simpl in Hlu; lia).
      destruct (IH q Hlq Hq Hq') as [q' [e' [Eq [Hdq' [He' Be']]]]].
      exists q',(e'++Y::(e++[V])); split.
      * rewrite Eu, Eq; rewrite <- !app_assoc; reflexivity.
      * split; [exact Hdq'|split].
        -- apply dyck_app; auto; apply dyck_wrap; [split; auto|discriminate].
        -- rewrite bal_app, Be'; simpl; rewrite bal_app, Be; reflexivity.
    + assert (Hb' : 2<=bal u) by (rewrite bal_app in Hb; simpl in Hb; lia).
      destruct (IH u Hlu Hu ltac:(lia)) as [q [e [Eu [Hq [He Be]]]]].
      assert (Hq' : 1<=bal q) by (rewrite Eu, bal_app in Hb'; simpl in Hb'; lia).
      assert (Hlq : (length q<=n)%nat) by (rewrite Eu, app_length in Hlu; simpl in Hlu; lia).
      destruct (IH q Hlq Hq Hq') as [q' [e' [Eq [Hdq' [He' Be']]]]].
      exists q',(e'++Y::(e++[D])); split.
      * rewrite Eu, Eq; rewrite <- !app_assoc; reflexivity.
      * split; [exact Hdq'|split].
        -- apply dyck_app; auto; apply dyck_wrap; [split; auto|discriminate].
        -- rewrite bal_app, Be'; simpl; rewrite bal_app, Be; reflexivity.
Qed.
Lemma dyck_split p : DyckPre p -> 1<=bal p ->
  exists q e,p=q++Y::e /\ DyckPre q /\ Bal e.
Proof. apply (dyck_split_aux (length p) p); lia. Qed.
Lemma split_first_close w : HasCl w ->
  exists k b rest,b<>Y /\ w=repeat Y k++b::rest.
Proof.
  induction w as [|b w IH]; intros H; [unfold HasCl in H; simpl in H; tauto|].
  destruct b.
  - assert (Hw : HasCl w) by (unfold HasCl in *; simpl in H; intuition congruence).
    destruct (IH Hw) as [k [b [r [Hb E]]]]; exists (S k),b,r; split; auto; simpl; now rewrite E.
  - exists 0%nat,V,w; split; [discriminate|reflexivity].
  - exists 0%nat,D,w; split; [discriminate|reflexivity].
Qed.
Lemma qcnt_pos_of_hasCl w a : DyckPre w -> HasCl w -> (1<=qcnt w a)%nat.
Proof.
  intros Hd Hc; destruct (split_first_close w Hc) as [k [b [r [Hb ->]]]].
  destruct k as [|k].
  - pose proof (Hd [b] r eq_refl); destruct b; simpl in *; congruence || lia.
  - rewrite qcnt_app.
    change (1<=qcnt (repeat Y (S k)) a +
      (qstep b (rrun (repeat Y (S k)) a)+qcnt r (rstep b (rrun (repeat Y (S k)) a))))%nat.
    assert (Ho : rrun (repeat Y (S k)) a mod 2=1).
    { rewrite rrun_repeat_Y, pow2_succ.
      pose proof (Z.mod_pos_bound (2*pow2 k*(a+1)-1) 2 ltac:(lia)).
      pose proof (Z.div_mod (2*pow2 k*(a+1)-1) 2 ltac:(lia)); nia. }
    destruct b; [contradiction|unfold qstep; lia|unfold qstep; rewrite Ho; cbn; lia].
Qed.

Lemma trun_gain_exact_aux n : forall w, (length w<=n)%nat -> DyckPre w ->
  forall h,bal w=Z.of_nat h -> forall a c,0<=c ->
  pow2 h*qgain (qcnt w a) c<=trun w a c+1.
Proof.
  induction n as [|n IH]; intros w Hl Hd h Hb a c Hc.
  - destruct w; simpl in Hl; [|lia]. simpl in Hb; assert (h=0%nat) by lia; subst h.
    cbn [qcnt trun pow2 wpow]; rewrite qgain_zero; lia.
  - destruct (list_snoc w) as [->|[p [b ->]]].
    + simpl in Hb; assert (h=0%nat) by lia; subst h.
      cbn [qcnt trun pow2 wpow]; rewrite qgain_zero; lia.
    + assert (Hp : DyckPre p) by (eapply dyck_prefix; eassumption).
      assert (Hlp : (length p<=n)%nat) by (rewrite app_length in Hl; simpl in Hl; lia).
      pose proof (dyck_nonneg p Hp) as Hbp.
      pose proof (pow2_pos h) as Hph.
      rewrite bal_app in Hb.
      rewrite trun_app, qcnt_app; cbn [trun qcnt].
      destruct b.
      * simpl in Hb; destruct h as [|h]; [lia|].
        assert (Hb' : bal p=Z.of_nat h) by (rewrite Nat2Z.inj_succ in Hb; lia).
        pose proof (IH p Hlp Hp h Hb' a c Hc) as A.
        cbn [qstep qout rstep]; rewrite Nat.add_0_r, pow2_succ; lia.
      * simpl in Hb; assert (Hb' : bal p=Z.of_nat (S h)) by (rewrite Nat2Z.inj_succ; lia).
        pose proof (IH p Hlp Hp (S h) Hb' a c Hc) as A.
        rewrite pow2_succ in A; cbn [qstep qout rstep].
        rewrite Nat.add_1_r, qgain_succ; nia.
      * simpl in Hb; assert (Hb' : bal p=Z.of_nat (S h)) by (rewrite Nat2Z.inj_succ; lia).
        cbn [qstep qout]. destruct (Z.eqb (rrun p a mod 2) 1) eqn:Ho.
        -- pose proof (IH p Hlp Hp (S h) Hb' a c Hc) as A.
           rewrite pow2_succ in A; cbn [rstep].
           rewrite Nat.add_1_r, qgain_succ; nia.
        -- rewrite Nat.add_0_r; cbn [rstep].
           destruct (dyck_split p Hp ltac:(lia)) as [u [e [Ep [Hu [He Be]]]]].
           assert (Hlu : (length u<=n)%nat) by (rewrite Ep, app_length in Hlp; simpl in Hlp; lia).
           assert (Hle : (length e<=n)%nat) by (rewrite Ep, app_length in Hlp; simpl in Hlp; lia).
           assert (Hbu : bal u=Z.of_nat h) by (rewrite Ep, bal_app in Hb; simpl in Hb; lia).
           set (cu:=trun u a c). set (au:=rrun u a).
           set (qe:=qcnt e (2*au+1)). set (qu:=qcnt u a).
           set (cc:=trun e (2*au+1) (2*cu+1)).
           assert (Eq : qcnt p a=(qu+qe)%nat).
           { rewrite Ep, qcnt_app; cbn [qcnt qstep rstep]; reflexivity. }
           assert (Et : trun p a c=cc).
           { rewrite Ep, trun_app; cbn [trun qout rstep]; reflexivity. }
           assert (En : e<>[]).
           { intro E; subst e; rewrite Ep, rrun_app in Ho; cbn [rrun rstep] in Ho.
             apply Z.eqb_neq in Ho. pose proof (div2_bounds (2*rrun u a+1)).
             pose proof (Z.div_mod (2*rrun u a+1) 2 ltac:(lia)).
             pose proof (Z.mod_pos_bound (2*rrun u a+1) 2 ltac:(lia)); nia. }
           assert (Hqe : (1<=qe)%nat) by (apply qcnt_pos_of_hasCl; [exact He|apply bal_has_close; auto; split; auto]).
           pose proof (IH u Hlu Hu h Hbu a c Hc) as A.
           change (pow2 h*qgain qu c<=cu+1) in A.
           assert (Hcu : 0<=cu) by (pose proof (qgain_pos qu c Hc); nia).
           pose proof (IH e Hle He 0%nat Be (2*au+1) (2*cu+1) ltac:(lia)) as B.
           change (1*qgain qe (2*cu+1)<=cc+1) in B.
           rewrite qgain_double in B.
           rewrite Eq, Et, qgain_add.
           pose proof (pow4_pos qe) as HE; pose proof (qloss_pos qe Hqe) as HM.
           pose proof (Z.mul_le_mono_nonneg_l _ _ (2*pow4 qe) ltac:(lia) A) as HA.
           pose proof (div2_bounds cc) as HC.
           nia.
Qed.
Theorem trun_ge_qgain w h a c q : DyckPre w -> bal w=Z.of_nat h -> 0<=c ->
  (q<=qcnt w a)%nat -> pow2 h*qgain q c<=trun w a c+1.
Proof.
  intros Hd Hb Hc Hq; pose proof (trun_gain_exact_aux (length w) w ltac:(lia) Hd h Hb a c Hc).
  pose proof (qgain_mono q (qcnt w a) c Hc Hq); pose proof (pow2_pos h); nia.
Qed.
Corollary trun_ge_pow_q1 w h a c : DyckPre w -> bal w=Z.of_nat h -> 0<=c ->
  (1<=qcnt w a)%nat -> pow2 h*(4*c+3)-1<=trun w a c.
Proof. intros Hd Hb Hc Hq; pose proof (trun_ge_qgain w h a c 1 Hd Hb Hc Hq); change (pow2 h*qgain (S O) c<=trun w a c+1) in H; rewrite qgain_succ, qgain_zero in H; nia. Qed.
Corollary trun_ge_pow_q2 w h a c : DyckPre w -> bal w=Z.of_nat h -> 0<=c ->
  (2<=qcnt w a)%nat -> pow2 h*(16*c+11)-1<=trun w a c.
Proof. intros Hd Hb Hc Hq; pose proof (trun_ge_qgain w h a c 2 Hd Hb Hc Hq); change (pow2 h*qgain (S (S O)) c<=trun w a c+1) in H; rewrite !qgain_succ, qgain_zero in H; nia. Qed.
Theorem trun_ge_of_hasCl w a c : DyckPre w -> HasCl w -> 0<=c -> 4*c+2<=trun w a c.
Proof.
  intros Hd Hcl Hc; pose proof (dyck_nonneg w Hd) as Hb.
  pose proof (qcnt_pos_of_hasCl w a Hd Hcl) as Hq.
  pose proof (trun_ge_pow_q1 w (Z.to_nat (bal w)) a c Hd ltac:(rewrite Z2Nat.id; lia) Hc Hq).
  pose proof (pow2_pos (Z.to_nat (bal w))); nia.
Qed.
Theorem trun_ge_two w : DyckPre w -> w<>[] -> rrun w 0=0 -> 2<=trun w 0 0.
Proof.
  intros Hd Hn Hr; assert (Hcl : HasCl w).
  { destruct (in_dec (fun a b:digit => ltac:(decide equality)) V w), (in_dec (fun a b:digit => ltac:(decide equality)) D w); try (unfold HasCl; tauto).
    assert (E : w=repeat Y (length w)) by (apply no_close_repeat; unfold HasCl; tauto).
    rewrite E, rrun_repeat_Y in Hr.
    assert (Hl : (1<=length w)%nat) by (destruct w; simpl in *; congruence || lia).
    pose proof (pow2_mono 1 (length w) Hl); cbn [pow2 wpow] in H; nia. }
  pose proof (trun_ge_of_hasCl w 0 0 Hd Hcl ltac:(lia)); lia.
Qed.

Definition Shape (a : Z) (h q : nat) : Prop :=
  (q=0%nat /\ a+1=pow2 h) \/
  (q=1%nat /\ exists k,(k<=h)%nat /\
    (a+1=pow2 h-pow2 k \/ a+1=pow2 (h+2)-pow2 k)) \/ (2<=q)%nat.
Lemma shape_step b a h q h' : Shape a h q ->
  Z.of_nat h'=Z.of_nat h+bal [b] -> 0<=rstep b a ->
  Shape (rstep b a) h' (q+qstep b a).
Proof.
  intros Hs Hh Ha; destruct b.
  - assert (E : h'=S h) by (cbn [bal] in Hh; lia); subst h'.
    cbn [rstep qstep]; rewrite Nat.add_0_r; unfold Shape in *.
    destruct Hs as [[Hq Hv]|[[Hq [k [Hk [Hv|Hv]]]]|Hq]].
    + left; split; [exact Hq|rewrite pow2_succ; lia].
    + right; left; split; [exact Hq|exists (S k); split; [lia|left; rewrite !pow2_succ; lia]].
    + right; left; split; [exact Hq|exists (S k); split; [lia|right; change (2*a+1+1=pow2 (S (h+2))-pow2 (S k)); rewrite !pow2_succ; lia]].
    + right; right; exact Hq.
  - assert (E : h=S h') by (cbn [bal] in Hh; lia); subst h.
    cbn [rstep qstep]; unfold Shape in *.
    destruct Hs as [[Hq Hv]|[[Hq Hk]|Hq]].
    + right; left; split; [lia|exists 0%nat; split; [lia|right]].
      rewrite pow2_succ in Hv; replace (h'+2)%nat with (S (S h')) by lia.
      change (2*a+1=pow2 (S (S h'))-1); rewrite !pow2_succ; lia.
    + right; right; lia.
    + right; right; lia.
  - assert (E : h=S h') by (cbn [bal] in Hh; lia); subst h.
    cbn [rstep] in Ha |- *; unfold qstep.
    pose proof (div2_bounds a) as Hd.
    pose proof (Z.div_mod a 2 ltac:(lia)) as He.
    pose proof (Z.mod_pos_bound a 2 ltac:(lia)) as Hm.
    destruct (Z.eqb (a mod 2) 1) eqn:Ho.
    + apply Z.eqb_eq in Ho; unfold Shape in *.
      destruct Hs as [[Hq Hv]|[[Hq Hk]|Hq]].
      * right; left; split; [lia|exists 0%nat; split; [lia|left]].
        rewrite pow2_succ in Hv; change (a/2-1+1=pow2 h'-1); lia.
      * right; right; lia.
      * right; right; lia.
    + apply Z.eqb_neq in Ho; rewrite Nat.add_0_r; unfold Shape in *.
      destruct Hs as [[Hq Hv]|[[Hq [k [Hk Hv]]]|Hq]].
      * rewrite pow2_succ in Hv; exfalso; lia.
      * assert (Ek : k=0%nat).
        { destruct k as [|k]; [reflexivity|].
          destruct Hv as [Hv|Hv].
          - rewrite !pow2_succ in Hv; exfalso; lia.
          - change (a+1=pow2 (S (h'+2))-pow2 (S k)) in Hv.
            rewrite !pow2_succ in Hv; exfalso; lia. }
        subst k; right; left; split; [exact Hq|exists 0%nat; split; [lia|]].
        change (a/2-1+1=pow2 h'-1 \/ a/2-1+1=pow2 (h'+2)-1).
        destruct Hv as [Hv|Hv].
        -- change (a+1=pow2 (S h')-1) in Hv; rewrite pow2_succ in Hv; left; lia.
        -- change (a+1=pow2 (S (h'+2))-1) in Hv; rewrite pow2_succ in Hv; right; lia.
      * right; right; exact Hq.
Qed.
Theorem shape_run w h : DyckPre w -> bal w=Z.of_nat h -> 0<=rrun w 0 ->
  Shape (rrun w 0) h (qcnt w 0).
Proof.
  revert h; induction w using rev_ind; intros h Hd Hb Hr.
  - cbn [bal] in Hb; assert (h=0%nat) by lia; subst h; left; split; reflexivity.
  - assert (Hp : DyckPre w) by (eapply dyck_prefix; eassumption).
    pose proof (dyck_nonneg w Hp) as Hbp.
    assert (Ep : bal w=Z.of_nat (Z.to_nat (bal w))) by (rewrite Z2Nat.id; lia).
    assert (Hrp : 0<=rrun w 0) by (eapply rrun_nonneg_of_nonneg; eassumption).
    pose proof (IHw (Z.to_nat (bal w)) Hp Ep Hrp) as Hs.
    rewrite rrun_app in Hr |- *; rewrite qcnt_app; cbn [rrun qcnt]; rewrite Nat.add_0_r.
    eapply shape_step; [exact Hs|rewrite bal_app in Hb; lia|exact Hr].
Qed.
Lemma pow2_even n : (1<=n)%nat -> exists a,pow2 n=2*a.
Proof. destruct n; [lia|intros; exists (pow2 n); reflexivity]. Qed.
Lemma pow2_four n : (2<=n)%nat -> exists a,pow2 n=4*a.
Proof. destruct n as [|[|n]]; try lia; intros; exists (pow2 n); rewrite !pow2_succ; ring. Qed.
Theorem rrun_shape_le_one w h : DyckPre w -> bal w=Z.of_nat h -> 0<=rrun w 0 ->
  (qcnt w 0<=1)%nat -> (2<=h)%nat ->
  rrun w 0 mod 2=1 \/ exists e,(2<=e)%nat /\ rrun w 0=pow2 e-2.
Proof.
  intros Hd Hb Hr Hq Hh; pose proof (shape_run w h Hd Hb Hr) as Hs.
  destruct (pow2_even h ltac:(lia)) as [u Hu].
  pose proof (Z.mod_pos_bound (rrun w 0) 2 ltac:(lia)) as Hm.
  pose proof (Z.div_mod (rrun w 0) 2 ltac:(lia)) as He.
  destruct Hs as [[Hq0 Hv]|[[Hq1 [k [Hk Hv]]]|Hq2]].
  - left; lia.
  - destruct k as [|k].
    + right; change (rrun w 0+1=pow2 h-1 \/ rrun w 0+1=pow2 (h+2)-1) in Hv.
      destruct Hv as [Hv|Hv]; [exists h|exists (h+2)%nat]; split; lia.
    + destruct (pow2_even (h+2)%nat ltac:(lia)) as [v Hv'].
      destruct Hv as [Hv|Hv]; rewrite pow2_succ in Hv; left; lia.
  - lia.
Qed.
Theorem rrun_mod_four_ne w h : DyckPre w -> bal w=Z.of_nat h -> 0<=rrun w 0 ->
  (qcnt w 0<=1)%nat -> (2<=h)%nat -> rrun w 0 mod 4<>0.
Proof.
  intros Hd Hb Hr Hq Hh Hm; pose proof (rrun_shape_le_one w h Hd Hb Hr Hq Hh) as Hs.
  pose proof (Z.div_mod (rrun w 0) 4 ltac:(lia)) as H4.
  destruct Hs as [H2|[e [He Hv]]].
  - pose proof (Z.div_mod (rrun w 0) 2 ltac:(lia)); lia.
  - destruct (pow2_four e He) as [u Hu]; lia.
Qed.

Lemma rrun_le_product w h a : DyckPre w -> bal w=Z.of_nat h -> 0<=a ->
  0<=rrun w a -> rrun w a+1<=pow2 h*pow4 (qcnt w a)*(a+1).
Proof.
  revert h a; induction w using rev_ind; intros h a Hd Hb Ha Hr.
  - cbn [bal] in Hb; assert (h=0%nat) by lia; subst h.
    change (a+1<=1*1*(a+1)); lia.
  - assert (Hp : DyckPre w) by (eapply dyck_prefix; eassumption).
    pose proof (dyck_nonneg w Hp) as Hbp.
    assert (Hrp : 0<=rrun w a) by (eapply rrun_nonneg_of_nonneg; eassumption).
    rewrite bal_app in Hb; rewrite rrun_app, qcnt_app; cbn [rrun qcnt]; rewrite Nat.add_0_r.
    destruct x.
    + cbn [bal] in Hb; destruct h as [|h]; [lia|].
      assert (Hb' : bal w=Z.of_nat h) by (rewrite Nat2Z.inj_succ in Hb; lia).
      pose proof (IHw h a Hp Hb' Ha Hrp) as A.
      cbn [rstep qstep]; rewrite Nat.add_0_r, pow2_succ; nia.
    + cbn [bal] in Hb; assert (Hb' : bal w=Z.of_nat (S h)) by (rewrite Nat2Z.inj_succ; lia).
      pose proof (IHw (S h) a Hp Hb' Ha Hrp) as A.
      cbn [rstep qstep]; rewrite Nat.add_1_r, pow4_succ; rewrite pow2_succ in A; nia.
    + cbn [bal] in Hb; assert (Hb' : bal w=Z.of_nat (S h)) by (rewrite Nat2Z.inj_succ; lia).
      pose proof (IHw (S h) a Hp Hb' Ha Hrp) as A.
      pose proof (div2_bounds (rrun w a)) as HB.
      cbn [rstep qstep]; rewrite pow2_succ in A.
      destruct (Z.eqb (rrun w a mod 2) 1).
      * rewrite Nat.add_1_r, pow4_succ; nia.
      * rewrite Nat.add_0_r; nia.
Qed.
Theorem rrun_le_two_pow w h a : DyckPre w -> bal w=Z.of_nat h -> 0<=a ->
  0<=rrun w a -> rrun w a+1<=pow2 (h+2*qcnt w a)*(a+1).
Proof. intros; rewrite pow2_add, <-pow4_two; now apply rrun_le_product. Qed.
Lemma two_pow_diff_two h e : (1<=h)%nat -> (1<=e)%nat ->
  pow2 h-pow2 e=2 -> h=2%nat /\ e=1%nat.
Proof.
  destruct h as [|h],e as [|e]; try lia; intros Hh He Hv.
  rewrite !pow2_succ in Hv.
  pose proof (pow2_pos h) as Hp; pose proof (pow2_pos e) as Hq.
  destruct e as [|e].
  - change (2*pow2 h-2*1=2) in Hv.
    destruct h as [|[|h]]; [cbn in Hv; lia|auto|].
    rewrite !pow2_succ in Hv; pose proof (pow2_pos h); nia.
  - rewrite pow2_succ in Hv.
    destruct h as [|h].
    + change (2*1-2*(2*pow2 e)=2) in Hv; pose proof (pow2_pos e); nia.
    + rewrite pow2_succ in Hv; lia.
Qed.
Theorem trun_gt_of_pow w h e : DyckPre w -> bal w=Z.of_nat h ->
  (1<=h)%nat -> (1<=e)%nat -> rrun w 0=pow2 e -> rrun w 0+2<=trun w 0 0.
Proof.
  intros Hd Hb Hh He Hv.
  pose proof (pow2_mono 1 e He) as Hpe; change (2<=pow2 e) in Hpe.
  assert (Hr : 0<=rrun w 0) by lia.
  destruct (pow2_even h Hh) as [u Hu]; destruct (pow2_even e He) as [v Hve].
  pose proof (shape_run w h Hd Hb Hr) as Hs.
  destruct Hs as [[Hq0 Hs]|[[Hq1 [k [Hk Hs]]]|Hq2]].
  - lia.
  - assert (Ek : k=0%nat).
    { destruct k as [|k]; [reflexivity|].
      destruct (pow2_even (h+2)%nat ltac:(lia)) as [u' Hu'].
      destruct Hs as [Hs|Hs]; rewrite pow2_succ in Hs; exfalso; lia. }
    subst k; change (rrun w 0+1=pow2 h-1 \/ rrun w 0+1=pow2 (h+2)-1) in Hs.
    assert (Hhe : h=2%nat /\ e=1%nat).
    { destruct Hs as [Hs|Hs].
      - apply two_pow_diff_two; auto; lia.
      - pose proof (two_pow_diff_two (h+2)%nat e ltac:(lia) He ltac:(lia)); lia. }
    destruct Hhe as [-> ->].
    pose proof (trun_ge_pow_q1 w 2 0 0 Hd Hb ltac:(lia) ltac:(lia)) as HT.
    change (4*(4*0+3)-1<=trun w 0 0) in HT; change (rrun w 0=2) in Hv; lia.
  - pose proof (rrun_le_two_pow w h 0 Hd Hb ltac:(lia) Hr) as HU.
    replace (0+1) with 1 in HU by lia; rewrite Z.mul_1_r in HU.
    assert (Hel : (e<h+2*qcnt w 0)%nat) by (apply pow2_lt; lia).
    pose proof (pow2_mono (S e) (h+2*qcnt w 0)%nat ltac:(lia)) as HF.
    rewrite pow2_succ, <-Hv in HF.
    pose proof (pow2_mono 5 (h+2*qcnt w 0)%nat ltac:(lia)) as HB.
    change (32<=pow2 (h+2*qcnt w 0)) in HB.
    pose proof (pow2_mono 1 h Hh) as HP; change (2<=pow2 h) in HP.
    pose proof (trun_ge_qgain w h 0 0 (qcnt w 0) Hd Hb ltac:(lia) ltac:(lia)) as HG.
    pose proof (three_qloss (qcnt w 0)) as HL.
    unfold qgain in HG; replace (0+1) with 1 in HG by lia; rewrite Z.mul_1_r in HG.
    rewrite pow2_add, <-pow4_two in HF, HB.
    nia.
Qed.

Example word_low_counter : rrun [Y;Y;D] 0=0 /\ 2<=trun [Y;Y;D] 0 0.
Proof. split; [reflexivity|change (2<=6); lia]. Qed.
Example word_sharp_bound : trun [Y;Y;V;D;Y;D] 0 0=10.
Proof. reflexivity. Qed.

End BB25FamilyWord.

(* BB25FamilyCore.v *)
Close Scope Z_scope. Close Scope N_scope.
From BusyCoq Require Import Individual25.
Open Scope sym_scope.
From Coq Require Import List NArith ZArith Lia.
Import ListNotations.

(* Pure stack algebra for the BB(2,5) prefix-safety family.  The bottom11
   is implicit; all words contain only the three actual counter tokens. *)
Module BB25FamilyCore.
Inductive tok := Z | X | W.
Fixpoint dec (d:nat) (w:list tok) {struct w} : option (list tok) :=
  match w with
  | []=>None
  | W::w=>option_map (cons W) (dec (S d) w)
  | X::w=>match d with O=>option_map (cons Z) (dec O w)
                      | S d=>option_map (cons X) (dec d w) end
  | Z::w=>match d with O=>Some(X::w)
                      | S d=>option_map (cons Z) (dec d w) end end.
Definition obind {X Y} (v:option X) (f:X->option Y) :=
  match v with None=>None | Some x=>f x end.
Lemma dec_length w : forall d v, dec d w=Some v -> length v=length w.
Proof.
  induction w as [|t w IH]; intros d v H; [discriminate|].
  destruct t,d; cbn[dec] in H;
    try (destruct (dec _ w) as [u|] eqn:E; [|discriminate]);
    inversion H; subst; cbn; eauto.
Qed.
Lemma dec_double w : forall d, dec (S d) w=obind (dec d w) (dec d).
Proof.
  induction w as [|t w IH]; intro d; [reflexivity|].
  destruct t.
  - destruct d; [reflexivity|]. cbn[dec]. rewrite(IH d).
    destruct(dec d w) as [u|]; cbn[obind option_map dec];
      [destruct(dec d u)|]; reflexivity.
  - destruct d.
    + cbn[dec]. destruct(dec O w); reflexivity.
    + cbn[dec]. rewrite(IH d).
      destruct(dec d w) as [u|]; cbn[obind option_map dec];
        [destruct(dec d u)|]; reflexivity.
  - cbn[dec]. rewrite(IH (S d)).
    destruct(dec (S d) w) as [u|]; cbn[obind option_map dec];
      [destruct(dec (S d) u)|]; reflexivity.
Qed.

Open Scope N_scope.
Fixpoint cap w : N := match w with
| []=>0 | Z::w=>2*cap w+1 | X::w=>2*cap w | W::w=>cap w/2 end.
Fixpoint pow2 (n:nat) : N := match n with O=>1 | S n=>2*pow2 n end.
Lemma pow2_pos n : 0<pow2 n.
Proof. induction n; cbn[pow2]; lia. Qed.
Ltac div2 :=
  repeat match goal with
  | |- context [?x / 2] =>
    let E:=fresh "Ediv" in let R:=fresh "Rdiv" in
    let q:=fresh "quo" in let r:=fresh "rem" in
    assert(E:x=2*(x/2)+x mod 2) by (apply N.div_mod; discriminate);
    assert(R:x mod 2<2) by (apply N.mod_lt; discriminate);
    set(q:=x/2) in *; set(r:=x mod 2) in *; clearbody q r
  | H:context [?x / 2] |- _ =>
    let E:=fresh "Ediv" in let R:=fresh "Rdiv" in
    let q:=fresh "quo" in let r:=fresh "rem" in
    assert(E:x=2*(x/2)+x mod 2) by (apply N.div_mod; discriminate);
    assert(R:x mod 2<2) by (apply N.mod_lt; discriminate);
    set(q:=x/2) in *; set(r:=x mod 2) in *; clearbody q r
  end; nia.
Lemma dec_capacity w : forall d,
  match dec d w with
  | None=>cap w<pow2 d
  | Some v=>cap w=cap v+pow2 d end.
Proof.
  induction w as [|t w IH]; intro d.
  - cbn[dec cap]; apply pow2_pos.
  - destruct t.
    + destruct d; [cbn[dec cap pow2]; lia|].
      specialize(IH d); cbn[dec cap pow2].
      destruct(dec d w) as [v|]; cbn[option_map cap] in *; lia.
    + destruct d.
      * specialize(IH O); cbn[dec cap pow2].
        destruct(dec O w) as [v|]; cbn[option_map cap pow2] in *; lia.
      * specialize(IH d); cbn[dec cap pow2].
        destruct(dec d w) as [v|]; cbn[option_map cap] in *; lia.
    + specialize(IH (S d)); cbn[dec cap pow2].
      destruct(dec (S d) w) as [v|]; cbn[option_map cap pow2] in *; div2.
Qed.
Lemma dec_exists w d : pow2 d<=cap w -> exists v, dec d w=Some v.
Proof.
  pose proof(dec_capacity w d) as H; destruct(dec d w) as [v|].
  - intro; eauto.
  - cbn in H; lia.
Qed.

Definition cdec w := match dec O w with Some v=>v | None=>w end.
Lemma cdec_spec w : 0<cap w -> dec O w=Some(cdec w).
Proof.
  intro H; destruct (dec_exists w O ltac:(cbn [pow2]; lia)) as [v HV].
  unfold cdec; now rewrite HV.
Qed.
Lemma cdec_capacity w : 0<cap w -> cap(cdec w)=cap w-1.
Proof.
  intro H; pose proof (dec_capacity w O) as E.
  rewrite (cdec_spec w H) in E; cbn [pow2] in E; lia.
Qed.
Lemma cdec_W w : 2<=cap w -> cdec(W::w)=W::cdec(cdec w).
Proof.
  intro H.
  assert (H1:0<cap w) by lia.
  assert (H2:0<cap(cdec w)) by (rewrite cdec_capacity by exact H1; lia).
  unfold cdec at 1; cbn [dec]; rewrite dec_double,(cdec_spec _ H1).
  cbn [obind]; rewrite (cdec_spec _ H2); reflexivity.
Qed.
Lemma cdec_Z w : cdec(Z::w)=X::w.
Proof. reflexivity. Qed.
Lemma cdec_X w : 0<cap w -> cdec(X::w)=Z::cdec w.
Proof. intro H; unfold cdec at 1; cbn [dec]; rewrite (cdec_spec _ H); reflexivity. Qed.
Lemma cdec_length w : length(cdec w)=length w.
Proof. unfold cdec; destruct (dec O w) eqn:E; [eapply dec_length; eauto|reflexivity]. Qed.

Fixpoint nbit w : nat := match w with
| []=>O | W::w=>nbit w | _::w=>S(nbit w) end.
Fixpoint nsh w : nat := match w with
| []=>O | W::w=>S(nsh w) | _::w=>nsh w end.
Fixpoint Adm w : Prop := match w with
| []=>True | _::v=>Adm v /\ (nsh w<=nbit w)%nat end.
Lemma dec_counts w : forall d v, dec d w=Some v ->
  nbit v=nbit w /\ nsh v=nsh w.
Proof.
  induction w as [|b w IH]; intros d v H; [discriminate|].
  destruct b,d; cbn [dec] in H;
    try (destruct (dec _ w) as [u|] eqn:E; [|discriminate]);
    inversion H; subst; cbn [nbit nsh];
    try (destruct (IH _ _ E); subst); auto.
Qed.
Lemma dec_adm w : forall d v, dec d w=Some v -> Adm w -> Adm v.
Proof.
  induction w as [|b w IH]; intros d v H HA; [discriminate|].
  destruct HA as [HA HB].
  destruct b,d; cbn [dec] in H;
    try (destruct (dec _ w) as [u|] eqn:E; [|discriminate]);
    inversion H; subst; cbn [Adm nbit nsh] in *;
    try (destruct (dec_counts _ _ _ E) as [Hbit Hsh]; rewrite Hbit,Hsh);
    split; eauto.
Qed.
Lemma cdec_adm w : Adm w -> Adm (cdec w).
Proof. intro H; unfold cdec; destruct (dec O w) eqn:E; eauto using dec_adm. Qed.
Lemma cdec_counts w : nbit(cdec w)=nbit w /\ nsh(cdec w)=nsh w.
Proof. unfold cdec; destruct (dec O w) eqn:E; eauto using dec_counts. Qed.

(* Admissibility prevents the counter from exceeding its unmatched bits. *)
Lemma capacity_bound w : Adm w -> cap w<pow2 (nbit w-nsh w).
Proof.
  induction w as [|b w IH]; [cbn; lia|].
  intros [HA HB]; specialize (IH HA).
  assert (HS:(nsh w<=nbit w)%nat).
  { destruct w; [reflexivity|exact (proj2 HA)]. }
  destruct b; cbn [cap nbit nsh] in HB |- *.
  - replace (S (nbit w)-nsh w)%nat with (S(nbit w-nsh w))%nat by lia.
    cbn [pow2]; lia.
  - replace (S (nbit w)-nsh w)%nat with (S(nbit w-nsh w))%nat by lia.
    cbn [pow2]; lia.
  - assert (HE:(nbit w-nsh w)%nat=S(nbit w-S(nsh w))%nat) by lia.
    rewrite HE in IH; cbn [pow2] in IH; div2.
Qed.

Lemma adm_bound w : Adm w -> (nsh w<=nbit w)%nat.
Proof. destruct w; [cbn; lia|exact (fun H=>proj2 H)]. Qed.
Lemma adm_Z w : Adm w -> Adm(Z::w).
Proof. intro H; split; [exact H|cbn [nbit nsh]; pose proof (adm_bound w H); lia]. Qed.
Lemma adm_X w : Adm w -> Adm(X::w).
Proof. intro H; split; [exact H|cbn [nbit nsh]; pose proof (adm_bound w H); lia]. Qed.
Lemma adm_W w : Adm w -> (nsh w<nbit w)%nat -> Adm(W::w).
Proof. intros H Hlt; split; [exact H|exact Hlt]. Qed.
Lemma capacity_two_bits w : Adm w -> 2<=cap w -> (2<=nbit w-nsh w)%nat.
Proof.
  intros HA HC; pose proof (capacity_bound w HA) as HB.
  destruct (nbit w-nsh w)%nat as [|[|n]]; cbn [pow2] in HB; lia.
Qed.

End BB25FamilyCore.

(* BB25FamilyStack.v *)
Close Scope Z_scope. Close Scope N_scope.
From BusyCoq Require Import Individual25.
Open Scope sym_scope.
From Coq Require Import List NArith ZArith Lia.
Import ListNotations BB25FamilyWord BB25FamilyCore.

Module BB25FamilyStack.
Open Scope N_scope.

Fixpoint pdec w : list digit := match w with
| []=>[] | Z::w | X::w=>pdec w++[Y]
| W::w=>pdec w++[if N.odd(cap w) then V else D] end.

Lemma dec_pdec w : forall d v, dec d w=Some v -> pdec v=pdec w.
Proof.
  induction w as [|b w IH]; intros d v E; [discriminate|].
  destruct b.
  - destruct d; cbn [dec] in E.
    + inversion E; reflexivity.
    + destruct (dec d w) as [u|] eqn:EU; [|discriminate].
      inversion E; subst; cbn [pdec]; now rewrite (IH d u EU).
  - destruct d; cbn [dec] in E;
      destruct (dec _ w) as [u|] eqn:EU; [|discriminate| |discriminate];
      inversion E; subst; cbn [pdec]; f_equal; eapply IH; exact EU.
  - cbn [dec] in E; destruct (dec (S d) w) as [u|] eqn:EU; [|discriminate].
    inversion E; subst; cbn [pdec]; rewrite (IH (S d) u EU).
    pose proof (dec_capacity w (S d)) as HC; rewrite EU in HC; cbn [pow2] in HC.
    rewrite HC,N.odd_add,N.odd_mul; cbn; rewrite Bool.xorb_false_r; reflexivity.
Qed.
Lemma cdec_pdec w : pdec(cdec w)=pdec w.
Proof. unfold cdec; destruct (dec O w) eqn:E; [eapply dec_pdec; exact E|reflexivity]. Qed.

Open Scope Z_scope.
Definition bval w := rrun (pdec w) 0.
Lemma bval_nil : bval []=0. Proof. reflexivity. Qed.
Lemma bval_Z w : bval (Z::w)=2*bval w+1.
Proof. unfold bval; cbn [pdec]; rewrite rrun_app; reflexivity. Qed.
Lemma bval_X w : bval (X::w)=2*bval w+1.
Proof. unfold bval; cbn [pdec]; rewrite rrun_app; reflexivity. Qed.
Lemma bval_W w : bval (W::w)=
  if N.odd(cap w) then 2*bval w else bval w/2-1.
Proof. unfold bval; cbn [pdec]; rewrite rrun_app; destruct (N.odd(cap w)); reflexivity. Qed.
Lemma dec_bval w d v : dec d w=Some v -> bval v=bval w.
Proof. intro H; unfold bval; now rewrite (dec_pdec w d v H). Qed.
Lemma cdec_bval w : bval(cdec w)=bval w.
Proof. unfold bval; now rewrite cdec_pdec. Qed.

(* Good is the bottom-prefix invariant, expressed recursively rather than
   quantified over suffix witnesses.  No whole-stack-only weakening. *)
Fixpoint Good w : Prop := match w with
| []=>True | _::v=>Good v /\ Z.of_N(cap w)<=bval w end.
Lemma good_bound w : Good w -> Z.of_N(cap w)<=bval w.
Proof. destruct w; [cbn; lia|exact (fun H=>proj2 H)]. Qed.
Lemma good_bval_nonneg w : Good w -> 0<=bval w.
Proof. intro H; pose proof (good_bound w H); lia. Qed.
Lemma good_Z w : Good w -> Good(Z::w).
Proof. intro H; split; [exact H|rewrite bval_Z; cbn [cap]; pose proof (good_bound w H); lia]. Qed.
Lemma good_X w : Good w -> Good(X::w).
Proof. intro H; split; [exact H|rewrite bval_X; cbn [cap]; pose proof (good_bound w H); lia]. Qed.

Lemma dec_good w : forall d v, dec d w=Some v -> Good w -> Good v.
Proof.
  induction w as [|b w IH]; intros d v E HG; [discriminate|].
  assert (HV:Z.of_N(cap v)<=bval v).
  { rewrite (dec_bval _ _ _ E).
    pose proof (dec_capacity (b::w) d) as HC; rewrite E in HC.
    pose proof (proj2 HG); lia. }
  destruct HG as [HG _].
  destruct b,d; cbn [dec] in E;
    try (destruct (dec _ w) as [u|] eqn:EU; [|discriminate]);
    inversion E; subst.
  all: split; [eauto|exact HV].
Qed.
Lemma cdec_good w : Good w -> Good(cdec w).
Proof. intro H; unfold cdec; destruct (dec O w) eqn:E; eauto using dec_good. Qed.

Lemma bal_pdec w : bal(pdec w)=Z.of_nat(nbit w)-Z.of_nat(nsh w).
Proof.
  induction w as [|b w IH]; [reflexivity|].
  destruct b; cbn [pdec nbit nsh]; rewrite bal_app,IH;
    try destruct (N.odd(cap w)); cbn [bal]; lia.
Qed.
Lemma pdec_dyck w : Adm w -> DyckPre(pdec w).
Proof.
  induction w as [|b w IH]; [intros _; apply dyck_nil|].
  intros [HA HB] p s HE; specialize (IH HA).
  assert (Hwhole:0<=bal(pdec(b::w))) by (rewrite bal_pdec; lia).
  destruct b; cbn [pdec] in HE;
    destruct (prefix_app_cases p _ _ (ex_intro _ s HE))
      as [[q HQ]|[q [-> HQ]]].
  all: try (exact (IH _ _ HQ)).
  all: destruct (prefix_singleton _ _ HQ) as [-> | ->];
    [rewrite app_nil_r; exact (dyck_nonneg _ IH)|exact Hwhole].
Qed.

End BB25FamilyStack.

(* BB25FamilyReset.v *)
Close Scope Z_scope. Close Scope N_scope.
From Coq Require Import List NArith ZArith Lia.
Import ListNotations BB25FamilyWord
  BB25FamilyCore BB25FamilyStack.
Open Scope Z_scope.

Module BB25FamilyReset.

Definition tstep (s : list tok) (b : digit) : list tok :=
  match b with Y=>Z::s | V=>X::s | D=>cdec(W::s) end.
Fixpoint tfold (s : list tok) (w : list digit) : list tok :=
  match w with []=>s | b::w=>tfold (tstep s b) w end.
Lemma tfold_app s w v : tfold s (w++v)=tfold (tfold s w) v.
Proof. revert s; induction w; intros; simpl; auto. Qed.

Lemma odd_of_N a : N.odd a=Z.eqb (Z.of_N a mod 2) 1.
Proof.
  rewrite <-N.bit0_odd,N.bit0_eqb.
  change ((a mod 2 =? 1)%N=(Z.of_N a mod Z.of_N 2 =? Z.of_N 1)%Z).
  rewrite <-N2Z.inj_mod.
  destruct (N.eqb_spec (a mod 2) 1); symmetry; [apply Z.eqb_eq|apply Z.eqb_neq]; lia.
Qed.
Lemma cap_cdec_twice s : (2<=cap s)%N -> cap(cdec(cdec s))=(cap s-2)%N.
Proof.
  intro H; assert (H1:(0<cap s)%N) by lia.
  assert (H2:(0<cap(cdec s))%N) by (rewrite cdec_capacity by exact H1; lia).
  rewrite (cdec_capacity _ H2),(cdec_capacity _ H1); lia.
Qed.
Lemma good_paid_W s : Good s -> (2<=cap s)%N -> Good(cdec(W::s)).
Proof.
  intros HG HC; rewrite cdec_W by exact HC; split.
  - now apply cdec_good,cdec_good.
  - rewrite bval_W,!cdec_bval; cbn [cap].
    rewrite cap_cdec_twice by exact HC.
    rewrite N2Z.inj_div.
    change (Z.of_N (cap s-2)/2 <= if N.odd (cap s-2) then 2*bval s else bval s/2-1).
    assert (EC : Z.of_N (cap s-2)=Z.of_N(cap s)-2) by lia.
    rewrite EC; pose proof (good_bound s HG) as HB.
    pose proof (div2_bounds (Z.of_N(cap s)-2)) as HD.
    pose proof (div2_bounds (bval s)) as HE.
    destruct (N.odd (cap s-2)); lia.
Qed.
Lemma pop_nonneg_capacity s : 0<=rstep D (Z.of_N(cap s)) -> (2<=cap s)%N.
Proof. unfold rstep; pose proof (div2_bounds (Z.of_N(cap s))); lia. Qed.
Lemma tstep_capacity s b : 0<=rstep b (Z.of_N(cap s)) ->
  Z.of_N(cap(tstep s b))=rstep b (Z.of_N(cap s)).
Proof.
  destruct b; cbn [tstep cap rstep]; intros H; try lia.
  assert (HC : (2<=cap s)%N) by (apply pop_nonneg_capacity; exact H).
  assert (HW : (0<cap(W::s))%N) by (cbn [cap]; apply N.div_str_pos; lia).
  rewrite cdec_capacity by exact HW; cbn [cap].
  rewrite N2Z.inj_sub by (change (1<=cap s/2)%N; lia).
  rewrite N2Z.inj_div; reflexivity.
Qed.
Lemma tstep_bval s b : 0<=rstep b (Z.of_N(cap s)) ->
  bval(tstep s b)=rstep (qout b (Z.of_N(cap s))) (bval s).
Proof.
  destruct b; intros H; cbn [tstep qout]; [apply bval_Z|apply bval_X|].
  rewrite cdec_bval,bval_W,odd_of_N.
  destruct (Z.eqb (Z.of_N(cap s) mod 2) 1); reflexivity.
Qed.
Lemma tstep_pdec s b : pdec(tstep s b)=pdec s++[qout b (Z.of_N(cap s))].
Proof.
  destruct b; cbn [tstep qout pdec]; auto.
  rewrite cdec_pdec; cbn [pdec]; now rewrite odd_of_N.
Qed.
Lemma tstep_props s b : Adm s -> Good s -> 0<=rstep b (Z.of_N(cap s)) ->
  Adm(tstep s b) /\ Good(tstep s b) /\
  Z.of_N(cap(tstep s b))=rstep b (Z.of_N(cap s)) /\
  bval(tstep s b)=rstep (qout b (Z.of_N(cap s))) (bval s) /\
  (1<=nbit(tstep s b)-nsh(tstep s b))%nat.
Proof.
  intros HA HG HC.
  assert (Hcap:=tstep_capacity s b HC).
  assert (Hval:=tstep_bval s b HC).
  destruct b.
  - split; [now apply adm_Z|split; [now apply good_Z|]].
    split; [exact Hcap|split; [exact Hval|]].
    cbn [tstep nbit nsh]; pose proof (adm_bound s HA); lia.
  - split; [now apply adm_X|split; [now apply good_X|]].
    split; [exact Hcap|split; [exact Hval|]].
    cbn [tstep nbit nsh]; pose proof (adm_bound s HA); lia.
  - assert (H2 : (2<=cap s)%N) by (apply pop_nonneg_capacity; exact HC).
    pose proof (capacity_two_bits s HA H2) as HB.
    assert (HW : Adm(W::s)) by (apply adm_W; auto; lia).
    split; [apply cdec_adm; exact HW|].
    split; [apply good_paid_W; auto|].
    split; [exact Hcap|split; [exact Hval|]].
    cbn [tstep]; destruct (cdec_counts (W::s)) as [E1 E2]; rewrite E1,E2; cbn [nbit nsh]; lia.
Qed.

Theorem tfold_props w s : Adm s -> Good s -> 0<=rrun w (Z.of_N(cap s)) ->
  Adm(tfold s w) /\ Good(tfold s w) /\
  Z.of_N(cap(tfold s w))=rrun w (Z.of_N(cap s)) /\
  bval(tfold s w)=trun w (Z.of_N(cap s)) (bval s) /\
  (w<>[] -> (1<=nbit(tfold s w)-nsh(tfold s w))%nat).
Proof.
  revert s; induction w as [|b w IH]; intros s HA HG HC.
  - cbn [tfold rrun trun]; repeat split; auto; intros H; contradiction.
  - pose proof (rrun_nonneg_head b w (Z.of_N(cap s)) HC) as Hstep.
    destruct (tstep_props s b HA HG Hstep) as [HA1 [HG1 [Hcap [Hval Hbits]]]].
    assert (Hrest : 0<=rrun w (Z.of_N(cap(tstep s b)))) by (rewrite Hcap; exact HC).
    destruct (IH (tstep s b) HA1 HG1 Hrest) as [HA2 [HG2 [Hcap2 [Hval2 Hbits2]]]].
    cbn [tfold]; split; [exact HA2|split; [exact HG2|]].
    split; [rewrite Hcap2,Hcap; reflexivity|].
    split; [rewrite Hval2,Hcap,Hval; reflexivity|].
    intros _; destruct w; [exact Hbits|apply Hbits2; discriminate].
Qed.

Fixpoint qword (w : list digit) (a : BinNums.Z) : list digit :=
  match w with []=>[] | b::w=>qout b a::qword w (rstep b a) end.
Lemma qword_rrun w a c : rrun(qword w a) c=trun w a c.
Proof. revert a c; induction w; intros; cbn [qword rrun trun]; auto. Qed.
Lemma qword_length w a : length(qword w a)=length w.
Proof. revert a; induction w; intros; cbn [qword length]; auto. Qed.
Theorem tfold_pdec w s : 0<=rrun w (Z.of_N(cap s)) ->
  pdec(tfold s w)=pdec s++qword w (Z.of_N(cap s)).
Proof.
  revert s; induction w as [|b w IH]; intros s HC.
  - cbn [tfold qword]; now rewrite app_nil_r.
  - pose proof (rrun_nonneg_head b w (Z.of_N(cap s)) HC) as Hstep.
    pose proof (tstep_capacity s b Hstep) as Hcap.
    cbn [tfold]; rewrite IH by (rewrite Hcap; exact HC).
    rewrite tstep_pdec,Hcap; cbn [qword]; rewrite <-app_assoc; reflexivity.
Qed.

Corollary tfold_empty_props w : 0<=rrun w 0 ->
  Adm(tfold [] w) /\ Good(tfold [] w) /\
  Z.of_N(cap(tfold [] w))=rrun w 0 /\ bval(tfold [] w)=trun w 0 0 /\
  (w<>[] -> (1<=nbit(tfold [] w)-nsh(tfold [] w))%nat).
Proof. intro H; exact (tfold_props w [] I I H). Qed.

Example reset_small : tfold [] [Y;Y;D]=[W;Z;X].
Proof. reflexivity. Qed.
Example reset_small_capacity : cap(tfold [] [Y;Y;D])=0%N.
Proof. reflexivity. Qed.
Example reset_small_output : pdec(tfold [] [Y;Y;D])=[Y;Y;V].
Proof. reflexivity. Qed.

End BB25FamilyReset.

(* BB25FamilyRules.v *)
Close Scope Z_scope. Close Scope N_scope.
From BusyCoq Require Import Individual25.
Open Scope sym_scope.
From Coq Require Import List Lia PeanoNat.
Import ListNotations.

(** Shared original-state transition table. Normal counting uses neither
    B3 nor B4; the regular family fixes B3 to 4LB, its sibling uses 4RB.
    No block configuration datatype or private execution relation is used. *)
Module BB25FamilyRules.

Record control := Control {
  b3_rule : option (Sym*dir*Q);
  b4_rule : option (Sym*dir*Q)
}.
Definition regular (b4:option (Sym*dir*Q)) := Control (Some(S4,L,B)) b4.
Coercion regular : option >-> control.

Definition family (b4:control) : TM := fun qs =>
  match qs with
  | (A,S0) => Some (S1,R,B)
  | (A,S1) => Some (S2,L,A)
  | (A,S2) => Some (S0,R,B)
  | (A,S3) => Some (S1,L,B)
  | (A,S4) => None
  | (B,S0) => Some (S1,L,A)
  | (B,S1) => Some (S3,R,A)
  | (B,S2) => Some (S1,R,A)
  | (B,S3) => b3_rule b4
  | (B,S4) => b4_rule b4
  end.

Section Shared.
Variable b4 : control.
Notation tm := (family b4).
Notation "c -->* c'" := (c -[tm]->* c') (at level 40).
Notation "c -->+ c'" := (c -[tm]->+ c') (at level 40).

(** Rightward entries. The one-cell rule includes X, U, F, and a pending 1. *)
Lemma right_one l r : l {{A}}> 1 >> r -->+ l <{{A}} 2 >> r.
Proof. execute. Qed.
Lemma right_V l r : l {{A}}> [2;1] *> r -->+ l <* [3;0] {{A}}> r.
Proof. execute. Qed.
Lemma right_Y l r : l {{A}}> [2;2] *> r -->+ l <* [1;0] {{A}}> r.
Proof. execute. Qed.
Lemma right_N2 l r : l {{A}}> [2;0;1] *> r -->+ l <{{B}} [1;2;2] *> r.
Proof. execute. Qed.
Lemma right_blank l : l {{A}}> 0inf -->+ l <{{A}} [2;1] *> 0inf.
Proof. execute. Qed.
Lemma right_two_blank l : l {{A}}> 2 >> 0inf -->+ l <{{B}} [1;2;2;1] *> 0inf.
Proof. execute. Qed.

(** Stack tokens are nearest-head first: X=11, Z=10, W=30. *)
Lemma left_X l r : l <* [1;1] <{{A}} r -->+ l <{{A}} [2;2] *> r.
Proof. execute. Qed.
Lemma left_Z l r : l <* [1;0] <{{A}} r -->+ l <* [1;1] {{A}}> r.
Proof. execute. Qed.
Lemma left_W l r : l <* [3;0] <{{A}} r -->+ l <{{A}} [1;1] *> r.
Proof. execute. Qed.
Lemma leftend_A r :
  0inf <* [1;1] <{{A}} r -->+ 0inf <* [1;1] {{A}}> 2 >> r.
Proof. execute. Qed.

(** The extra 1 belongs to the directed marker <B1, not the stack token. *)
Lemma B1_X l r : l <* [1;1] <{{B}} 1 >> r -->+ l <{{B}} [1;2;2] *> r.
Proof. execute. Qed.
Lemma B1_Z l r : l <* [1;0] <{{B}} 1 >> r -->+ l <{{A}} [1;1;2] *> r.
Proof. execute. Qed.
Lemma B1_X_sweep n l r :
  l <* [1;1]^^n <{{B}} 1 >> r -->* l <{{B}} 1 >> [2;2]^^n *> r.
Proof.
  apply (shift_rule_L [1]); intros.
  apply progress_evstep; apply B1_X.
Qed.

(** Marker words introduced by the variable G case, still with arbitrary tails. *)
Lemma left_J2 l r : l <* [3;2;0] <{{A}} r -->+ l <* [1;1] {{A}}> 2 >> r.
Proof. execute. Qed.
Lemma left_J1 l r : l <* [3;1;0] <{{A}} r -->+ l <{{A}} [1;1;2] *> r.
Proof. execute. Qed.
Lemma left_J0 l r : l <* [3;0;0] <{{A}} r -->+ l <{{B}} [1;2;2] *> r.
Proof. execute. Qed.
Lemma left_K0 l r : l <* [1;0;0] <{{A}} r -->+ l <* [1;1;0] {{A}}> r.
Proof. execute. Qed.
Lemma left_K1 l r : l <* [1;1;0] <{{A}} r -->+ l <* [1;1] {{A}}> 2 >> r.
Proof. execute. Qed.

(** Both spinouts leave their arbitrary right tail unread. *)
Lemma spinout_step r :
  0inf <{{A}} [1;1;2;2] *> r -->+ 0inf <{{A}} [1;1;2;2;2;2] *> r.
Proof. execute. Qed.
Lemma xy_spinout_step r :
  0inf <* [1;1] <{{A}} [1;1;2;2] *> r -->+
  0inf <* [1;1] <{{A}} [1;1;2;2;2] *> r.
Proof. execute. Qed.
Lemma leftend_B1_run r :
  0inf <* [1;1] <{{B}} 1 >> r -->+ 0inf <{{A}} [1;1;2;2] *> r.
Proof. execute. Qed.

Lemma spinout_nonhalt r : ~halts tm (0inf <{{A}} [1;1;2;2] *> r).
Proof.
  apply (progress_nonhalt_simple tm side
    (fun t => 0inf <{{A}} [1;1;2;2] *> t) r).
  intro t; exists (2 >> 2 >> t); apply spinout_step.
Qed.
Lemma leftend_B1_nonhalt r : ~halts tm (0inf <* [1;1] <{{B}} 1 >> r).
Proof.
  eapply multistep_nonhalt.
  - apply progress_evstep; apply leftend_B1_run.
  - apply spinout_nonhalt.
Qed.
Lemma xy_spinout_nonhalt r : ~halts tm (0inf <* [1;1] <{{A}} [1;1;2;2] *> r).
Proof.
  apply (progress_nonhalt_simple tm side
    (fun t => 0inf <* [1;1] <{{A}} [1;1;2;2] *> t) r).
  intro t; exists (2 >> t); apply xy_spinout_step.
Qed.
End Shared.

Lemma B1_W (b4:option(Sym*dir*Q)) l r :
  l <* [3;0] <{{B}} 1 >> r -[family b4]->+ l <{{A}} [1;4;1] *> r.
Proof. execute. Qed.

(** G=241. The first two schemas each cover 0/1/2 written in state B;
    the remaining seven statements cover all listed state-A variants.
    They are direct machine rules, not a second block-step evaluator. *)
Lemma G_B_left s l r :
  l {{A}}> [2;4;1] *> r -[family (Some (s,L,B))]->+
  l <{{A}} [1;s;1] *> r.
Proof. execute. Qed.
Lemma G_B_right s l r :
  l {{A}}> [2;4;1] *> r -[family (Some (s,R,B))]->+
  l <* [3;s;0] {{A}}> r.
Proof. execute. Qed.
Lemma G_3RA l r :
  l {{A}}> [2;4;1] *> r -[family (Some (3,R,A))]->+ l <{{A}} [1;1;2] *> r.
Proof. execute. Qed.
Lemma G_2LA l r :
  l {{A}}> [2;4;1] *> r -[family (Some (2,L,A))]->+ l <{{A}} [2;2;2] *> r.
Proof. execute. Qed.
Lemma G_2RA l r :
  l {{A}}> [2;4;1] *> r -[family (Some (2,R,A))]->+ l <* [1;0;0] {{A}}> r.
Proof. execute. Qed.
Lemma G_1LA l r :
  l {{A}}> [2;4;1] *> r -[family (Some (1,L,A))]->+ l <{{B}} [1;2;2] *> r.
Proof. execute. Qed.
Lemma G_1RA l r :
  l {{A}}> [2;4;1] *> r -[family (Some (1,R,A))]->+ l <* [1;1] {{A}}> 2 >> r.
Proof. execute. Qed.
Lemma G_0LA l r :
  l {{A}}> [2;4;1] *> r -[family (Some (0,L,A))]->+ l <{{A}} [2;1;1] *> r.
Proof. execute. Qed.
Lemma G_0RA l r :
  l {{A}}> [2;4;1] *> r -[family (Some (0,R,A))]->+ l <* [1;1;0] {{A}}> r.
Proof. execute. Qed.

End BB25FamilyRules.

(* BB25FamilyMachine.v *)
Close Scope Z_scope. Close Scope N_scope.
From BusyCoq Require Import Individual25.
Open Scope sym_scope.
From Coq Require Import List NArith Lia Arith.Wf_nat.
Import ListNotations BB25FamilyRules BB25FamilyCore.

(** The pure counter algebra connected to actual machine configurations.
    The left environment remains arbitrary until overflow_root_run. *)
Module BB25FamilyMachine.

Definition tc (t:tok) : list Sym :=
  match t with Z => [S1;S0] | X => [S1;S1] | W => [S3;S0] end.
Definition left (w:list tok) (l:side) := flat_map tc w *> l.
Fixpoint out (w:list tok) : list Sym :=
  match w with
  | [] => []
  | Z::w | X::w => out w ++ [S2;S2]
  | W::w => out w ++ (if N.odd (cap w) then [S2;S1] else [S1;S1])
  end.

Lemma left_cons t w l : left (t::w) l = tc t *> left w l.
Proof. unfold left; cbn [flat_map]; rewrite Str_app_assoc; reflexivity. Qed.

Open Scope N_scope.

Lemma out_dec w : forall d v, dec d w = Some v -> out v = out w.
Proof.
  induction w as [|t w IH]; intros d v E; [discriminate|].
  destruct t.
  - destruct d; cbn [dec] in E.
    + inversion E; reflexivity.
    + destruct (dec d w) as [u|] eqn:EU; [|discriminate].
      inversion E; subst; cbn [out]; rewrite (IH d u EU); reflexivity.
  - destruct d; cbn [dec] in E;
      destruct (dec _ w) as [u|] eqn:EU; [|discriminate| |discriminate];
      inversion E; subst; cbn [out]; f_equal; eapply IH; exact EU.
  - cbn [dec] in E; destruct (dec (S d) w) as [u|] eqn:EU; [|discriminate].
    inversion E; subst; cbn [out]; rewrite (IH (S d) u EU).
    pose proof (dec_capacity w (S d)) as HC; rewrite EU in HC; cbn [pow2] in HC.
    rewrite HC, N.odd_add, N.odd_mul; cbn; rewrite Bool.xorb_false_r; reflexivity.
Qed.

Section Runs.
Variable b4 : control.
Notation tm := (family b4).
Notation "c -->* c'" := (c -[tm]->* c') (at level 40).
Notation "c -->+ c'" := (c -[tm]->+ c') (at level 40).

(** W removes two units of capacity from its shorter tail. The second
    recursive call is on a different word of the same shorter length. *)
Lemma dec_run w : forall v, dec O w = Some v -> forall l r,
  left w l <{{A}} r -->+ left v l {{A}}> r.
Proof.
  induction w as [w IH] using
    (well_founded_induction (well_founded_ltof _ (@List.length tok))).
  destruct w as [|t w]; [intros; discriminate|].
  intros v E l r; destruct t.
  - cbn [dec] in E; inversion E; subst.
    rewrite !left_cons; cbn [tc]; apply left_Z.
  - cbn [dec] in E; destruct (dec O w) as [u|] eqn:EU; [|discriminate].
    inversion E; subst; rewrite !left_cons; cbn [tc].
    eapply progress_trans; [apply left_X|].
    eapply progress_trans; [|apply right_Y].
    apply IH; [unfold ltof; cbn; lia|exact EU].
  - cbn [dec] in E; rewrite (dec_double w O) in E.
    destruct (dec O w) as [u|] eqn:EU; cbn [obind] in E; [|discriminate].
    destruct (dec O u) as [v'|] eqn:EV; [|discriminate].
    inversion E; subst; pose proof (dec_length w O u EU) as HL.
    rewrite !left_cons; cbn [tc].
    eapply progress_trans; [apply left_W|].
    eapply progress_trans; [apply IH; [unfold ltof; cbn; lia|exact EU]|].
    eapply progress_trans; [apply right_one|].
    eapply progress_trans; [|apply right_V].
    apply IH; [unfold ltof; cbn; lia|exact EV].
Qed.

(** Zero capacity spills exactly out w, without touching the arbitrary
    bottom l. This is deliberately reflexive for the empty stack. *)
Lemma overflow_run w : cap w = 0 -> forall l r,
  left w l <{{A}} r -->* l <{{A}} out w *> r.
Proof.
  induction w as [w IH] using
    (well_founded_induction (well_founded_ltof _ (@List.length tok))).
  destruct w as [|t w].
  - intros _ l r; apply evstep_refl.
  - intro HC; destruct t; intros l r.
    + cbn [cap] in HC; lia.
    + assert (HW:cap w=0) by (cbn [cap] in HC; lia).
      rewrite left_cons; cbn [tc out]; rewrite Str_app_assoc.
      eapply evstep_trans; [apply progress_evstep; apply left_X|].
      apply IH; [unfold ltof; cbn; lia|exact HW].
    + assert (HW:cap w=0 \/ cap w=1) by (cbn [cap] in HC; div2).
      destruct HW as [HW|HW].
      * rewrite left_cons; cbn [tc out]; rewrite HW; cbn [N.odd].
        rewrite Str_app_assoc.
        eapply evstep_trans; [apply progress_evstep; apply left_W|].
        apply IH; [unfold ltof; cbn; lia|exact HW].
      * destruct (dec_exists w O ltac:(cbn [pow2]; lia)) as [u EU].
        pose proof (dec_capacity w O) as HU; rewrite EU in HU; cbn [pow2] in HU.
        pose proof (dec_length w O u EU) as HL.
        rewrite left_cons; cbn [tc out]; rewrite HW; cbn [N.odd].
        rewrite Str_app_assoc, <- (out_dec w O u EU).
        eapply evstep_trans; [apply progress_evstep; apply left_W|].
        eapply evstep_trans; [apply progress_evstep; apply dec_run; exact EU|].
        eapply evstep_trans; [apply progress_evstep; apply right_one|].
        apply IH; [unfold ltof; cbn; lia|lia].
Qed.

Definition root : side := 0inf <* [S1;S1].

Lemma overflow_root_run w : cap w = 0 -> forall r,
  left w root <{{A}} r -->+ root {{A}}> S2 >> out w *> r.
Proof.
  intros HC r.
  eapply evstep_progress_trans; [apply overflow_run; exact HC|].
  unfold root; apply leftend_A.
Qed.
End Runs.

End BB25FamilyMachine.

(* BB25FamilyDrain.v *)
Close Scope Z_scope. Close Scope N_scope.
From Coq Require Import List NArith ZArith Lia.
Import ListNotations BB25FamilyWord
  BB25FamilyCore BB25FamilyStack
  BB25FamilyReset.
Open Scope Z_scope.

Module BB25FamilyDrain.

Definition Strong (s:list tok) : Prop :=
  Adm s /\ 3*(Z.of_N(cap s)+1)<=bval s+2.
Definition pushZ (n:nat) (s:list tok) := Nat.iter n (cons Z) s.
Lemma pushZ_zero s : pushZ O s=s. Proof. reflexivity. Qed.
Lemma pushZ_succ n s : pushZ (S n) s=Z::pushZ n s. Proof. reflexivity. Qed.
Lemma pushZ_repeat n s : pushZ n s=repeat Z n++s.
Proof. induction n; cbn [repeat app]; [reflexivity|rewrite pushZ_succ,IHn; reflexivity]. Qed.
Lemma pushZ_adm n s : Adm s -> Adm(pushZ n s).
Proof. intro H; induction n; [exact H|rewrite pushZ_succ; now apply adm_Z]. Qed.
Lemma pushZ_good n s : Good s -> Good(pushZ n s).
Proof. intro H; induction n; [exact H|rewrite pushZ_succ; now apply good_Z]. Qed.
Lemma pushZ_counts n s : nbit(pushZ n s)=(nbit s+n)%nat /\ nsh(pushZ n s)=nsh s.
Proof.
  induction n; [rewrite pushZ_zero,Nat.add_0_r; split; reflexivity|].
  rewrite pushZ_succ; cbn [nbit nsh]; destruct IHn; lia.
Qed.
Lemma pushZ_capacity n s : (cap(pushZ n s)+1=
  BB25FamilyCore.pow2 n*(cap s+1))%N.
Proof.
  induction n; [change (cap s+1=1*(cap s+1))%N; lia|].
  rewrite pushZ_succ; cbn [cap BB25FamilyCore.pow2]; nia.
Qed.
Lemma pushZ_cap_exact n s : cap(pushZ n s)=
  (BB25FamilyCore.pow2 n*(cap s+1)-1)%N.
Proof. pose proof (pushZ_capacity n s); lia. Qed.
Lemma pow2_of_N n : Z.of_N(BB25FamilyCore.pow2 n)=
  BB25FamilyWord.pow2 n.
Proof.
  induction n; [reflexivity|].
  change (Z.of_N(2*BB25FamilyCore.pow2 n)%N=
    BB25FamilyWord.pow2 (S n)).
  rewrite N2Z.inj_mul,IHn; reflexivity.
Qed.
Lemma pushZ_zcapacity n s : Z.of_N(cap(pushZ n s))+1=
  BB25FamilyWord.pow2 n*(Z.of_N(cap s)+1).
Proof.
  pose proof (f_equal Z.of_N (pushZ_capacity n s)) as E.
  rewrite N2Z.inj_add,N2Z.inj_mul,N2Z.inj_add,pow2_of_N in E; exact E.
Qed.
Lemma pushZ_bval n s : bval(pushZ n s)=
  BB25FamilyWord.pow2 n*(bval s+1)-1.
Proof.
  induction n; [change (bval s=1*(bval s+1)-1); ring|].
  rewrite pushZ_succ,bval_Z,IHn,BB25FamilyWord.pow2_succ; ring.
Qed.
Lemma pushZ_pdec n s : pdec(pushZ n s)=pdec s++repeat Y n.
Proof.
  induction n; [rewrite pushZ_zero; now rewrite app_nil_r|].
  rewrite pushZ_succ; cbn [pdec]; rewrite IHn,<-app_assoc.
  rewrite <-repeat_cons; reflexivity.
Qed.
Lemma capacity_one_bit s : Adm s -> (0<cap s)%N -> (1<=nbit s-nsh s)%nat.
Proof.
  intros HA HC; pose proof (capacity_bound s HA) as HB.
  destruct (nbit s-nsh s)%nat; [cbn [BB25FamilyCore.pow2] in HB; lia|lia].
Qed.
Lemma odd_capacity_positive s : N.odd(cap s)=true -> (0<cap s)%N.
Proof. destruct (cap s); cbn; intros H; [discriminate|lia]. Qed.

Theorem strong_round s : Strong s -> (0<cap s)%N ->
  Strong(W::cdec s) /\ (cap(W::cdec s)<cap s)%N.
Proof.
  intros [HA HB] HC; pose proof (capacity_one_bit s HA HC) as Hbits.
  pose proof (cdec_counts s) as [Ebit Esh].
  split.
  - split.
    + apply adm_W; [now apply cdec_adm|rewrite Ebit,Esh; lia].
    + rewrite bval_W,cdec_bval; cbn [cap]; rewrite cdec_capacity by exact HC.
      rewrite N2Z.inj_div.
      assert (EC : Z.of_N(cap s-1)=Z.of_N(cap s)-1) by lia.
      rewrite EC; change (3*((Z.of_N(cap s)-1)/2+1)<=
        (if N.odd(cap s-1) then 2*bval s else bval s/2-1)+2).
      pose proof (div2_bounds (Z.of_N(cap s)-1)) as HD.
      pose proof (div2_bounds (bval s)) as HE.
      destruct (N.odd(cap s-1)); lia.
  - cbn [cap]; rewrite cdec_capacity by exact HC.
    pose proof (N.div_mod (cap s-1) 2 ltac:(discriminate)).
    pose proof (N.mod_lt (cap s-1) 2 ltac:(discriminate)); lia.
Qed.
Corollary strong_step s : Strong s -> (0<cap s)%N -> Strong(W::cdec s).
Proof. intros HS HC; exact (proj1 (strong_round s HS HC)). Qed.
Corollary strong_decrease s : Strong s -> (0<cap s)%N -> (cap(W::cdec s)<cap s)%N.
Proof. intros HS HC; exact (proj2 (strong_round s HS HC)). Qed.
Theorem strong_zero s : Strong s -> cap s=0%N -> 1<=bval s.
Proof. intros [_ H] HC; rewrite HC in H; cbn in H; lia. Qed.

Lemma tail_bound_of_good s : Good s ->
  3*(Z.of_N(cap s)+1)<=4*(bval s+1).
Proof. intro H; pose proof (good_bound s H); lia. Qed.
Lemma pushZ_odd n s : (1<=n)%nat \/ N.odd(cap s)=true ->
  N.odd(cap(pushZ n s))=true.
Proof.
  intros H; destruct n; [destruct H; [lia|exact H]|].
  rewrite pushZ_succ; cbn [cap]; rewrite N.odd_add,N.odd_mul; reflexivity.
Qed.
Theorem strong_pending n s : Adm s ->
  3*(Z.of_N(cap s)+1)<=4*(bval s+1) ->
  ((1<=n)%nat \/ N.odd(cap s)=true) -> Strong(W::pushZ n s).
Proof.
  intros HA HB HG; pose proof (pushZ_adm n s HA) as HAp.
  pose proof (pushZ_odd n s HG) as HO.
  pose proof (odd_capacity_positive (pushZ n s) HO) as HC.
  split.
  - apply adm_W; [exact HAp|pose proof (capacity_one_bit _ HAp HC); lia].
  - rewrite bval_W,HO; cbn [cap]; rewrite N2Z.inj_div.
    change (3*(Z.of_N(cap(pushZ n s))/2+1)<=2*bval(pushZ n s)+2).
    pose proof (pushZ_zcapacity n s) as EA; pose proof (pushZ_bval n s) as EB.
    rewrite odd_of_N in HO; apply Z.eqb_eq in HO.
    pose proof (Z.div_mod (Z.of_N(cap(pushZ n s))) 2 ltac:(lia)) as ED.
    pose proof (BB25FamilyWord.pow2_pos n) as HP.
    pose proof (Z.mul_le_mono_nonneg_l _ _
      (BB25FamilyWord.pow2 n) ltac:(lia) HB) as HM.
    nia.
Qed.

Example drain_low_round : W::cdec [X;Z]=[W;Z;X]. Proof. reflexivity. Qed.
Example pending_from_bottom : Strong(W::pushZ 1 []).
Proof. apply strong_pending; [exact I|cbn; lia|left; lia]. Qed.
Example pending_zero_odd : Strong(W::pushZ 0 [Z]).
Proof. apply strong_pending; [apply adm_Z; exact I|apply tail_bound_of_good; apply good_Z; exact I|right; reflexivity]. Qed.

End BB25FamilyDrain.

(* BB25FamilyBounds.v *)
Close Scope Z_scope. Close Scope N_scope.
From Coq Require Import List NArith ZArith Lia.
Import ListNotations BB25FamilyWord
  BB25FamilyCore BB25FamilyStack
  BB25FamilyReset BB25FamilyDrain.
Open Scope Z_scope.

Module BB25FamilyBounds.

Theorem pushZ_checkpoint n s : Adm s -> Good s -> (1<=n)%nat ->
  ((2<=n)%nat \/ (0<cap s)%N) ->
  Adm(cdec(pushZ n s)) /\ Good(cdec(pushZ n s)) /\
  (0<cap(cdec(pushZ n s)))%N /\ exists t,cdec(pushZ n s)=X::t.
Proof.
  intros HA HG Hn HP; destruct n as [|n]; [lia|].
  split; [apply cdec_adm,pushZ_adm; exact HA|].
  split; [apply cdec_good,pushZ_good; exact HG|].
  rewrite pushZ_succ,cdec_Z; split.
  - cbn [cap]; destruct n as [|n].
    + destruct HP; [lia|change (0<2*cap s)%N; lia].
    + rewrite pushZ_succ; cbn [cap]; lia.
  - eexists; reflexivity.
Qed.

Lemma good_W s : Good s -> Z.of_N(cap s)+2<=bval s -> Good(W::s).
Proof.
  intros HG HB; split; [exact HG|].
  rewrite bval_W; cbn [cap]; rewrite N2Z.inj_div.
  pose proof (div2_bounds (Z.of_N(cap s))) as HC.
  pose proof (div2_bounds (bval s)) as HD.
  destruct (N.odd(cap s)); cbn [Z.of_N]; lia.
Qed.
Lemma good_W_odd s : Good s -> N.odd(cap s)=true -> Good(W::s).
Proof.
  intros HG HO; split; [exact HG|].
  rewrite bval_W,HO; cbn [cap]; rewrite N2Z.inj_div.
  pose proof (good_bound s HG) as HB.
  pose proof (div2_bounds (Z.of_N(cap s))) as HC; cbn [Z.of_N]; lia.
Qed.

Theorem overflow_retry s : Adm s -> cap s=0%N ->
  0<=bval s<=1 -> pdec s<>[] ->
  let t:=tfold [] (pdec s) in let u:=W::t in
  Adm u /\ Good u /\ cap u=0%N /\ 0<=bval u.
Proof.
  intros HA HC HB Hne; cbn zeta.
  pose proof (pdec_dyck s HA) as HD.
  assert (HR : 0<=rrun (pdec s) 0) by exact (proj1 HB).
  destruct (tfold_empty_props (pdec s) HR)
    as [HAt [HGt [EC [EB Hbits]]]].
  change (Z.of_N(cap(tfold [] (pdec s)))=bval s) in EC.
  assert (HAu : Adm(W::tfold [] (pdec s))).
  { apply adm_W; [exact HAt|specialize (Hbits Hne); lia]. }
  assert (HGu : Good(W::tfold [] (pdec s))).
  { destruct (Z.eq_dec (bval s) 0) as [H0|H1].
    - apply good_W; [exact HGt|].
      rewrite EC,H0,EB.
      exact (trun_ge_two (pdec s) HD Hne H0).
    - apply good_W_odd; [exact HGt|].
      assert (E1 : cap(tfold [] (pdec s))=1%N) by lia.
      now rewrite E1. }
  split; [exact HAu|split; [exact HGu|split]].
  - cbn [cap]; apply N.div_small; lia.
  - exact (good_bval_nonneg _ HGu).
Qed.

Example checkpoint_small : cdec(pushZ 2 [])=[X;Z]. Proof. reflexivity. Qed.
Example retry_zero_small :
  let s:=[W;X;X] in
  Adm(W::tfold [] (pdec s)) /\ Good(W::tfold [] (pdec s)) /\
  cap(W::tfold [] (pdec s))=0%N /\ 0<=bval(W::tfold [] (pdec s)).
Proof.
  apply overflow_retry.
  - cbn [Adm nbit nsh]; repeat split; lia.
  - reflexivity.
  - change (0<=0<=1); lia.
  - discriminate.
Qed.

End BB25FamilyBounds.

(* BB25FamilySeed.v *)
Close Scope Z_scope. Close Scope N_scope.
From BusyCoq Require Import Individual25.
Open Scope sym_scope.
From Coq Require Import List NArith Lia.
Import ListNotations BB25FamilyRules BB25FamilyCore
  BB25FamilyStack BB25FamilyMachine.

Module BB25FamilySeed.

(** The implicit bottom is [root]; tokens are nearest-head first. *)
Definition seed : list tok := [X;X;X;Z;Z;Z].

(** This finite prefix never reads B4, so the transition there is arbitrary. *)
Lemma seed_run_156 b4 : c0 -[family b4]->> 156 /
  (left seed root <{{B}} [S1;S2;S2;S1] *> 0inf).
Proof. apply multistep_c_spec; reflexivity. Qed.

Lemma seed_run b4 : c0 -[family b4]->*
  (left seed root <{{B}} [S1;S2;S2;S1] *> 0inf).
Proof. apply multistep_evstep_iff; exists 156%nat; apply seed_run_156. Qed.

Lemma cap_seed : cap seed=56%N.
Proof. reflexivity. Qed.

Lemma seed_safe : Adm seed /\ Good seed /\ (0<cap seed)%N /\
  exists t, seed=X::t.
Proof.
  split; [unfold seed; repeat first [apply adm_X|apply adm_Z]; exact I|].
  split.
  - unfold seed. apply good_X, good_X, good_X.
    apply BB25FamilyStack.good_Z.
    apply BB25FamilyStack.good_Z.
    apply BB25FamilyStack.good_Z; exact I.
  - split; [rewrite cap_seed; reflexivity|eexists; reflexivity].
Qed.

(** A generic progress closure allowing terminal branches already known
    non-halting. The hypothetical halting execution rules those branches
    out; BusyCoq's ordinary strict-progress criterion handles the rest. *)
Lemma progress_nonhalt_or (tm:TM) (P:Q*tape->Prop) :
  (forall c, P c ->
    (exists c', c -[tm]->+ c' /\ P c') \/ ~halts tm c) ->
  forall c, P c -> ~halts tm c.
Proof.
  intros Hstep c HP HH.
  eapply (progress_nonhalt tm (fun d=>P d /\ halts tm d) c).
  - intros d [HPd HHd]. destruct (Hstep d HPd) as [[d' [Hrun HP']]|HN].
    + exists d'; split; [split; [exact HP'|]|exact Hrun].
      apply (proj1 (halts_evstep_iff tm d d' (progress_evstep _ _ _ Hrun))).
      exact HHd.
    + contradiction.
  - split; assumption.
  - exact HH.
Qed.

End BB25FamilySeed.

(* BB25FamilyReturn.v *)
Close Scope Z_scope. Close Scope N_scope.
From BusyCoq Require Import Individual25.
Open Scope sym_scope.
From Coq Require Import List NArith ZArith Lia.
Import ListNotations BB25FamilyRules
  BB25FamilyCore BB25FamilyWord
  BB25FamilyStack BB25FamilyReset
  BB25FamilyMachine BB25FamilyDrain
  BB25FamilyBounds.

Module BB25FamilyReturn.

Definition dc b : list Sym := match b with
  Y=>[S2;S2] | V=>[S2;S1] | D=>[S1;S1] end.
Definition cells w := flat_map dc w.
Lemma cells_app w v : cells(w++v)=cells w++cells v.
Proof. apply flat_map_app. Qed.
Lemma cells_snoc w b r : cells(w++[b]) *> r=cells w *> dc b *> r.
Proof. rewrite cells_app,Str_app_assoc; cbn [cells flat_map]; now rewrite app_nil_r. Qed.
Lemma out_pdec s : out s=cells(pdec s).
Proof.
  induction s as [|b s IH]; [reflexivity|].
  destruct b; cbn [out pdec]; rewrite cells_app,<-IH;
    try destruct (N.odd(cap s)); reflexivity.
Qed.

Definition SafeCP s := Adm s /\ Good s /\ (0<cap s)%N /\ exists t,s=X::t.
Definition cp s := left s root <{{B}} [S1;S2;S2;S1] *> 0inf.

Section Runs.
Variable b4 : control.
Notation tm := (family b4).
Notation "c -->* c'" := (c -[tm]->* c') (at level 40).
Notation "c -->+ c'" := (c -[tm]->+ c') (at level 40).

Lemma cdec_run s : (0<cap s)%N -> forall l r,
  left s l <{{A}} r -->+ left(cdec s) l {{A}}> r.
Proof. intros H l r; apply dec_run; apply cdec_spec; exact H. Qed.

(** Keep the pending 2 at every boundary and pay each pending 1 immediately.
    This removes the separate paid/unpaid stack relation of the source proof. *)
Lemma reset_step s b : (0<=rstep b (Z.of_N(cap s)))%Z -> forall l r,
  left s l {{A}}> S2 >> dc b *> r -->+
  left(tstep s b) l {{A}}> S2 >> r.
Proof.
  destruct b; intros HC l r; cbn [tstep dc].
  - rewrite left_cons; cbn [tc]; apply right_Y.
  - eapply progress_trans; [apply right_Y|].
    eapply progress_trans; [apply right_one|].
    rewrite left_cons; cbn [tc]; apply left_Z.
  - eapply progress_trans; [apply right_V|].
    eapply progress_trans; [apply right_one|].
    change (left(W::s) l <{{A}} S2 >> r -->+
      left(cdec(W::s)) l {{A}}> S2 >> r).
    apply cdec_run; cbn [cap].
    pose proof (pop_nonneg_capacity s HC); apply N.div_str_pos; lia.
Qed.

Lemma reset_run w s : (0<=rrun w (Z.of_N(cap s)))%Z -> forall l r,
  left s l {{A}}> S2 >> cells w *> r -->*
  left(tfold s w) l {{A}}> S2 >> r.
Proof.
  revert s; induction w as [|b w IH]; intros s HC l r.
  - apply evstep_refl.
  - pose proof (rrun_nonneg_head b w (Z.of_N(cap s)) HC) as HB.
    cbn [cells flat_map]; rewrite Str_app_assoc; cbn [tfold].
    eapply evstep_trans; [apply progress_evstep; apply reset_step; exact HB|].
    apply IH; rewrite tstep_capacity by exact HB; exact HC.
Qed.

Definition Returns c :=
  (exists s, SafeCP s /\ c -->* cp s) \/ ~halts tm c.
Lemma returns_trans c c' : c -->* c' -> Returns c' -> Returns c.
Proof.
  intros H [[s [HS HR]]|HN]; [left; exists s; split; [exact HS|eapply evstep_trans; eauto]|].
  right; eapply multistep_nonhalt; eauto.
Qed.
Lemma returns_cp s : SafeCP s -> Returns(cp s).
Proof. intro H; left; exists s; split; [exact H|apply evstep_refl]. Qed.

Lemma returns_strong_zero s : cap s=0%N -> (1<=bval s)%Z ->
  Returns(left s root {{A}}> 0inf).
Proof.
  intros HC HB.
  set (w:=pdec s++[V]).
  assert (HW:rrun w 0=(2*bval s)%Z).
  { unfold w; rewrite rrun_app; reflexivity. }
  destruct (tfold_empty_props w ltac:(rewrite HW; lia))
    as [HA [HG [HC' [HB' HU]]]].
  assert (HS:SafeCP(tfold [] w)).
  { repeat split; try assumption.
    - rewrite HW in HC'; lia.
    - exists (tfold [] (pdec s)); unfold w; rewrite tfold_app; reflexivity. }
  eapply returns_trans; [apply progress_evstep; apply right_blank|].
  eapply returns_trans; [apply progress_evstep; apply overflow_root_run; exact HC|].
  rewrite out_pdec.
  assert (EW:cells w *> 0inf=cells(pdec s) *> [S2;S1] *> 0inf).
  { unfold w; rewrite cells_app,Str_app_assoc; reflexivity. }
  rewrite <-EW.
  eapply returns_trans; [apply (reset_run w []); change (0<=rrun w 0)%Z; rewrite HW; lia|].
  eapply returns_trans; [apply progress_evstep; apply right_two_blank|].
  apply returns_cp; exact HS.
Qed.

Lemma returns_strong s : Strong s -> Returns(left s root {{A}}> 0inf).
Proof.
  induction s as [s IH] using
    (well_founded_induction (well_founded_ltof _ (fun s=>N.to_nat(cap s)))).
  intro HS; destruct (N.eq_dec (cap s) 0) as [HC|HC].
  - apply returns_strong_zero; [exact HC|now apply strong_zero].
  - assert (HP:(0<cap s)%N) by lia.
    destruct (strong_round s HS HP) as [HS' HC'].
    eapply returns_trans; [apply progress_evstep; apply right_blank|].
    eapply returns_trans; [apply progress_evstep; apply cdec_run; exact HP|].
    eapply returns_trans; [apply progress_evstep; apply right_V|].
    apply (IH (W::cdec s)); [unfold ltof; lia|exact HS'].
Qed.

Lemma pushZ_cons n s : pushZ n (Z::s)=Z::pushZ n s.
Proof. induction n; [reflexivity|rewrite !pushZ_succ,IHn; reflexivity]. Qed.

Lemma Yrun n s l r :
  left s l {{A}}> cells(repeat Y n) *> r -->* left(pushZ n s) l {{A}}> r.
Proof.
  revert s; induction n as [|n IH]; intro s; [apply evstep_refl|].
  cbn [repeat cells flat_map]; rewrite Str_app_assoc.
  eapply evstep_trans; [apply progress_evstep; apply right_Y|].
  rewrite pushZ_succ,<-pushZ_cons; apply (IH (Z::s)).
Qed.
Lemma P2_Yrun n s l r :
  left s l {{A}}> S2 >> cells(repeat Y n) *> r -->*
  left(pushZ n s) l {{A}}> S2 >> r.
Proof.
  revert s; induction n as [|n IH]; intro s; [apply evstep_refl|].
  cbn [repeat cells flat_map]; rewrite Str_app_assoc.
  eapply evstep_trans; [apply progress_evstep; apply right_Y|].
  rewrite pushZ_succ,<-pushZ_cons; apply (IH (Z::s)).
Qed.

Lemma returns_tail n s : Adm s ->
  (3*(Z.of_N(cap s)+1)<=4*(bval s+1))%Z ->
  ((1<=n)%nat \/ N.odd(cap s)=true) ->
  Returns(left s root {{A}}> S2 >> cells(repeat Y n) *> S1 >> 0inf).
Proof.
  intros HA HB HN.
  eapply returns_trans; [apply P2_Yrun|].
  eapply returns_trans; [apply progress_evstep; apply right_V|].
  apply (returns_strong (W::pushZ n s)), strong_pending; assumption.
Qed.

Lemma returns_Yrun n s : Adm s -> Good s -> (1<=n)%nat ->
  ((2<=n)%nat \/ (0<cap s)%N) ->
  Returns(left s root {{A}}> cells(repeat Y n) *> S1 >> 0inf).
Proof.
  intros HA HG HN HP.
  assert (HC:(0<cap(pushZ n s))%N).
  { destruct n; [lia|rewrite pushZ_succ; cbn [cap]; lia]. }
  eapply returns_trans; [apply Yrun|].
  eapply returns_trans; [apply progress_evstep; apply right_one|].
  eapply returns_trans; [apply progress_evstep; apply cdec_run; exact HC|].
  eapply returns_trans; [apply progress_evstep; apply right_two_blank|].
  apply returns_cp, pushZ_checkpoint; assumption.
Qed.

Lemma reset_zero_run w : (0<=rrun w 0)%Z -> forall r,
  root {{A}}> S2 >> cells w *> r -->*
  left(tfold [] w) root {{A}}> S2 >> r.
Proof. intros H r; apply (reset_run w []); exact H. Qed.

Lemma returns_reset_P2 w n : (0<=rrun w 0)%Z ->
  ((1<=n)%nat \/ (1<=rrun w 0)%Z) ->
  Returns(root {{A}}> S2 >> cells w *> S2 >> cells(repeat Y n) *> S1 >> 0inf).
Proof.
  intros HW HN; destruct (tfold_empty_props w HW) as [HA [HG [HC HR]]].
  eapply returns_trans; [apply reset_zero_run; exact HW|].
  change (Returns(left(tfold [] w) root {{A}}>
    cells(repeat Y (S n)) *> S1 >> 0inf)).
  apply returns_Yrun; try assumption; [lia|].
  destruct HN; [left|right]; lia.
Qed.

Lemma returns_reset_Yrun w n : (0<=rrun w 0)%Z -> (1<=n)%nat ->
  Returns(root {{A}}> S2 >> cells w *> cells(repeat Y n) *> S1 >> 0inf).
Proof.
  intros HW HN; destruct (tfold_empty_props w HW) as [HA [HG HR]].
  eapply returns_trans; [apply reset_zero_run; exact HW|].
  apply returns_tail; [exact HA|apply tail_bound_of_good; exact HG|left; exact HN].
Qed.

Lemma returns_overflow s b n : Adm s -> (0<=bval s)%Z -> cap s=0%N ->
  ((1<=n)%nat \/ b=Y) ->
  Returns(left s root <{{A}} dc b *> S2 >> cells(repeat Y n) *> S1 >> 0inf).
Proof.
  intros HA HB HC HN.
  destruct (Z_le_dec 0 (rstep b (bval s))) as [HR|HR].
  - eapply returns_trans; [apply progress_evstep; apply overflow_root_run; exact HC|].
    rewrite out_pdec,<-cells_snoc.
    apply returns_reset_P2.
    + rewrite rrun_app; exact HR.
    + destruct HN as [HN | ->]; [left; exact HN|right].
      rewrite rrun_app; change (1<=2*bval s+1)%Z; lia.
  - assert (EB:b=D).
    { destruct b; cbn [rstep] in HR; try lia; reflexivity. }
    subst b; assert (HN':(1<=n)%nat) by (destruct HN; [assumption|discriminate]).
    assert (HB':(bval s<=1)%Z).
    { cbn [rstep] in HR; pose proof (div2_bounds (bval s)); lia. }
    destruct (pdec s) as [|x xs] eqn:HE.
    + destruct n as [|n]; [lia|].
      eapply returns_trans; [apply overflow_run; exact HC|].
      rewrite out_pdec,HE; right; unfold root.
      apply xy_spinout_nonhalt.
    + assert (Hne:pdec s<>[]) by (rewrite HE; discriminate).
      destruct (overflow_retry s HA HC ltac:(lia) Hne) as [HA' [HG' [HC' HB'']]].
      eapply returns_trans; [apply progress_evstep; apply overflow_root_run; exact HC|].
      rewrite out_pdec.
      eapply returns_trans; [apply reset_zero_run; exact HB|].
      eapply returns_trans; [apply progress_evstep; apply right_V|].
      eapply returns_trans; [apply progress_evstep; apply right_one|].
      eapply returns_trans;
        [apply progress_evstep; apply (overflow_root_run b4 (W::tfold [] (pdec s))); exact HC'|].
      rewrite out_pdec.
      change (Returns(root {{A}}> S2 >> cells(pdec(W::tfold [] (pdec s))) *>
        cells(repeat Y (S n)) *> S1 >> 0inf)).
      apply returns_reset_Yrun; [exact HB''|lia].
Qed.

Lemma returns_dP2 s b n : Adm s -> Good s -> (b=D \/ b=Y) ->
  ((1<=n)%nat \/ b=Y) ->
  Returns(left s root <{{A}} dc b *> S2 >> cells(repeat Y n) *> S1 >> 0inf).
Proof.
  intros HA HG HB HN; destruct (N.eq_dec (cap s) 0) as [HC|HC].
  - apply returns_overflow; auto using good_bval_nonneg.
  - assert (HP:(0<cap s)%N) by lia.
    assert (HA':Adm(cdec s)) by now apply cdec_adm.
    assert (HG':Good(cdec s)) by now apply cdec_good.
    eapply returns_trans; [apply progress_evstep; apply cdec_run; exact HP|].
    destruct HB as [-> | ->].
    + assert (HN':(1<=n)%nat) by (destruct HN; [assumption|discriminate]).
      eapply returns_trans; [apply progress_evstep; apply right_one|].
      destruct (N.eq_dec (cap(cdec s)) 0) as [HC'|HC'].
      * apply (returns_overflow (cdec s) V n); auto using good_bval_nonneg.
      * assert (HP':(0<cap(cdec s))%N) by lia.
        assert (H2:(2<=cap s)%N) by (rewrite cdec_capacity in HP' by exact HP; lia).
        eapply returns_trans; [apply progress_evstep; apply cdec_run; exact HP'|].
        eapply returns_trans; [apply progress_evstep; apply right_V|].
        apply (returns_tail n (W::cdec(cdec s))).
        -- rewrite <-cdec_W by exact H2; apply cdec_adm, adm_W; [exact HA|].
           pose proof (capacity_two_bits s HA H2); lia.
        -- apply tail_bound_of_good; rewrite <-cdec_W by exact H2.
           apply good_paid_W; assumption.
        -- left; exact HN'.
    + eapply returns_trans; [apply progress_evstep; apply right_Y|].
      apply (returns_tail n (Z::cdec s)).
      * now apply adm_Z.
      * apply tail_bound_of_good, good_Z; exact HG'.
      * right; cbn [cap]; rewrite N.odd_add,N.odd_mul; reflexivity.
Qed.

Lemma returns_P1_tail s n : Adm s -> Good s -> (1<=n)%nat ->
  Returns(left s root {{A}}> S1 >> cells(repeat Y n) *> S1 >> 0inf).
Proof.
  intros HA HG HN; destruct n; [lia|].
  eapply returns_trans; [apply progress_evstep; apply right_one|].
  apply (returns_dP2 s Y n); auto.
Qed.

End Runs.
End BB25FamilyReturn.

(* BB25FamilyCases.v *)
Close Scope Z_scope. Close Scope N_scope.
From BusyCoq Require Import Individual25.
Open Scope sym_scope.
From Coq Require Import List NArith ZArith Lia.
Import ListNotations BB25FamilyRules
  BB25FamilyCore BB25FamilyWord
  BB25FamilyStack BB25FamilyReset
  BB25FamilyMachine BB25FamilyDrain
  BB25FamilyBounds BB25FamilyReturn.

Module BB25FamilyCases.

Lemma case_two_decrements b4 s l r : (2<=cap s)%N ->
  left s l <{{A}} [S1;S4;S1] *> r -[family b4]->+
  left(cdec(cdec s)) l {{A}}> [S2;S4;S1] *> r.
Proof.
  intro H; assert (H1:(0<cap s)%N) by lia.
  assert (H2:(0<cap(cdec s))%N) by (rewrite cdec_capacity by exact H1; lia).
  eapply progress_trans; [apply cdec_run; exact H1|].
  eapply progress_trans; [apply right_one|].
  apply cdec_run; exact H2.
Qed.

Theorem returns_W_1RA s n : Adm s -> Good s -> (2<=cap s)%N ->
  (1<=n)%nat ->
  Returns (Some(S1,R,A))
    (left s root <{{A}} [S1;S4;S1] *> cells(repeat Y n) *> S1 >> 0inf).
Proof.
  intros HA HG HC HN.
  eapply returns_trans; [apply progress_evstep; apply case_two_decrements; exact HC|].
  eapply returns_trans; [apply progress_evstep; apply G_1RA|].
  change (Returns (Some(S1,R,A))
    (left(X::cdec(cdec s)) root {{A}}> S2 >> cells(repeat Y n) *> S1 >> 0inf)).
  apply returns_tail.
  - apply adm_X,cdec_adm,cdec_adm; exact HA.
  - apply tail_bound_of_good,good_X,cdec_good,cdec_good; exact HG.
  - left; exact HN.
Qed.

End BB25FamilyCases.

(* BB25FamilyClosure.v *)
Close Scope Z_scope. Close Scope N_scope.
From BusyCoq Require Import Individual25.
Open Scope sym_scope.
From Coq Require Import List NArith ZArith Lia String.
Import ListNotations BB25FamilyRules
  BB25FamilyCore BB25FamilyWord
  BB25FamilyStack BB25FamilyReset
  BB25FamilyMachine BB25FamilyReturn
  BB25FamilySeed BB25FamilyCases.

Module BB25FamilyClosure.

Definition sweep s (n:nat) :=
  left s root <{{B}} S1 >> cells(repeat Y n) *> S1 >> 0inf.

(** Preserve both margins of the source interface for later B4 variants.
    The bit-producing members below need only the two available decrements. *)
Definition WCase b4 : Prop := forall s (n:nat),
  Adm s -> Good s -> (2<=cap s)%N ->
  (cap s=2%N -> (4<=bval s)%Z) ->
  ((cap s mod 2=0)%N -> (Z.of_N(cap s)+2<=bval s)%Z) ->
  (2<=n)%nat ->
  Returns b4 (left s root <{{A}} [S1;S4;S1] *>
    cells(repeat Y n) *> S1 >> 0inf).

Definition GBit b4 d : Prop := forall l r,
  l {{A}}> [S2;S4;S1] *> r -[family b4]->+
  l <{{A}} dc d *> S2 >> r.

Lemma gBit_3RA : GBit (Some(S3,R,A)) D.
Proof. intros l r; apply G_3RA. Qed.
Lemma gBit_2LA : GBit (Some(S2,L,A)) Y.
Proof. intros l r; apply G_2LA. Qed.

Lemma wcase_of_gBit b4 d : GBit b4 d ->(d=D \/ d=Y) ->WCase b4.
Proof.
  intros HG Hd s n HA HS HC _ _ Hn.
  assert (H1:(0<cap s)%N) by lia.
  assert (H2:(0<cap(cdec s))%N) by (rewrite cdec_capacity by exact H1; lia).
  eapply returns_trans; [apply progress_evstep; apply cdec_run; exact H1|].
  eapply returns_trans; [apply progress_evstep; apply right_one|].
  eapply returns_trans; [apply progress_evstep; apply cdec_run; exact H2|].
  eapply returns_trans; [apply progress_evstep; apply HG|].
  apply returns_dP2.
  - now apply cdec_adm,cdec_adm.
  - now apply cdec_good,cdec_good.
  - exact Hd.
  - left; lia.
Qed.

Lemma wcase_3RA : WCase (Some(S3,R,A)).
Proof. eapply wcase_of_gBit; [apply gBit_3RA|left; reflexivity]. Qed.
Lemma wcase_2LA : WCase (Some(S2,L,A)).
Proof. eapply wcase_of_gBit; [apply gBit_2LA|right; reflexivity]. Qed.

Lemma wcase_1RA : WCase (Some(S1,R,A)).
Proof. intros s n HA HG HC _ _ Hn; apply returns_W_1RA; try assumption; lia. Qed.

Lemma sweep_even_margin s : Good(W::s) ->(cap s mod 2=0)%N ->
  (Z.of_N(cap s)+2<=bval s)%Z.
Proof.
  intros HG HE. pose proof (good_bound (W::s) HG) as HB.
  assert (HO:N.odd(cap s)=false).
  { rewrite odd_of_N; apply Z.eqb_neq.
    change (Z.of_N(cap s) mod Z.of_N 2 <> 1)%Z.
    rewrite <-N2Z.inj_mod,HE; discriminate. }
  rewrite bval_W,HO in HB; cbn [cap] in HB; rewrite N2Z.inj_div in HB.
  assert (HE':(Z.of_N(cap s) mod 2=0)%Z).
  { change (Z.of_N(cap s) mod Z.of_N 2=0)%Z.
    rewrite <-N2Z.inj_mod,HE; reflexivity. }
  pose proof (Z.div_mod (Z.of_N(cap s)) 2 ltac:(lia)) as HC.
  pose proof (div2_bounds (bval s)) as HD; cbn [Z.of_N] in HB; lia.
Qed.

Section Closure.
Variable b4 : option(Sym*dir*Q).
Hypothesis hW : WCase b4.
Notation tm := (family b4).
Notation "c -->* c'" := (c -[tm]->* c') (at level 40).
Notation "c -->+ c'" := (c -[tm]->+ c') (at level 40).

Lemma returns_sweep s : Adm s ->Good s ->(0<cap s)%N ->
  forall n, (2<=n)%nat ->Returns b4 (sweep s n).
Proof.
  induction s as [|b s IH]; intros HA HG HC n Hn; [cbn [cap] in HC; lia|].
  pose proof (proj1 HA) as HA'. pose proof (proj1 HG) as HG'.
  destruct b.
  - unfold sweep; rewrite left_cons; cbn [tc].
    eapply returns_trans; [apply progress_evstep; apply B1_Z|].
    apply (returns_dP2 b4 s D n); auto; left; lia.
  - unfold sweep; rewrite left_cons; cbn [tc].
    eapply returns_trans; [apply progress_evstep; apply B1_X|].
    change (Returns b4 (sweep s (S n))).
    apply IH; try assumption; [cbn [cap] in HC; lia|lia].
  - assert (H2:(2<=cap s)%N) by (cbn [cap] in HC; lia).
    unfold sweep; rewrite left_cons; cbn [tc].
    eapply returns_trans; [apply progress_evstep; apply B1_W|].
    apply hW; try assumption.
    + intro HE; pose proof (sweep_even_margin s HG ltac:(rewrite HE; reflexivity));
        rewrite HE in H; cbn [Z.of_N] in H; lia.
    + apply sweep_even_margin; exact HG.
Qed.

(** The first X is removed before using a reflexive Returns result. Thus
    every checkpoint-to-checkpoint branch has genuinely positive progress. *)
Lemma cp_progress s : SafeCP s ->
  (exists t, cp s -->+ cp t /\ SafeCP t) \/ ~halts tm (cp s).
Proof.
  intros [HA [HG [HC [t ->]]]].
  assert (HR:cp(X::t) -->+ sweep t 2).
  { unfold cp,sweep; rewrite left_cons; cbn [tc cells flat_map repeat dc].
    apply B1_X. }
  assert (HT:Returns b4 (sweep t 2)).
  { apply returns_sweep; [exact (proj1 HA)|exact (proj1 HG)| |lia].
    cbn [cap] in HC; lia. }
  destruct HT as [[s [HS Hrun]]|HN].
  - left; exists s; split; [eapply progress_evstep_trans; eassumption|exact HS].
  - right; eapply multistep_nonhalt; [apply progress_evstep; exact HR|exact HN].
Qed.

Lemma safe_nonhalt s : SafeCP s -> ~halts tm (cp s).
Proof.
  intro HS.
  apply (progress_nonhalt_or tm (fun c=>exists s,SafeCP s /\ c=cp s)).
  - intros c [t [HT ->]]. destruct (cp_progress t HT) as [[u [HR HU]]|HN].
    + left; exists (cp u); split; [exact HR|exists u; split; [exact HU|reflexivity]].
    + right; exact HN.
  - exists s; split; [exact HS|reflexivity].
Qed.

Theorem family_nonhalt : ~halts tm c0.
Proof.
  eapply multistep_nonhalt; [apply seed_run|].
  apply safe_nonhalt; exact seed_safe.
Qed.

End Closure.
End BB25FamilyClosure.

Import BB25FamilyClosure.
Open Scope string_scope.

Module TM_3RA.
Definition tm := Eval compute in (TM_from_str "1RB2LA0RB1LB---_1LA3RA1RA4LB3RA").
Theorem nonhalt : ~halts tm c0.
Proof. change (~halts (family(Some(S3,R,A))) c0); apply family_nonhalt,wcase_3RA. Qed.
End TM_3RA.

Module TM_2LA.
Definition tm := Eval compute in (TM_from_str "1RB2LA0RB1LB---_1LA3RA1RA4LB2LA").
Theorem nonhalt : ~halts tm c0.
Proof. change (~halts (family(Some(S2,L,A))) c0); apply family_nonhalt,wcase_2LA. Qed.
End TM_2LA.

Module TM_1RA.
Definition tm := Eval compute in (TM_from_str "1RB2LA0RB1LB---_1LA3RA1RA4LB1RA").
Theorem nonhalt : ~halts tm c0.
Proof. change (~halts (family(Some(S1,R,A))) c0); apply family_nonhalt,wcase_1RA. Qed.
End TM_1RA.

(* BB25FamilyExcept.v *)
Close Scope Z_scope. Close Scope N_scope.
From BusyCoq Require Import Individual25.
Open Scope sym_scope.
From Coq Require Import List NArith ZArith Lia.
Import ListNotations BB25FamilyRules
  BB25FamilyCore BB25FamilyWord
  BB25FamilyStack BB25FamilyReset
  BB25FamilyMachine BB25FamilyDrain
  BB25FamilyBounds BB25FamilyReturn.

Module BB25FamilyExcept.

Lemma values_W_cdec2 s : (2<=cap s)%N ->
  cap(W::cdec(cdec s))=((cap s-2)/2)%N /\
  bval(W::cdec(cdec s))=
    (if N.odd(cap s-2) then 2*bval s else bval s/2-1)%Z.
Proof.
  intro H; split; [cbn [cap]; now rewrite cap_cdec_twice|].
  rewrite bval_W,!cdec_bval,cap_cdec_twice by exact H; reflexivity.
Qed.
Lemma adm_W_cdec2 s : Adm s -> (2<=cap s)%N -> Adm(W::cdec(cdec s)).
Proof.
  intros HA HC; rewrite <-cdec_W by exact HC; apply cdec_adm,adm_W; [exact HA|].
  pose proof (capacity_two_bits s HA HC); lia.
Qed.

Section Runs.
Variable b4 : option(Sym*dir*Q).
Notation tm := (family b4).
Notation "c -->* c'" := (c -[tm]->* c') (at level 40).
Notation "c -->+ c'" := (c -[tm]->+ c') (at level 40).

(** No invariant is needed to reach this checkpoint: it is an exact run. *)
Lemma Yrun_cp n s l :
  left s l {{A}}> cells(repeat Y (S n)) *> S1 >> 0inf -->+
  left(X::pushZ n s) l <{{B}} [S1;S2;S2;S1] *> 0inf.
Proof.
  eapply evstep_progress_trans; [apply Yrun|].
  eapply progress_trans; [apply right_one|].
  rewrite pushZ_succ,!left_cons; cbn [tc].
  eapply progress_trans; [apply left_Z|apply right_two_blank].
Qed.

Lemma returns_YP2_weak s n : Adm s -> (0<=bval s)%Z ->
  (3*Z.of_N(cap s)<=4*bval s+4)%Z ->
  Returns b4 (left s root <{{A}} dc Y *> S2 >> cells(repeat Y n) *> S1 >> 0inf).
Proof.
  intros HA HB HB'; destruct (N.eq_dec (cap s) 0) as [HC|HC].
  - apply returns_overflow; auto.
  - assert (HP:(0<cap s)%N) by lia.
    eapply returns_trans; [apply progress_evstep; apply cdec_run; exact HP|].
    eapply returns_trans; [apply progress_evstep; apply right_Y|].
    apply (returns_tail b4 n (Z::cdec s)).
    + apply adm_Z,cdec_adm; exact HA.
    + rewrite bval_Z,cdec_bval; cbn [cap]; rewrite cdec_capacity by exact HP; lia.
    + right; cbn [cap]; rewrite N.odd_add,N.odd_mul; reflexivity.
Qed.
Lemma returns_P1_tail_weak s n : Adm s -> (0<=bval s)%Z ->
  (3*Z.of_N(cap s)<=4*bval s+4)%Z -> (1<=n)%nat ->
  Returns b4 (left s root {{A}}> S1 >> cells(repeat Y n) *> S1 >> 0inf).
Proof.
  intros HA HB HB' HN; destruct n; [lia|].
  eapply returns_trans; [apply progress_evstep; apply right_one|].
  apply returns_YP2_weak; assumption.
Qed.
Lemma returns_dX_weak s n : Adm s -> (2<=cap s)%N ->
  (3*(Z.of_N(cap(W::cdec(cdec s)))+1)<=4*(bval(W::cdec(cdec s))+1))%Z ->
  (1<=n)%nat ->
  Returns b4 (left s root <{{A}} dc D *> S2 >> cells(repeat Y n) *> S1 >> 0inf).
Proof.
  intros HA HC HB HN.
  assert (H1:(0<cap s)%N) by lia.
  assert (H2:(0<cap(cdec s))%N) by (rewrite cdec_capacity by exact H1; lia).
  eapply returns_trans; [apply progress_evstep; apply cdec_run; exact H1|].
  eapply returns_trans; [apply progress_evstep; apply right_one|].
  eapply returns_trans; [apply progress_evstep; apply cdec_run; exact H2|].
  eapply returns_trans; [apply progress_evstep; apply right_V|].
  apply (returns_tail b4 n (W::cdec(cdec s))); auto using adm_W_cdec2.
Qed.
End Runs.

Open Scope Z_scope.
Lemma bal_pdec_nat s : Adm s -> bal(pdec s)=Z.of_nat(nbit s-nsh s).
Proof. intro H; rewrite bal_pdec; pose proof (adm_bound s H); lia. Qed.

Lemma paid_stack_facts s : Adm s -> Good s -> (2<=nbit s-nsh s)%nat ->
  let t:=tfold [] (pdec s) in
  Adm t /\ Good t /\ Z.of_N(cap t)=bval s /\ bval t=trun(pdec s) 0 0 /\
  (Z.of_N(cap t) mod 2=1 \/ 11<=bval t).
Proof.
  intros HA HG HH; cbn zeta.
  pose proof (good_bval_nonneg s HG) as HB.
  destruct (tfold_empty_props (pdec s) HB) as [HA' [HG' [EC [EB Hbits]]]].
  split; [exact HA'|split; [exact HG'|split; [exact EC|split; [exact EB|]]]].
  rewrite EC,EB.
  pose proof (pdec_dyck s HA) as HD.
  pose proof (bal_pdec_nat s HA) as HE.
  pose proof (pow2_mono 2 (nbit s-nsh s) HH) as HP.
  change (4<=pow2(nbit s-nsh s)) in HP.
  destruct (qcnt(pdec s) 0) eqn:HQ.
  - left; assert (HN:~HasCl(pdec s)).
    { intro HC; pose proof (qcnt_pos_of_hasCl (pdec s) 0 HD HC); lia. }
    assert (HL:(1<=length(pdec s))%nat).
    { destruct (pdec s); cbn [bal length] in *; lia. }
    pose proof (no_close_repeat (pdec s) HN) as HR.
    unfold bval; rewrite HR,rrun_repeat_Y.
    destruct (pow2_even (length(pdec s)) HL) as [v HV]; rewrite HV; lia.
  - right; pose proof (trun_ge_pow_q1 (pdec s) (nbit s-nsh s) 0 0 HD HE
      ltac:(lia) ltac:(lia)) as HT; lia.
Qed.

Lemma paid_stack_mod_four s : Adm s -> Good s -> (2<=nbit s-nsh s)%nat ->
  bval s mod 4=0 -> 43<=bval(tfold [] (pdec s)).
Proof.
  intros HA HG HH HM.
  destruct (paid_stack_facts s HA HG HH) as [_ [_ [_ [EB _]]]].
  rewrite EB.
  pose proof (pdec_dyck s HA) as HD.
  pose proof (bal_pdec_nat s HA) as HE.
  pose proof (good_bval_nonneg s HG) as HB.
  assert (HQ:(2<=qcnt(pdec s) 0)%nat).
  { destruct (le_lt_dec 2 (qcnt(pdec s) 0)); [assumption|].
    pose proof (rrun_mod_four_ne (pdec s) (nbit s-nsh s) HD HE HB ltac:(lia) HH).
    contradiction. }
  pose proof (trun_ge_pow_q2 (pdec s) (nbit s-nsh s) 0 0 HD HE
    ltac:(lia) HQ) as HT.
  pose proof (pow2_mono 2 (nbit s-nsh s) HH) as HP.
  change (4<=pow2(nbit s-nsh s)) in HP; lia.
Qed.

End BB25FamilyExcept.

(* BB25FamilyMarker.v *)
Close Scope Z_scope. Close Scope N_scope.
From BusyCoq Require Import Individual25.
Open Scope sym_scope.
From Coq Require Import List NArith ZArith Lia String Arith.Wf_nat.
Import ListNotations BB25FamilyRules
  BB25FamilyCore BB25FamilyWord
  BB25FamilyStack BB25FamilyReset
  BB25FamilyMachine BB25FamilyDrain
  BB25FamilyBounds BB25FamilyReturn
  BB25FamilyCases BB25FamilyClosure.

Module BB25FamilyMarker.

(** A marker is just a finite nearest-head-first prefix of an arbitrary
    side. The shadow counter needs no replacement datatype or interpreter. *)
Definition MarkTurn b4 (m:list Sym) : Prop := forall l r,
  m *> l <{{A}} r -[family b4]->+ left [X] l {{A}}> S2 >> r.
Definition GMarker b4 (m:list Sym) : Prop := forall l r,
  l {{A}}> [S2;S4;S1] *> r -[family b4]->+ m *> l {{A}}> r.

Definition marker_tail : side :=
  dc D *> S2 >> cells(repeat Y 2) *> S1 >> 0inf.

Section Runs.
Variable b4 : control.
Notation tm := (family b4).
Notation "c -->* c'" := (c -[tm]->* c') (at level 40).
Notation "c -->+ c'" := (c -[tm]->+ c') (at level 40).

(** The same protected drain works over every bottom side. Only its
    numerical Strong invariant is needed at the eventual overflow. *)
Lemma drain_bottom s : Strong s ->forall l,
  exists z, cap z=0%N /\ (1<=bval z)%Z /\
    left s l {{A}}> 0inf -->+ l <{{A}} out z *> [S2;S1] *> 0inf.
Proof.
  induction s as [s IH] using
    (well_founded_induction (well_founded_ltof _ (fun s=>N.to_nat(cap s)))).
  intros HS l; destruct (N.eq_dec (cap s) 0) as [HC|HC].
  - exists s; split; [exact HC|split; [now apply strong_zero|]].
    eapply progress_evstep_trans; [apply right_blank|].
    apply overflow_run; exact HC.
  - assert (HP:(0<cap s)%N) by lia.
    destruct (strong_round s HS HP) as [HS' HC'].
    destruct (IH (W::cdec s) ltac:(unfold ltof; lia) HS' l)
      as [z [HZ [HB HR]]].
    exists z; split; [exact HZ|split; [exact HB|]].
    eapply progress_trans; [apply right_blank|].
    eapply progress_trans; [apply cdec_run; exact HP|].
    eapply progress_trans; [|exact HR].
    rewrite left_cons; cbn [tc]; apply right_V.
Qed.

Lemma marker_reset_end s w : Adm s ->Good s ->
  (1<=rrun (w++[V]) (Z.of_N(cap s)))%Z ->
  Returns b4 (left s root {{A}}> S2 >> cells(w++[V]) *> 0inf).
Proof.
  intros HA HG HR.
  destruct (tfold_props (w++[V]) s HA HG ltac:(lia)) as [HA' [HG' [HC Hrest]]].
  eapply returns_trans; [apply reset_run; lia|].
  eapply returns_trans; [apply progress_evstep; apply right_two_blank|].
  apply returns_cp; split; [exact HA'|split; [exact HG'|split]].
  - lia.
  - exists (tfold s w); rewrite tfold_app; reflexivity.
Qed.

Lemma marker_returns_Y3 s : Adm s ->Good s ->
  Returns b4 (left s root <{{A}} cells(repeat Y 3) *> S1 >> 0inf).
Proof.
  intros HA HG; destruct (N.eq_dec (cap s) 0) as [HC|HC].
  - eapply returns_trans; [apply progress_evstep; apply overflow_root_run; exact HC|].
    rewrite out_pdec; apply returns_reset_Yrun; [apply good_bval_nonneg; exact HG|lia].
  - eapply returns_trans; [apply progress_evstep; apply cdec_run; lia|].
    apply returns_Yrun; [now apply cdec_adm|now apply cdec_good|lia|left; lia].
Qed.

Lemma marker_paid_props s : Adm s ->Good s ->(2<=cap s)%N ->
  Adm(W::cdec(cdec s)) /\ Good(W::cdec(cdec s)).
Proof.
  intros HA HG HC; rewrite <-cdec_W by exact HC; split.
  - apply cdec_adm,adm_W; [exact HA|pose proof (capacity_two_bits s HA HC); lia].
  - apply good_paid_W; assumption.
Qed.

Variable m : list Sym.
Hypothesis hm : MarkTurn b4 m.

Lemma marker_core_zero s : Adm s ->Good s ->
  (Z.of_N(cap s)+1<=bval s)%Z ->
  Returns b4 (m *> left s root <{{A}} marker_tail).
Proof.
  intros HA HG HB.
  eapply returns_trans; [apply progress_evstep; apply hm|].
  change (Returns b4 (left(X::s) root {{A}}> S2 >> marker_tail)).
  eapply returns_trans; [apply progress_evstep; apply right_V|].
  eapply returns_trans; [apply progress_evstep; apply right_one|].
  change (Returns b4 (left(W::X::s) root <{{A}} cells(repeat Y 3) *> S1 >> 0inf)).
  apply marker_returns_Y3.
  - apply adm_W; [now apply adm_X|cbn [nbit nsh]; pose proof (adm_bound s HA); lia].
  - apply good_W; [now apply good_X|rewrite bval_X; cbn [cap]; lia].
Qed.

Lemma marker_core_one s : Adm s ->Good s ->
  Returns b4 (left [Z] (m *> left s root) <{{A}} marker_tail).
Proof.
  intros HA HG; rewrite left_cons; cbn [tc].
  eapply returns_trans; [apply progress_evstep; apply left_Z|].
  eapply returns_trans; [apply progress_evstep; apply right_one|].
  eapply returns_trans; [apply progress_evstep; apply left_X|].
  eapply returns_trans; [apply progress_evstep; apply hm|].
  eapply returns_trans; [apply progress_evstep; apply right_Y|].
  eapply returns_trans; [apply progress_evstep; apply right_Y|].
  eapply returns_trans; [apply progress_evstep; apply right_one|].
  change (Returns b4 (left(Z::Z::X::s) root <{{A}} cells(repeat Y 3) *> S1 >> 0inf)).
  apply marker_returns_Y3.
  - apply adm_Z,adm_Z,adm_X; exact HA.
  - apply good_Z,good_Z,good_X; exact HG.
Qed.

Lemma marker_core_big s k : Adm s ->Good s ->
  Returns b4 (left(pushZ (S(S k)) []) (m *> left s root) <{{A}} marker_tail).
Proof.
  intros HA HG.
  set (p:=pushZ (S(S k)) []).
  assert (HAp:Adm p) by (apply pushZ_adm; exact I).
  assert (HGp:Good p) by (apply pushZ_good; exact I).
  assert (HCp:(2<=cap p)%N) by (unfold p; rewrite !pushZ_succ; cbn [cap]; lia).
  assert (H1:(0<cap p)%N) by lia.
  assert (H2:(0<cap(cdec p))%N) by (rewrite cdec_capacity by exact H1; lia).
  destruct (marker_paid_props p HAp HGp HCp) as [HAt HGt].
  assert (HS:Strong(W::pushZ 2 (W::cdec(cdec p)))).
  { apply strong_pending; [exact HAt|apply tail_bound_of_good; exact HGt|left; lia]. }
  eapply returns_trans; [apply progress_evstep; apply cdec_run; exact H1|].
  eapply returns_trans; [apply progress_evstep; apply right_one|].
  eapply returns_trans; [apply progress_evstep; apply cdec_run; exact H2|].
  eapply returns_trans; [apply progress_evstep; apply right_V|].
  change (Returns b4 (left(W::cdec(cdec p)) (m *> left s root)
    {{A}}> S2 >> cells(repeat Y 2) *> S1 >> 0inf)).
  eapply returns_trans; [apply P2_Yrun|].
  eapply returns_trans; [apply progress_evstep; apply right_V|].
  change (Returns b4 (left(W::pushZ 2 (W::cdec(cdec p))) (m *> left s root) {{A}}> 0inf)).
  destruct (drain_bottom _ HS (m *> left s root)) as [z [HZ [HB HR]]].
  eapply returns_trans; [apply progress_evstep; exact HR|].
  eapply returns_trans; [apply progress_evstep; apply hm|].
  change (Returns b4 (left(X::s) root {{A}}> S2 >> out z *> [S2;S1] *> 0inf)).
  rewrite out_pdec.
  change (Returns b4 (left(X::s) root {{A}}>
    S2 >> cells(pdec z) *> dc V *> 0inf)).
  rewrite <-cells_snoc.
  apply marker_reset_end; [now apply adm_X|now apply good_X|].
  rewrite rrun_app; cbn [rrun rstep].
  pose proof (rrun_mono (pdec z) 0 (Z.of_N(cap(X::s))) ltac:(lia)) as HM.
  change (1<=2*rrun (pdec z) (Z.of_N(cap(X::s))))%Z.
  change (1<=rrun (pdec z) 0)%Z in HB; lia.
Qed.

Lemma marker_core s n : Adm s ->Good s ->
  (Z.of_N(cap s)+1<=bval s)%Z ->
  Returns b4 (left(pushZ n []) (m *> left s root) <{{A}} marker_tail).
Proof.
  intros HA HG HB; destruct n as [|[|k]].
  - apply marker_core_zero; assumption.
  - apply marker_core_one; assumption.
  - apply marker_core_big; assumption.
Qed.

Lemma marker_tail_run n l :
  left(pushZ (S(S n)) []) l {{A}}> S1 >> 0inf -->+
  left(pushZ n []) l <{{A}} marker_tail.
Proof.
  rewrite !pushZ_succ,!left_cons; cbn [tc]. unfold marker_tail; execute.
Qed.

Lemma wcase_of_marker : GMarker b4 m ->WCase b4.
Proof.
  intros hG s n HA HG HC _ _ Hn.
  destruct n as [|[|n]]; [lia|lia|].
  assert (HA':Adm(cdec(cdec s))) by now apply cdec_adm,cdec_adm.
  assert (HG':Good(cdec(cdec s))) by now apply cdec_good,cdec_good.
  assert (HB:(Z.of_N(cap(cdec(cdec s)))+1<=bval(cdec(cdec s)))%Z).
  { rewrite cap_cdec_twice by exact HC; rewrite !cdec_bval.
    pose proof (good_bound s HG); lia. }
  eapply returns_trans; [apply progress_evstep; apply case_two_decrements; exact HC|].
  eapply returns_trans; [apply progress_evstep; apply hG|].
  change (Returns b4 (left [] (m *> left(cdec(cdec s)) root) {{A}}>
    cells(repeat Y (S(S n))) *> S1 >> 0inf)).
  eapply returns_trans; [apply Yrun|].
  eapply returns_trans; [apply progress_evstep; apply marker_tail_run|].
  apply marker_core; assumption.
Qed.
End Runs.

Lemma mark_0RA : MarkTurn (Some(S0,R,A)) [S1;S1;S0].
Proof. intros l r; apply left_K1. Qed.
Lemma mark_2RB : MarkTurn (Some(S2,R,B)) [S3;S2;S0].
Proof. intros l r; apply left_J2. Qed.
Lemma marker_0RA : GMarker (Some(S0,R,A)) [S1;S1;S0].
Proof. intros l r; apply G_0RA. Qed.
Lemma marker_2RB : GMarker (Some(S2,R,B)) [S3;S2;S0].
Proof. intros l r; apply G_B_right. Qed.

Theorem wcase_0RA : WCase (Some(S0,R,A)).
Proof. eapply wcase_of_marker; [apply mark_0RA|apply marker_0RA]. Qed.
Theorem wcase_2RB : WCase (Some(S2,R,B)).
Proof. eapply wcase_of_marker; [apply mark_2RB|apply marker_2RB]. Qed.

End BB25FamilyMarker.

Import BB25FamilyMarker.
Open Scope string_scope.
Module TM_0RA.
Definition tm := Eval compute in (TM_from_str "1RB2LA0RB1LB---_1LA3RA1RA4LB0RA").
Theorem nonhalt : ~halts tm c0.
Proof. change (~halts (family(Some(S0,R,A))) c0); apply family_nonhalt,wcase_0RA. Qed.
End TM_0RA.
Module TM_2RB.
Definition tm := Eval compute in (TM_from_str "1RB2LA0RB1LB---_1LA3RA1RA4LB2RB").
Theorem nonhalt : ~halts tm c0.
Proof. change (~halts (family(Some(S2,R,B))) c0); apply family_nonhalt,wcase_2RB. Qed.
End TM_2RB.

(* BB25FamilyZero.v *)
Close Scope Z_scope. Close Scope N_scope.
From BusyCoq Require Import Individual25.
Open Scope sym_scope.
From Coq Require Import List NArith ZArith Lia String.
Import ListNotations BB25FamilyRules
  BB25FamilyCore BB25FamilyWord
  BB25FamilyStack BB25FamilyReset
  BB25FamilyMachine BB25FamilyDrain
  BB25FamilyBounds BB25FamilyReturn
  BB25FamilyCases BB25FamilyClosure
  BB25FamilyExcept.

Module BB25FamilyZero.
Open Scope Z_scope.
Notation b4 := (Some(S0,L,A)).
Notation tm := (family b4).
Notation "c -->* c'" := (c -[tm]->* c') (at level 40).
Notation "c -->+ c'" := (c -[tm]->+ c') (at level 40).

Lemma zero_paid3 s : Adm s -> Good s -> (3<=cap s)%N ->
  Adm(W::cdec(cdec(cdec s))) /\ Good(W::cdec(cdec(cdec s))).
Proof.
  intros HA HG HC.
  pose proof (cap_cdec_twice s ltac:(lia)) as EC.
  assert (HP:(0<cap(cdec(cdec s)))%N) by lia.
  split.
  - apply adm_W; [now apply cdec_adm,cdec_adm,cdec_adm|].
    destruct (cdec_counts s) as [E1 E2].
    destruct (cdec_counts (cdec s)) as [E3 E4].
    destruct (cdec_counts (cdec(cdec s))) as [E5 E6].
    rewrite E5,E6,E3,E4,E1,E2.
    pose proof (capacity_one_bit s HA ltac:(lia)); lia.
  - apply good_W; [now apply cdec_good,cdec_good,cdec_good|].
    rewrite !cdec_bval,cdec_capacity by exact HP.
    pose proof (good_bound s HG); lia.
Qed.

Theorem wcase_0LA_ord s n : Adm s -> Good s -> (3<=cap s)%N -> (1<=n)%nat ->
  Returns b4 (left s root <{{A}} [S1;S4;S1] *> cells(repeat Y n) *> S1 >> 0inf).
Proof.
  intros HA HG HC HN; destruct (zero_paid3 s HA HG HC) as [HA3 HG3].
  assert (HP:(0<cap(cdec(cdec s)))%N) by (rewrite cap_cdec_twice by lia; lia).
  eapply returns_trans; [apply progress_evstep; apply case_two_decrements; lia|].
  eapply returns_trans; [apply progress_evstep; apply G_0LA|].
  eapply returns_trans; [apply progress_evstep; apply cdec_run; exact HP|].
  eapply returns_trans; [apply progress_evstep; apply right_V|].
  apply (returns_P1_tail b4 (W::cdec(cdec(cdec s))) n); assumption.
Qed.

Lemma WX_values s : cap(W::X::s)=cap s /\ (bval(W::X::s)=bval s-1)%Z.
Proof.
  split.
  - cbn [cap]; replace (2*cap s)%N with (cap s*2)%N by lia.
    apply N.div_mul; discriminate.
  - rewrite bval_W,bval_X; cbn [cap]; rewrite N.odd_mul.
    change ((2*bval s+1)/2-1=bval s-1)%Z.
    pose proof (div2_bounds (bval s)); pose proof (div2_bounds (2*bval s+1)); lia.
Qed.
Lemma WX_adm s : Adm s -> Adm(W::X::s).
Proof. intro HA; apply adm_W; [now apply adm_X|cbn [nbit nsh]; pose proof (adm_bound s HA); lia]. Qed.
Lemma WX_good s : Good s -> (Z.of_N(cap s)+1<=bval s)%Z -> Good(W::X::s).
Proof.
  intros HG HB; split; [now apply good_X|].
  destruct (WX_values s) as [EC EB]; rewrite EC,EB; lia.
Qed.

Lemma zero_repair_tail_bound i t : (4<=cap t)%N -> bval t=Z.of_N(cap t) ->
  (N.odd(cap t)=true \/ (11<=bval t)%Z) ->
  let s:=pushZ i (W::X::t) in
  (2<=cap s)%N /\
  (3*(Z.of_N(cap(W::cdec(cdec s)))+1)<=4*(bval(W::cdec(cdec s))+1))%Z.
Proof.
  intros HT EB HD; cbn zeta.
  destruct (WX_values t) as [Eca Eba].
  pose proof (pushZ_zcapacity i (W::X::t)) as EC.
  pose proof (pushZ_bval i (W::X::t)) as EV.
  rewrite Eca in EC; rewrite Eba,EB in EV.
  pose proof (BB25FamilyWord.pow2_pos i) as HP.
  assert (HS:(2<=cap(pushZ i (W::X::t)))%N) by nia.
  split; [exact HS|].
  rewrite bval_W,!cdec_bval; cbn [cap].
  rewrite cap_cdec_twice by exact HS; rewrite N2Z.inj_div.
  assert (ES:Z.of_N(cap(pushZ i (W::X::t))-2)=Z.of_N(cap(pushZ i (W::X::t)))-2) by lia.
  rewrite ES.
  set (a:=Z.of_N(cap(pushZ i (W::X::t)))) in *.
  set (v:=bval(pushZ i (W::X::t))) in *.
  change (3*((a-2)/2+1)<=4*((if N.odd(cap(pushZ i (W::X::t))-2) then 2*v else v/2-1)+1))%Z.
  pose proof (div2_bounds (a-2)) as Hdiv.
  pose proof (div2_bounds v) as Hvdiv.
  destruct i as [|i].
  - change (a+1=1*(Z.of_N(cap t)+1))%Z in EC.
    change (v=1*(Z.of_N(cap t)-1+1)-1)%Z in EV.
    destruct (N.odd(cap(pushZ 0 (W::X::t))-2)) eqn:HO; [lia|].
    assert (Hbig:(11<=Z.of_N(cap t))%Z).
    { destruct HD as [HD|HD]; [|lia].
      rewrite odd_of_N in HD,HO; apply Z.eqb_eq in HD; apply Z.eqb_neq in HO.
      change ((Z.of_N(cap(pushZ 0 (W::X::t))-2) mod 2)<>1)%Z in HO.
      rewrite ES in HO.
      pose proof (Z.div_mod (Z.of_N(cap t)) 2 ltac:(lia)).
      pose proof (Z.div_mod (a-2) 2 ltac:(lia)).
      pose proof (Z.mod_pos_bound (a-2) 2 ltac:(lia)); lia. }
    lia.
  - assert (HO:N.odd(cap(pushZ (S i) (W::X::t))-2)=true).
    { rewrite odd_of_N; apply Z.eqb_eq; rewrite ES.
      rewrite BB25FamilyWord.pow2_succ in EC.
      pose proof (Z.div_mod (a-2) 2 ltac:(lia)).
      pose proof (Z.mod_pos_bound (a-2) 2 ltac:(lia)); nia. }
    rewrite HO; nia.
Qed.

Lemma returns_WXt t n : Adm t -> Good t -> (4<=cap t)%N ->
  (N.odd(cap t)=true \/ 11<=bval t) -> (1<=n)%nat ->
  Returns b4 (left(W::X::t) root {{A}}> cells(repeat Y n) *> S1 >> 0inf).
Proof.
  intros HA HG HC HD HN.
  destruct (WX_values t) as [Eca Eba].
  assert (HAK:Adm(W::X::t)) by now apply WX_adm.
  destruct (Z_le_dec (Z.of_N(cap t)+1) (bval t)) as [HB|HB].
  - apply returns_Yrun; [exact HAK|now apply WX_good|exact HN|right; rewrite Eca; lia].
  - assert (EB:bval t=Z.of_N(cap t)) by (pose proof (good_bound t HG); lia).
    destruct n as [|j]; [lia|].
    eapply returns_trans; [apply progress_evstep; apply Yrun_cp|].
    rewrite left_cons; cbn [tc].
    eapply returns_trans; [apply progress_evstep; apply B1_X|].
    destruct j as [|i].
    + change (Returns b4 (left(W::X::t) root <{{B}}
        S1 >> cells(repeat Y 2) *> S1 >> 0inf)).
      rewrite left_cons; cbn [tc].
      eapply returns_trans; [apply progress_evstep; apply B1_W|].
      apply wcase_0LA_ord; [now apply adm_X|now apply good_X|cbn [cap]; lia|lia].
    + rewrite pushZ_succ,left_cons; cbn [tc].
      eapply returns_trans; [apply progress_evstep; apply B1_Z|].
      change (Returns b4 (left(pushZ i (W::X::t)) root <{{A}}
        dc D *> S2 >> cells(repeat Y 2) *> S1 >> 0inf)).
      destruct (zero_repair_tail_bound i t HC EB HD) as [HS HBnd].
      apply returns_dX_weak; [now apply pushZ_adm|exact HS|exact HBnd|lia].
Qed.

Theorem wcase_0LA_exc s n : Adm s -> Good s -> cap s=2%N -> 4<=bval s ->
  (1<=n)%nat ->
  Returns b4 (left s root <{{A}} [S1;S4;S1] *> cells(repeat Y n) *> S1 >> 0inf).
Proof.
  intros HA HG HC HB HN.
  assert (H2:(2<=cap s)%N) by lia.
  assert (EC:cap(cdec(cdec s))=0%N) by (rewrite cap_cdec_twice by exact H2; lia).
  destruct (paid_stack_facts s HA HG (capacity_two_bits s HA H2))
    as [HAt [HGt [ECt [EBt HDt]]]].
  assert (HR:0<=rrun (pdec s++[V]) 0).
  { rewrite rrun_app; change (0<=2*bval s); lia. }
  eapply returns_trans; [apply progress_evstep; apply case_two_decrements; exact H2|].
  eapply returns_trans; [apply progress_evstep; apply G_0LA|].
  eapply returns_trans; [apply progress_evstep; apply overflow_root_run; exact EC|].
  rewrite out_pdec,!cdec_pdec.
  change (Returns b4 (root {{A}}> S2 >> cells(pdec s) *>
    dc V *> S1 >> cells(repeat Y n) *> S1 >> 0inf)).
  rewrite <-cells_snoc.
  eapply returns_trans; [apply reset_zero_run; exact HR|].
  rewrite tfold_app; cbn [tfold tstep].
  eapply returns_trans; [apply progress_evstep; apply right_V|].
  apply (returns_WXt (tfold [] (pdec s)) n); try assumption.
  - lia.
  - destruct HDt as [HO|HBt]; [left; rewrite odd_of_N; now apply Z.eqb_eq|now right].
Qed.

Theorem wcase_0LA : WCase b4.
Proof.
  intros s n HA HG HC Hcrit _ HN.
  destruct (N.eq_dec (cap s) 2) as [HE|HE].
  - apply wcase_0LA_exc; auto; lia.
  - apply wcase_0LA_ord; auto; lia.
Qed.

End BB25FamilyZero.

Open Scope string_scope.
Module TM_0LA.
Definition tm := Eval compute in (TM_from_str "1RB2LA0RB1LB---_1LA3RA1RA4LB0LA").
Theorem nonhalt : ~halts tm c0.
Proof. change (~halts (family(Some(S0,L,A))) c0); apply family_nonhalt,BB25FamilyZero.wcase_0LA. Qed.
End TM_0LA.

(* BB25FamilyOne.v *)
Close Scope Z_scope. Close Scope N_scope.
From BusyCoq Require Import Individual25.
Open Scope sym_scope.
From Coq Require Import String List NArith ZArith Lia.
Import ListNotations BB25FamilyRules
  BB25FamilyCore BB25FamilyWord
  BB25FamilyStack BB25FamilyReset
  BB25FamilyMachine BB25FamilyDrain
  BB25FamilyBounds BB25FamilyReturn
  BB25FamilyCases BB25FamilyClosure
  BB25FamilyExcept.

Module BB25FamilyOne.
Open Scope Z_scope.

(** The mod-eight barrier excludes the one-expanding-close word shape. *)
Lemma paid_stack_mod_eight s : Adm s -> Good s ->
  (2<=nbit s-nsh s)%nat -> 4<=bval s -> bval s mod 8=2 ->
  43<=bval(tfold [] (pdec s)).
Proof.
  intros HA HG HH H4 HM.
  destruct (paid_stack_facts s HA HG HH) as [_ [_ [_ [EB _]]]].
  rewrite EB.
  pose proof (pdec_dyck s HA) as HD.
  pose proof (bal_pdec_nat s HA) as HE.
  pose proof (good_bval_nonneg s HG) as HB.
  assert (HQ:(2<=qcnt(pdec s) 0)%nat).
  { destruct (le_lt_dec 2 (qcnt(pdec s) 0)); [assumption|].
    destruct (rrun_shape_le_one (pdec s) (nbit s-nsh s)
      HD HE HB ltac:(lia) HH) as [HO|[e [He Hv]]].
    - change (bval s mod 2=1) in HO; lia.
    - change (bval s=pow2 e-2) in Hv.
      destruct e as [|[|[|e]]]; try lia.
      + change (bval s=2) in Hv; lia.
      + rewrite !pow2_succ in Hv; lia. }
  pose proof (trun_ge_pow_q2 (pdec s) (nbit s-nsh s) 0 0 HD HE
    ltac:(lia) HQ) as HT.
  pose proof (pow2_mono 2 (nbit s-nsh s) HH) as HP.
  change (4<=pow2(nbit s-nsh s)) in HP; lia.
Qed.

(** A temporary loss of goodness by one unit is repairable at a sufficiently
    large counter; the even counters need the stronger lower bound. *)
Definition Repair s : Prop :=
  3<=Z.of_N(cap s) /\ Z.of_N(cap s)-1<=bval s /\
  (Z.of_N(cap s) mod 2=0 -> 8<=Z.of_N(cap s)).

Lemma repair_tail_bound K j : Repair K ->
  (2<=cap(pushZ j K))%N /\
  3*(Z.of_N(cap(W::cdec(cdec(pushZ j K))))+1)<=
    4*(bval(W::cdec(cdec(pushZ j K)))+1).
Proof.
  intros [HA [HB HE]].
  pose proof (pushZ_zcapacity j K) as EC.
  pose proof (pushZ_bval j K) as EB.
  pose proof (pow2_pos j) as HP.
  assert (HC:(2<=cap(pushZ j K))%N) by nia.
  split; [exact HC|].
  destruct (values_W_cdec2 (pushZ j K) HC) as [EA ED].
  rewrite EA,ED,N2Z.inj_div.
  assert (ES:Z.of_N(cap(pushZ j K)-2)=Z.of_N(cap(pushZ j K))-2) by lia.
  rewrite ES; cbn [Z.of_N].
  pose proof (div2_bounds (Z.of_N(cap(pushZ j K))-2)) as HD.
  pose proof (div2_bounds (bval(pushZ j K))) as HF.
  rewrite odd_of_N,ES.
  destruct j as [|j].
  - rewrite pushZ_zero in *.
    destruct (Z.eqb_spec ((Z.of_N(cap K)-2) mod 2) 1) as [HO|HO].
    + lia.
    + pose proof (Z.mod_pos_bound (Z.of_N(cap K)-2) 2 ltac:(lia)) as HM.
      assert (HE':Z.of_N(cap K) mod 2=0) by lia.
      specialize (HE HE'); lia.
  - destruct (pow2_even (S j) ltac:(lia)) as [p EP].
    assert (HO:(Z.of_N(cap(pushZ (S j) K))-2) mod 2=1) by nia.
    rewrite (proj2 (Z.eqb_eq _ _) HO).
    nia.
Qed.

Section Runs.
Variable b4 : option(Sym*dir*Q).

Lemma repair_return K j : Adm K -> Repair K ->
  Returns b4 (left(pushZ j K) root <{{A}}
    dc D *> S2 >> cells(repeat Y 2) *> S1 >> 0inf).
Proof.
  intros HA HR; destruct (repair_tail_bound K j HR) as [HC HB].
  apply returns_dX_weak; auto using pushZ_adm; lia.
Qed.

Lemma returns_tail_or_repair K n : Adm K -> (Good K \/ Repair K) ->
  (2<=n)%nat ->
  Returns b4 (left K root {{A}}> cells(repeat Y n) *> S1 >> 0inf).
Proof.
  intros HA [HG|HR] HN.
  - apply returns_Yrun; [exact HA|exact HG|lia|left; lia].
  - destruct n as [|[|j]]; try lia.
    eapply returns_trans; [apply progress_evstep; apply Yrun_cp|].
    rewrite left_cons; cbn [tc].
    eapply returns_trans; [apply progress_evstep; apply B1_X|].
    rewrite pushZ_succ,left_cons; cbn [tc].
    eapply returns_trans; [apply progress_evstep; apply B1_Z|].
    apply repair_return; assumption.
Qed.

Lemma returns_overflow_P1 s d n : cap s=0%N ->
  0<=rstep d (bval s) -> (2<=n)%nat ->
  (Good(W::tfold [] (pdec s++[d])) \/ Repair(W::tfold [] (pdec s++[d]))) ->
  Returns b4 (left s root <{{A}}
    dc d *> S1 >> cells(repeat Y n) *> S1 >> 0inf).
Proof.
  intros HC HD HN HG.
  assert (HW:0<=rrun (pdec s++[d]) 0).
  { rewrite rrun_app; exact HD. }
  destruct (tfold_empty_props (pdec s++[d]) HW) as [HA [_ [_ [_ HB]]]].
  assert (Hne:pdec s++[d]<>[]).
  { intro E; apply app_eq_nil in E; destruct E; discriminate. }
  specialize (HB Hne).
  eapply returns_trans; [apply progress_evstep; apply overflow_root_run; exact HC|].
  rewrite out_pdec,<-cells_snoc.
  eapply returns_trans; [apply reset_zero_run; exact HW|].
  eapply returns_trans; [apply progress_evstep; apply right_V|].
  change (Returns b4 (left(W::tfold [] (pdec s++[d])) root
    {{A}}> cells(repeat Y n) *> S1 >> 0inf)).
  apply returns_tail_or_repair; try assumption.
  apply adm_W; [exact HA|lia].
Qed.

Lemma returns_XP1_big s n : Adm s -> Good s -> (2<=cap s)%N ->
  (1<=n)%nat ->
  Returns b4 (left s root <{{A}} dc D *> S1 >> cells(repeat Y n) *> S1 >> 0inf).
Proof.
  intros HA HG HC HN.
  assert (H1:(0<cap s)%N) by lia.
  assert (H2:(0<cap(cdec s))%N) by (rewrite cdec_capacity by exact H1; lia).
  eapply returns_trans; [apply progress_evstep; apply cdec_run; exact H1|].
  eapply returns_trans; [apply progress_evstep; apply right_one|].
  eapply returns_trans; [apply progress_evstep; apply cdec_run; exact H2|].
  eapply returns_trans; [apply progress_evstep; apply right_V|].
  change (Returns b4 (left(W::cdec(cdec s)) root {{A}}>
    S1 >> cells(repeat Y n) *> S1 >> 0inf)).
  apply returns_P1_tail; [apply adm_W_cdec2; assumption| |exact HN].
  apply good_W; [apply cdec_good,cdec_good; exact HG|].
  rewrite cap_cdec_twice by exact HC; rewrite !cdec_bval.
  pose proof (good_bound s HG); lia.
Qed.

Lemma values_WX s : cap(W::X::s)=cap s /\ bval(W::X::s)=bval s-1.
Proof.
  split.
  - cbn [cap]; replace (2*cap s)%N with (cap s*2)%N by lia.
    apply N.div_mul; discriminate.
  - rewrite bval_W,bval_X; cbn [cap]; rewrite N.odd_mul.
    change ((2*bval s+1)/2-1=bval s-1).
    pose proof (div2_bounds (2*bval s+1)); lia.
Qed.

Lemma returns_XP1_one s n : Adm s -> Good s ->
  Z.of_N(cap s)+2<=bval s -> (2<=nbit s-nsh s)%nat -> cap s=1%N ->
  (2<=n)%nat ->
  Returns b4 (left s root <{{A}} dc D *> S1 >> cells(repeat Y n) *> S1 >> 0inf).
Proof.
  intros HA HG HL HH HC HN.
  assert (HP:(0<cap s)%N) by lia.
  assert (HC':cap(cdec s)=0%N) by (rewrite cdec_capacity by exact HP; lia).
  assert (HH':(2<=nbit(cdec s)-nsh(cdec s))%nat).
  { destruct (cdec_counts s); lia. }
  destruct (paid_stack_facts (cdec s) (cdec_adm s HA) (cdec_good s HG) HH')
    as [HAt [HGt [EC [EB HD]]]].
  rewrite cdec_bval in EC.
  pose proof (good_bound _ HGt) as HT.
  eapply returns_trans; [apply progress_evstep; apply cdec_run; exact HP|].
  eapply returns_trans; [apply progress_evstep; apply right_one|].
  apply (returns_overflow_P1 (cdec s) V n); try assumption.
  - change (0<=2*bval(cdec s)); rewrite cdec_bval; lia.
  - rewrite tfold_app; change
      (Good(W::X::tfold [] (pdec(cdec s))) \/ Repair(W::X::tfold [] (pdec(cdec s)))).
    destruct (values_WX (tfold [] (pdec(cdec s)))) as [EK EBK].
    destruct (Z_le_dec (Z.of_N(cap(tfold [] (pdec(cdec s))))+1)
      (bval(tfold [] (pdec(cdec s))))) as [HS|HS].
    + left; split; [apply good_X; exact HGt|rewrite EK,EBK; lia].
    + right; unfold Repair; rewrite EK,EBK.
      split; [rewrite EC; rewrite HC in HL; cbn [Z.of_N] in HL; lia|].
      split; [lia|intro HE; destruct HD; lia].
Qed.

(** Two successive halving closes can lose only one unit. The 11 and 43
    expansion barriers rule out precisely the small unrecoverable counters. *)
Lemma zero_repair_arith f g : 4<=f -> f<=g ->
  (f mod 2=1 \/ 11<=g) -> (f mod 8=2 -> 43<=g) ->
  let v:=f/2-1 in
  let d:=if Z.eqb (f mod 2) 1 then 2*g else g/2-1 in
  v<=d ->
  let k:=v/2 in
  let b:=if Z.eqb (v mod 2) 1 then 2*d else d/2-1 in
  k<=b \/ (3<=k /\ k-1<=b /\ (k mod 2=0 -> 8<=k)).
Proof.
  intros HF HG HD H43; cbn zeta; intro HV.
  destruct (Z.eqb_spec ((f/2-1) mod 2) 1) as [HO|HO].
  - left; destruct (Z.eqb_spec (f mod 2) 1); lia.
  - destruct (Z.eqb_spec (f mod 2) 1) as [HE|HE].
    + left; lia.
    + destruct (Z_le_dec ((f/2-1)/2) ((g/2-1)/2-1)) as [HB|HB].
      * left; exact HB.
      * right.
        assert (HM:f mod 4=2) by lia.
        assert (HG':g<=f+3) by lia.
        assert (H11:11<=g) by (destruct HD; lia).
        assert (H8:f mod 8=2 \/ f mod 8=6) by lia.
        split.
        -- destruct H8 as [H8|H8]; [specialize (H43 H8); lia|lia].
        -- split; [lia|intro HK].
           assert (H8':f mod 8=2) by lia; specialize (H43 H8'); lia.
Qed.

Lemma reset_D_repair s : Adm s -> Good s -> 4<=bval s ->
  (2<=nbit s-nsh s)%nat ->
  Good(W::tfold [] (pdec s++[D])) \/ Repair(W::tfold [] (pdec s++[D])).
Proof.
  intros HA HG H4 HH.
  destruct (paid_stack_facts s HA HG HH) as [HAt [HGt [EC [EB HD]]]].
  set (t:=tfold [] (pdec s)) in *.
  assert (HT2:(2<=cap t)%N) by lia.
  assert (HW:(0<cap(W::t))%N).
  { cbn [cap]; apply N.div_str_pos; lia. }
  pose proof (good_paid_W t HGt HT2) as HGu.
  pose proof (good_bound t HGt) as Ht.
  pose proof (good_bound _ HGu) as Hu.
  assert (EU:Z.of_N(cap(cdec(W::t)))=Z.of_N(cap t)/2-1).
  { rewrite cdec_capacity by exact HW.
    assert (E:Z.of_N(cap(W::t)-1)=Z.of_N(cap(W::t))-1) by lia.
    rewrite E; cbn [cap]; rewrite N2Z.inj_div; reflexivity. }
  assert (BU:bval(cdec(W::t))=
    if Z.eqb (Z.of_N(cap t) mod 2) 1 then 2*bval t else bval t/2-1).
  { rewrite cdec_bval,bval_W,odd_of_N; reflexivity. }
  assert (EK:Z.of_N(cap(W::cdec(W::t)))=(Z.of_N(cap t)/2-1)/2).
  { change (Z.of_N(cap(cdec(W::t))/2)=(Z.of_N(cap t)/2-1)/2).
    rewrite N2Z.inj_div,EU; reflexivity. }
  assert (BK:bval(W::cdec(W::t))=
    if Z.eqb ((Z.of_N(cap t)/2-1) mod 2) 1 then
      2*(if Z.eqb (Z.of_N(cap t) mod 2) 1 then 2*bval t else bval t/2-1)
    else (if Z.eqb (Z.of_N(cap t) mod 2) 1 then 2*bval t else bval t/2-1)/2-1).
  { rewrite bval_W,odd_of_N,EU,BU; reflexivity. }
  assert (H43:Z.of_N(cap t) mod 8=2 -> 43<=bval t).
  { intro H; apply paid_stack_mod_eight; try assumption; rewrite <-EC; exact H. }
  rewrite EU,BU in Hu.
  destruct (zero_repair_arith (Z.of_N(cap t)) (bval t)
    ltac:(lia) Ht HD H43 Hu) as [Hgood|Hrepair].
  - left; rewrite tfold_app.
    change (Good(W::cdec(W::t))).
    split; [exact HGu|rewrite EK,BK; exact Hgood].
  - right; rewrite tfold_app.
    change (Repair(W::cdec(W::t))).
    unfold Repair; rewrite EK,BK; exact Hrepair.
Qed.

Lemma returns_XP1_zero s n : Adm s -> Good s -> 4<=bval s ->
  (2<=nbit s-nsh s)%nat -> cap s=0%N -> (2<=n)%nat ->
  Returns b4 (left s root <{{A}} dc D *> S1 >> cells(repeat Y n) *> S1 >> 0inf).
Proof.
  intros HA HG H4 HH HC HN.
  apply returns_overflow_P1; try assumption.
  - change (0<=bval s/2-1); lia.
  - apply reset_D_repair; assumption.
Qed.

End Runs.

Theorem wcase_1LB : WCase (Some(S1,L,B)).
Proof.
  intros s n HA HG HC Hcrit _ HN.
  pose proof (cap_cdec_twice s HC) as EC.
  pose proof (cdec_adm _ (cdec_adm s HA)) as HA'.
  pose proof (cdec_good _ (cdec_good s HG)) as HG'.
  assert (EB:bval(cdec(cdec s))=bval s) by now rewrite !cdec_bval.
  assert (HH:(2<=nbit(cdec(cdec s))-nsh(cdec(cdec s)))%nat).
  { destruct (cdec_counts s); destruct (cdec_counts (cdec s)).
    pose proof (capacity_two_bits s HA HC); lia. }
  eapply returns_trans; [apply progress_evstep; apply case_two_decrements; exact HC|].
  eapply returns_trans; [apply progress_evstep; apply G_B_left|].
  change (Returns (Some(S1,L,B)) (left(cdec(cdec s)) root <{{A}}
    dc D *> S1 >> cells(repeat Y n) *> S1 >> 0inf)).
  destruct (N.eq_dec (cap(cdec(cdec s))) 0) as [H0|H0].
  - apply returns_XP1_zero; try assumption.
    rewrite EB; apply Hcrit; lia.
  - destruct (N.eq_dec (cap(cdec(cdec s))) 1) as [H1|H1].
    + apply returns_XP1_one; try assumption.
      rewrite EC,EB; pose proof (good_bound s HG); lia.
    + apply returns_XP1_big; try assumption; lia.
Qed.
End BB25FamilyOne.

Module TM_1LB.
Definition tm := Eval compute in (TM_from_str "1RB2LA0RB1LB---_1LA3RA1RA4LB1LB").
Theorem nonhalt : ~halts tm c0.
Proof.
  change (~halts (family (Some(S1,L,B))) c0).
  apply family_nonhalt,BB25FamilyOne.wcase_1LB.
Qed.
End TM_1LB.

(* BB25FamilyDrainWord.v *)
Close Scope Z_scope. Close Scope N_scope.
From BusyCoq Require Import Individual25.
Open Scope sym_scope.
From Coq Require Import List NArith ZArith Lia.
Import ListNotations BB25FamilyRules
  BB25FamilyCore BB25FamilyWord
  BB25FamilyStack BB25FamilyReset
  BB25FamilyMachine BB25FamilyDrain
  BB25FamilyBounds BB25FamilyReturn
  BB25FamilyMarker.

Module BB25FamilyDrainWord.
Notation npow := BB25FamilyCore.pow2.
Definition pushW n s := Nat.iter n (cons W) s.
Lemma pushW_zero s : pushW O s=s. Proof. reflexivity. Qed.
Lemma pushW_succ n s : pushW (S n) s=W::pushW n s. Proof. reflexivity. Qed.
Lemma pushW_cons n s : pushW n (W::s)=W::pushW n s.
Proof. induction n; [reflexivity|rewrite !pushW_succ,IHn; reflexivity]. Qed.
Lemma pushW_repeat n s : pushW n s=repeat W n++s.
Proof. induction n; [reflexivity|rewrite pushW_succ,IHn; reflexivity]. Qed.
Lemma pushW_capacity n s : cap(pushW n s)=(cap s/npow n)%N.
Proof.
  induction n; [cbn [npow pushW Nat.iter]; now rewrite N.div_1_r|].
  rewrite pushW_succ; cbn [cap npow]; rewrite IHn,N.div_div by
    (pose proof (BB25FamilyCore.pow2_pos n); lia).
  f_equal; nia.
Qed.
Lemma odd_before_even a : (0<a)%N -> N.odd(a-1)=negb(N.odd a).
Proof.
  intro H; assert (E:((a-1)+1=a)%N) by lia.
  pose proof (f_equal N.odd E) as HO; rewrite N.odd_add in HO.
  destruct (N.odd(a-1)),(N.odd a); cbn in *; congruence.
Qed.
Lemma odd_of_succ_double a b : (a+1=2*b)%N -> N.odd a=true.
Proof.
  intro E; pose proof(f_equal N.odd E) as H.
  rewrite N.odd_add,N.odd_mul in H; destruct(N.odd a); cbn in *; congruence.
Qed.
Lemma pdec_Wrun_ones n s : (cap s+1=npow n)%N ->
  pdec(pushW n s)=pdec s++repeat V n.
Proof.
  revert s; induction n as [|n IH]; intros s HC.
  - cbn [pushW Nat.iter repeat]; now rewrite app_nil_r.
  - assert (HO:N.odd(cap s)=true) by (eapply odd_of_succ_double; exact HC).
    assert (HC':(cap(W::s)+1=npow n)%N).
    { cbn [cap]; cbn [npow] in HC; div2. }
    rewrite pushW_succ,<-pushW_cons,IH by exact HC'.
    cbn [pdec]; rewrite HO,<-app_assoc; reflexivity.
Qed.
Lemma rrun_repeat_V n a : rrun(repeat V n) a=(pow2 n*a)%Z.
Proof.
  revert a; induction n; intro a; [change (a=1*a)%Z; ring|].
  cbn [repeat rrun rstep]; rewrite IHn,pow2_succ; ring.
Qed.
Definition kword n := repeat Y n++[V;Y;Y;V;D]++repeat V (n-1).
Lemma rrun_kword n : (1<=n)%nat ->
  rrun(kword n) 0=(4*pow2 n*pow2 n-3*pow2 n)%Z.
Proof.
  intro H; destruct n; [lia|]. unfold kword.
  replace (S n-1)%nat with n by lia.
  rewrite !rrun_app,rrun_repeat_Y,rrun_repeat_V.
  cbn [rrun rstep]; rewrite pow2_succ.
  assert (E:((2*(2*(2*(2*(2*pow2 n*(0+1)-1))+1)+1)/2)=
    16*pow2 n-5)%Z) by lia.
  rewrite E; ring.
Qed.
Lemma rrun_kword_pos n : (1<=n)%nat -> (1<=rrun(kword n) 0)%Z.
Proof.
  intro H; rewrite rrun_kword by exact H.
  pose proof (pow2_mono 1 n H) as HP; change (2<=pow2 n)%Z in HP; nia.
Qed.

Section Runs.
Variable b4 : control.
Notation tm := (family b4).
Notation "c -->* c'" := (c -[tm]->* c') (at level 40).
Notation "c -->+ c'" := (c -[tm]->+ c') (at level 40).

Lemma Vrun n s l r :
  left s l {{A}}> cells(repeat V n) *> r -->* left(pushW n s) l {{A}}> r.
Proof.
  revert s; induction n as [|n IH]; intro s; [apply evstep_refl|].
  cbn [repeat cells flat_map]; rewrite Str_app_assoc.
  eapply evstep_trans; [apply progress_evstep; apply right_V|].
  rewrite pushW_succ,<-pushW_cons; apply (IH (W::s)).
Qed.

(** Exact drain words only for the two capacity families that are used.
    There is no general recursive word evaluator or a second run semantics. *)
Lemma drain_even n s : Strong s -> (cap s+2=2*npow n)%N -> forall l,
  left s l {{A}}> 0inf -->+
  l <{{A}} cells(pdec s++repeat V n) *> [S2;S1] *> 0inf.
Proof.
  revert s; induction n as [|n IH]; intros s HS HC l.
  - assert (HC0:cap s=0%N) by (cbn [npow] in HC; lia).
    cbn [repeat]; rewrite app_nil_r,<-out_pdec.
    eapply progress_evstep_trans; [apply right_blank|apply overflow_run; exact HC0].
  - pose proof (BB25FamilyCore.pow2_pos n) as Hpow.
    assert (HP:(0<cap s)%N) by (cbn [npow] in HC; nia).
    assert (HO:N.odd(cap s)=false).
    { pose proof(f_equal N.odd HC) as H; rewrite !N.odd_add,N.odd_mul in H.
      cbn in H; now rewrite Bool.xorb_false_r in H. }
    assert (HS':Strong(W::cdec s)) by now apply strong_step.
    assert (HC':(cap(W::cdec s)+2=2*npow n)%N).
    { cbn [cap]; rewrite cdec_capacity by exact HP; cbn [npow] in HC; div2. }
    pose proof(IH (W::cdec s) HS' HC' l) as HR.
    assert (EW:pdec(W::cdec s)++repeat V n=pdec s++repeat V(S n)).
    { cbn [pdec]; rewrite cdec_pdec,cdec_capacity by exact HP.
      rewrite odd_before_even,HO by exact HP; cbn.
      rewrite <-app_assoc; reflexivity. }
    rewrite EW in HR.
    eapply progress_trans; [apply right_blank|].
    eapply progress_trans; [apply cdec_run; exact HP|].
    eapply progress_trans; [apply right_V|exact HR].
Qed.
Lemma drain_entry n s : Strong s -> (cap s+3=4*npow n)%N -> forall l,
  left s l {{A}}> 0inf -->+
  l <{{A}} cells(pdec s++D::repeat V n) *> [S2;S1] *> 0inf.
Proof.
  intros HS HC l; pose proof(BB25FamilyCore.pow2_pos n) as Hpow.
  assert (HP:(0<cap s)%N) by nia.
  assert (HO:N.odd(cap s)=true).
  { apply odd_of_succ_double with(b:=(2*npow n-1)%N); nia. }
  assert (HS':Strong(W::cdec s)) by now apply strong_step.
  assert (HC':(cap(W::cdec s)+2=2*npow n)%N).
  { cbn [cap]; rewrite cdec_capacity by exact HP; div2. }
  pose proof(drain_even n (W::cdec s) HS' HC' l) as HR.
  assert (EW:pdec(W::cdec s)++repeat V n=pdec s++D::repeat V n).
  { cbn [pdec]; rewrite cdec_pdec,cdec_capacity by exact HP.
    rewrite odd_before_even,HO by exact HP; cbn.
    rewrite <-app_assoc; reflexivity. }
  rewrite EW in HR.
  eapply progress_trans; [apply right_blank|].
  eapply progress_trans; [apply cdec_run; exact HP|].
  eapply progress_trans; [apply right_V|exact HR].
Qed.

Definition marker_state k :=
  W::pushZ 2 (W::cdec(cdec(pushZ (S(S k)) []))).
Lemma marker_state_props k : Strong(marker_state k) /\
  (cap(marker_state k)+3=4*npow k)%N /\
  pdec(marker_state k)=repeat Y (S(S k))++[V;Y;Y;V].
Proof.
  set (p:=pushZ (S(S k)) []).
  assert (HA:Adm p) by (apply pushZ_adm; exact I).
  assert (HG:Good p) by (apply pushZ_good; exact I).
  pose proof(BB25FamilyCore.pow2_pos k) as Hpow.
  assert (HC:cap p=(4*npow k-1)%N).
  { pose proof(pushZ_capacity (S(S k)) []) as H; cbn [cap npow] in H; unfold p; lia. }
  assert (H2:(2<=cap p)%N) by lia.
  destruct (marker_paid_props p HA HG H2) as [HA' HG'].
  split.
  - apply strong_pending; [exact HA'|now apply tail_bound_of_good|left; lia].
  - assert (HO:N.odd(cap(cdec(cdec p)))=true).
    { apply odd_of_succ_double with(b:=(2*npow k-1)%N).
      rewrite cap_cdec_twice by exact H2; rewrite HC; nia. }
    assert (HO':N.odd (cap (pushZ 2 (W::cdec (cdec p))))=true).
    { rewrite pushZ_succ; cbn [cap]; rewrite N.odd_add,N.odd_mul; reflexivity. }
    split.
    + change ((2*(2*(cap(cdec(cdec p))/2)+1)+1)/2+3=4*npow k)%N.
      rewrite cap_cdec_twice by exact H2.
      rewrite HC; div2.
    + assert (EP:pdec(W::cdec(cdec p))=pdec p++[V]).
      { change (pdec(cdec(cdec p))++[if N.odd(cap(cdec(cdec p))) then V else D]=pdec p++[V]).
        rewrite HO,!cdec_pdec; reflexivity. }
      change (pdec(pushZ 2 (W::cdec(cdec p)))++
        [if N.odd(cap(pushZ 2 (W::cdec(cdec p)))) then V else D]=
        repeat Y(S(S k))++[V;Y;Y;V]).
      rewrite HO',pushZ_pdec,EP; unfold p; rewrite pushZ_pdec.
      cbn [pdec app]; rewrite <-!app_assoc; reflexivity.
Qed.

Lemma marker_drain k l :
  left(pushZ(S(S k))[]) l <{{A}} marker_tail -->+
  l <{{A}} cells(kword(S(S k))) *> 0inf.
Proof.
  set (p:=pushZ(S(S k))[]).
  assert (H2:(2<=cap p)%N) by (unfold p; rewrite !pushZ_succ; cbn [cap]; lia).
  assert (H1:(0<cap p)%N) by lia.
  assert (H1':(0<cap(cdec p))%N) by (rewrite cdec_capacity by exact H1; lia).
  destruct(marker_state_props k) as [HS [HC HW]].
  eapply progress_trans; [apply cdec_run; exact H1|].
  eapply progress_trans; [apply right_one|].
  eapply progress_trans; [apply cdec_run; exact H1'|].
  eapply progress_trans; [apply right_V|].
  change (left(W::cdec(cdec p)) l {{A}}>
    S2 >> cells(repeat Y 2) *> S1 >> 0inf -->+
    l <{{A}} cells(kword(S(S k))) *> 0inf).
  eapply evstep_progress_trans; [apply P2_Yrun|].
  eapply progress_trans; [apply right_V|].
  pose proof (drain_entry k (marker_state k) HS HC l) as HR.
  rewrite HW in HR.
  replace (cells((repeat Y(S(S k))++[V;Y;Y;V])++D::repeat V k) *>
    [S2;S1] *> 0inf) with (cells(kword(S(S k))) *> 0inf) in HR.
  - exact HR.
  - change (cells(kword(S(S k))) *> 0inf=
      cells((repeat Y(S(S k))++[V;Y;Y;V])++D::repeat V k) *> dc V *> 0inf).
    rewrite <-cells_snoc; f_equal.
    unfold kword; replace(S(S k)-1)%nat with(S k) by lia.
    rewrite <-!app_assoc; cbn [app]; rewrite <-repeat_cons; reflexivity.
Qed.

End Runs.
End BB25FamilyDrainWord.

(* BB25FamilyK0.v *)
Close Scope Z_scope. Close Scope N_scope.
From BusyCoq Require Import Individual25.
Open Scope sym_scope.
From Coq Require Import List NArith ZArith Lia String.
Import ListNotations BB25FamilyRules
  BB25FamilyCore BB25FamilyWord
  BB25FamilyStack BB25FamilyReset
  BB25FamilyMachine BB25FamilyDrain
  BB25FamilyBounds BB25FamilyReturn
  BB25FamilyCases BB25FamilyClosure
  BB25FamilyMarker BB25FamilyDrainWord.

Module BB25FamilyK0.
Notation cpow := BB25FamilyCore.pow2.

Definition free_base n := W::Z::Z::W::pushZ n [].
Definition free_paid n := W::cdec(free_base n).

Lemma free_base_capacity k : (cap(free_base(S k))+1=cpow(S k))%N.
Proof.
  pose proof (pushZ_capacity (S k) []) as H.
  pose proof (BB25FamilyCore.pow2_pos k) as HP.
  cbn [cap cpow] in H; unfold free_base; cbn [cap cpow]; lia.
Qed.

Lemma free_paid_capacity k : (cap(free_paid(S(S k)))+1=cpow(S k))%N.
Proof.
  pose proof (free_base_capacity (S k)) as H.
  pose proof (BB25FamilyCore.pow2_pos (S k)) as HP.
  assert (HC:(0<cap(free_base(S(S k))))%N) by (cbn [cpow] in H; lia).
  unfold free_paid; cbn [cap]; rewrite cdec_capacity by exact HC.
  cbn [cpow] in *; lia.
Qed.

Lemma free_base_pdec n : (1<=n)%nat ->
  pdec(free_base n)=repeat Y n++[V;Y;Y;V].
Proof.
  intro Hn; assert (HO:N.odd(cap(pushZ n []))=true)
    by (apply pushZ_odd; left; exact Hn).
  unfold free_base; cbn [pdec cap].
  rewrite N.odd_add,N.odd_mul; cbn [N.odd].
  rewrite HO,pushZ_pdec; cbn [pdec app].
  rewrite <-!app_assoc; reflexivity.
Qed.

Lemma free_paid_pdec k :
  pdec(free_paid(S(S k)))=repeat Y (S(S k))++[V;Y;Y;V;D].
Proof.
  pose proof (free_base_capacity (S k)) as H.
  pose proof (BB25FamilyCore.pow2_pos (S k)) as HP.
  assert (HC:(0<cap(free_base(S(S k))))%N) by (cbn [cpow] in H; lia).
  assert (HO:N.odd(cap(cdec(free_base(S(S k)))))=false).
  { rewrite cdec_capacity by exact HC; rewrite odd_of_N.
    apply Z.eqb_neq; cbn [cpow] in H; lia. }
  unfold free_paid; cbn [pdec]; rewrite HO,cdec_pdec,free_base_pdec by lia.
  rewrite <-app_assoc; reflexivity.
Qed.

Definition free_stack k := pushW (S k) (free_paid(S(S k))).
Lemma free_stack_zero k : cap(free_stack k)=0%N.
Proof.
  unfold free_stack; rewrite pushW_capacity; apply N.div_small.
  pose proof (free_paid_capacity k); lia.
Qed.
Lemma free_stack_word k : pdec(free_stack k)=kword(S(S k)).
Proof.
  unfold free_stack; rewrite pdec_Wrun_ones by apply free_paid_capacity.
  rewrite free_paid_pdec; unfold kword.
  replace (S(S k)-1)%nat with (S k) by lia.
  rewrite <-app_assoc; reflexivity.
Qed.

Section Runs.
Variable b4 : option(Sym*dir*Q).
Notation tm := (family b4).
Notation "c -->* c'" := (c -[tm]->* c') (at level 40).
Notation "c -->+ c'" := (c -[tm]->+ c') (at level 40).

Lemma marker_end s w : Adm s ->Good s ->(1<=rrun w 0)%Z ->
  Returns b4 ([S1;S1;S0] *> left s root <{{A}} cells(w++[V]) *> 0inf).
Proof.
  intros HA HG HB.
  eapply returns_trans; [apply progress_evstep; apply left_K1|].
  change (Returns b4 (left(X::s) root {{A}}> S2 >> cells(w++[V]) *> 0inf)).
  apply marker_reset_end; [now apply adm_X|now apply good_X|].
  rewrite rrun_app; cbn [rrun rstep].
  pose proof (rrun_mono w 0 (Z.of_N(cap(X::s))) ltac:(lia)); lia.
Qed.

Lemma core_zero_run l :
  [S1;S0;S0] *> l <{{A}} marker_tail -->+
  left [X;X] l {{A}}> cells(repeat Y 3) *> S1 >> 0inf.
Proof. unfold marker_tail,left; cbn [tc cells flat_map repeat dc]; execute. Qed.

Lemma core_zero s : Adm s ->Good s ->
  Returns b4 ([S1;S0;S0] *> left s root <{{A}} marker_tail).
Proof.
  intros HA HG; eapply returns_trans; [apply progress_evstep; apply core_zero_run|].
  change (Returns b4 (left(X::X::s) root {{A}}> cells(repeat Y 3) *> S1 >> 0inf)).
  apply returns_Yrun; [now apply adm_X,adm_X|now apply good_X,good_X|lia|left; lia].
Qed.

Lemma core_one_run l :
  left [Z] ([S1;S0;S0] *> l) <{{A}} marker_tail -->+
  [S1;S1;S0] *> l <{{A}} cells([Y;V;Y;Y;V;D]++[V]) *> 0inf.
Proof. unfold marker_tail,left; cbn [tc cells flat_map repeat dc]; execute. Qed.

Lemma core_one s : Adm s ->Good s ->
  Returns b4 (left [Z] ([S1;S0;S0] *> left s root) <{{A}} marker_tail).
Proof.
  intros HA HG; eapply returns_trans; [apply progress_evstep; apply core_one_run|].
  apply marker_end; [exact HA|exact HG|vm_compute; discriminate].
Qed.

(** The explicit counter phase of kword needs just one decrement. No
    goodness invariant is asserted for its intermediate shadow stack. *)
Lemma free_word_run k l :
  l {{A}}> cells(kword(S(S k))) *> 0inf -->*
  left(free_stack k) l {{A}}> 0inf.
Proof.
  assert (HC:(0<cap(free_base(S(S k))))%N).
  { pose proof (free_base_capacity (S k));
    pose proof (BB25FamilyCore.pow2_pos k); cbn [cpow] in *; lia. }
  change (left [] l {{A}}> cells(kword(S(S k))) *> 0inf -->*
    left(free_stack k) l {{A}}> 0inf).
  unfold kword; replace (S(S k)-1)%nat with (S k) by lia.
  rewrite !cells_app,!Str_app_assoc.
  eapply evstep_trans; [apply Yrun|].
  eapply evstep_trans; [apply progress_evstep; apply right_V|].
  eapply evstep_trans; [apply progress_evstep; apply right_Y|].
  eapply evstep_trans; [apply progress_evstep; apply right_Y|].
  eapply evstep_trans; [apply progress_evstep; apply right_V|].
  change (left(free_base(S(S k))) l {{A}}> dc D *> cells(repeat V (S k)) *> 0inf -->*
    left(free_stack k) l {{A}}> 0inf).
  eapply evstep_trans; [apply progress_evstep; apply right_one|].
  eapply evstep_trans; [apply progress_evstep; apply cdec_run; exact HC|].
  eapply evstep_trans; [apply progress_evstep; apply right_V|].
  change (left(free_paid(S(S k))) l {{A}}> cells(repeat V (S k)) *> 0inf -->*
    left(pushW (S k) (free_paid(S(S k)))) l {{A}}> 0inf).
  apply Vrun.
Qed.

Lemma free_cycle s k : Adm s ->Good s ->
  Returns b4 ([S1;S1;S0] *> left s root {{A}}> cells(kword(S(S k))) *> 0inf).
Proof.
  intros HA HG; eapply returns_trans; [apply free_word_run|].
  eapply returns_trans; [apply progress_evstep; apply right_blank|].
  eapply returns_trans; [apply overflow_run; apply free_stack_zero|].
  rewrite out_pdec,free_stack_word.
  change (Returns b4 ([S1;S1;S0] *> left s root <{{A}}
    cells(kword(S(S k))) *> dc V *> 0inf)).
  rewrite <-cells_snoc; apply marker_end; [exact HA|exact HG|apply rrun_kword_pos; lia].
Qed.

Lemma core_big s k : Adm s ->Good s ->
  Returns b4 (left(pushZ(S(S k))[]) ([S1;S0;S0] *> left s root) <{{A}} marker_tail).
Proof.
  intros HA HG; eapply returns_trans; [apply progress_evstep; apply marker_drain|].
  eapply returns_trans; [apply progress_evstep; apply left_K0|].
  apply free_cycle; assumption.
Qed.

Lemma core s n : Adm s ->Good s ->
  Returns b4 (left(pushZ n []) ([S1;S0;S0] *> left s root) <{{A}} marker_tail).
Proof.
  intros HA HG; destruct n as [|[|k]].
  - apply core_zero; assumption.
  - apply core_one; assumption.
  - apply core_big; assumption.
Qed.

End Runs.

Theorem wcase_2RA : WCase (Some(S2,R,A)).
Proof.
  intros s n HA HG HC _ _ Hn; destruct n as [|[|n]]; [lia|lia|].
  eapply returns_trans; [apply progress_evstep; apply case_two_decrements; exact HC|].
  eapply returns_trans; [apply progress_evstep; apply G_2RA|].
  change (Returns (Some(S2,R,A)) (left [] ([S1;S0;S0] *> left(cdec(cdec s)) root)
    {{A}}> cells(repeat Y (S(S n))) *> S1 >> 0inf)).
  eapply returns_trans; [apply Yrun|].
  eapply returns_trans; [apply progress_evstep; apply marker_tail_run|].
  apply core; [now apply cdec_adm,cdec_adm|now apply cdec_good,cdec_good].
Qed.

End BB25FamilyK0.

Import BB25FamilyK0.
Open Scope string_scope.
Module TM_2RA.
Definition tm := Eval compute in (TM_from_str "1RB2LA0RB1LB---_1LA3RA1RA4LB2RA").
Theorem nonhalt : ~halts tm c0.
Proof. change (~halts (family(Some(S2,R,A))) c0); apply family_nonhalt,wcase_2RA. Qed.
End TM_2RA.

(* BB25FamilyJOne.v *)
Close Scope Z_scope. Close Scope N_scope.
From BusyCoq Require Import Individual25.
Open Scope sym_scope.
From Coq Require Import List NArith ZArith Lia String.
Import ListNotations BB25FamilyRules
  BB25FamilyCore BB25FamilyWord
  BB25FamilyStack BB25FamilyReset
  BB25FamilyMachine BB25FamilyDrain
  BB25FamilyBounds BB25FamilyReturn
  BB25FamilyCases BB25FamilyClosure
  BB25FamilyExcept BB25FamilyMarker
  BB25FamilyDrainWord.

Module BB25FamilyJOne.
Open Scope Z_scope.
Lemma j_odd_pred a : (0<a)%N -> N.odd(a-1)=negb(N.odd a).
Proof.
  intro H; assert (E:((a-1)+1=a)%N) by lia.
  pose proof(f_equal N.odd E); rewrite N.odd_add in H0.
  destruct(N.odd(a-1)),(N.odd a); cbn in *; congruence.
Qed.
Lemma j_Z_odd s : N.odd(cap(Z::s))=true.
Proof. cbn [cap]; rewrite N.odd_add,N.odd_mul; reflexivity. Qed.
Lemma j_odd_linear s x : Z.of_N(cap s)=2*x-1 -> N.odd(cap s)=true.
Proof.
  intro H; rewrite odd_of_N; apply Z.eqb_eq; rewrite H.
  pose proof(Z.div_mod (2*x-1) 2 ltac:(lia)).
  pose proof(Z.mod_pos_bound (2*x-1) 2 ltac:(lia)); lia.
Qed.
Lemma j_even_linear s x : Z.of_N(cap s)=2*x -> N.odd(cap s)=false.
Proof.
  intro H; rewrite odd_of_N; apply Z.eqb_neq; rewrite H.
  pose proof(Z.div_mod (2*x) 2 ltac:(lia)).
  pose proof(Z.mod_pos_bound (2*x) 2 ltac:(lia)); lia.
Qed.

Definition ctpre k s := W::cdec(W::Z::Z::W::pushZ(S(S k)) s).
Lemma ctpre_props k s : Adm s ->
  Adm(ctpre k s) /\ (nsh(ctpre k s)+S k<=nbit(ctpre k s))%nat /\
  Z.of_N(cap(ctpre k s))+1=pow2(S k)*(Z.of_N(cap s)+1) /\
  bval(ctpre k s)=32*pow2 k*(bval s+1)-6 /\
  (0<cap(W::Z::Z::W::pushZ(S(S k)) s))%N.
Proof.
  intro HA; set (p:=pushZ(S(S k)) s).
  set (x:=pow2 k*(Z.of_N(cap s)+1)).
  set (y:=pow2 k*(bval s+1)).
  pose proof (BB25FamilyWord.pow2_pos k) as HP.
  assert (HX:1<=x) by (unfold x; nia).
  assert (EC1:Z.of_N(cap p)=4*x-1).
  { pose proof(pushZ_zcapacity (S(S k)) s); rewrite !pow2_succ in H; unfold p,x; nia. }
  assert (EC2:Z.of_N(cap(W::p))=2*x-1).
  { cbn [cap]; rewrite N2Z.inj_div,EC1; pose proof(div2_bounds (4*x-1)); cbn [Z.of_N]; lia. }
  assert (EC4:Z.of_N(cap(Z::Z::W::p))=8*x-1).
  { cbn [cap]; change (Z.of_N(2*(2*cap(W::p)+1)+1)%N=8*x-1); lia. }
  assert (EC5:Z.of_N(cap(W::Z::Z::W::p))=4*x-1).
  { change (Z.of_N(cap(Z::Z::W::p)/2)=4*x-1); rewrite N2Z.inj_div,EC4;
      pose proof(div2_bounds (8*x-1)); cbn [Z.of_N]; lia. }
  assert (HC5:(0<cap(W::Z::Z::W::p))%N) by lia.
  assert (ECd:Z.of_N(cap(cdec(W::Z::Z::W::p)))=4*x-2).
  { rewrite cdec_capacity by exact HC5; lia. }
  assert (EC6:Z.of_N(cap(W::cdec(W::Z::Z::W::p)))=2*x-1).
  { change (Z.of_N(cap(cdec(W::Z::Z::W::p))/2)=2*x-1).
    rewrite N2Z.inj_div,ECd; pose proof(div2_bounds (4*x-2)); cbn [Z.of_N]; lia. }
  assert (HO1:N.odd(cap p)=true) by (apply j_odd_linear with (x:=2*x); lia).
  assert (HO4:N.odd(cap(Z::Z::W::p))=true) by (apply j_odd_linear with (x:=4*x); lia).
  assert (HOd:N.odd(cap(cdec(W::Z::Z::W::p)))=false) by (apply j_even_linear with (x:=2*x-1); lia).
  assert (EB1:bval p=4*y-1).
  { unfold p; rewrite pushZ_bval,!pow2_succ; unfold y; ring. }
  assert (EB5:bval(W::Z::Z::W::p)=64*y-10).
  { rewrite bval_W,HO4,!bval_Z,bval_W,HO1,EB1; ring. }
  assert (EB6:bval(W::cdec(W::Z::Z::W::p))=32*y-6).
  { rewrite bval_W,HOd,cdec_bval,EB5; pose proof(div2_bounds (64*y-10)); lia. }
  pose proof (pushZ_counts (S(S k)) s) as [Ebit Esh].
  change (nbit p=(nbit s+S(S k))%nat) in Ebit; change (nsh p=nsh s) in Esh.
  pose proof(adm_bound s HA) as Hbal.
  assert (HAp:Adm p) by (apply pushZ_adm; exact HA).
  assert (HA2:Adm(W::p)) by (apply adm_W; [exact HAp|lia]).
  assert (HA5:Adm(W::Z::Z::W::p)).
  { apply adm_W; [now apply adm_Z,adm_Z|cbn [nbit nsh]; lia]. }
  pose proof(cdec_counts(W::Z::Z::W::p)) as [EdB EdS].
  cbn [nbit nsh] in EdB,EdS.
  assert (HA6:Adm(W::cdec(W::Z::Z::W::p))).
  { apply adm_W; [now apply cdec_adm|rewrite EdB,EdS; lia]. }
  unfold ctpre; fold p.
  split; [exact HA6|split].
  - cbn [nbit nsh]; rewrite EdB,EdS; lia.
  - split.
    + change (Z.of_N(cap(W::cdec(W::Z::Z::W::p)))+1=pow2(S k)*(Z.of_N(cap s)+1)).
      rewrite EC6,pow2_succ; unfold x; ring.
    + split; [change (bval(W::cdec(W::Z::Z::W::p))=32*pow2 k*(bval s+1)-6); rewrite EB6; unfold y; ring|exact HC5].
Qed.

Lemma Wrun_facts m s u : Adm s ->
  Z.of_N(cap s)+1=pow2 m*(Z.of_N u+1) ->
  (nsh s+m<=nbit s)%nat ->
  Adm(pushW m s) /\ cap(pushW m s)=u /\
  bval(pushW m s)=pow2 m*bval s.
Proof.
  revert s; induction m as [|m IH]; intros s HA EC HH.
  - change (Z.of_N(cap s)+1=1*(Z.of_N u+1)) in EC.
    split; [exact HA|split; [change (cap s=u); lia|change (bval s=1*bval s); ring]].
  - assert (HO:N.odd(cap s)=true).
    { apply j_odd_linear with (x:=pow2 m*(Z.of_N u+1)); rewrite pow2_succ in EC; lia. }
    assert (HAW:Adm(W::s)) by (apply adm_W; [exact HA|lia]).
    assert (ECW:Z.of_N(cap(W::s))+1=pow2 m*(Z.of_N u+1)).
    { cbn [cap]; rewrite N2Z.inj_div; cbn [Z.of_N].
      rewrite pow2_succ in EC; pose proof(div2_bounds(Z.of_N(cap s))); lia. }
    assert (HHW:(nsh(W::s)+m<=nbit(W::s))%nat) by (cbn [nsh nbit]; lia).
    destruct(IH (W::s) HAW ECW HHW) as [HA' [EC' EB']].
    rewrite pushW_succ,<-pushW_cons; split; [exact HA'|split; [exact EC'|]].
    rewrite EB',bval_W,HO,pow2_succ; ring.
Qed.

Section Runs.
Variable b4 : option(Sym*dir*Q).
Notation tm := (family b4).
Notation "c -->* c'" := (c -[tm]->* c') (at level 40).
Notation "c -->+ c'" := (c -[tm]->+ c') (at level 40).

Lemma returns_merge s w T : 0<=rrun w (Z.of_N(cap s)) ->
  Returns b4 (left(Z::tfold s w) root {{A}}> T) ->
  Returns b4 (left s root {{A}}> S2 >> cells w *> S2 >> T).
Proof.
  intros HR HC; eapply returns_trans; [apply reset_run; exact HR|].
  eapply returns_trans; [apply progress_evstep; apply right_Y|exact HC].
Qed.

Lemma returns_ct0 s : Adm s -> Good s -> N.odd(cap s)=true -> 7<=bval s ->
  Returns b4 (left s root {{A}}> marker_tail).
Proof.
  intros HA HG HO HB; pose proof (odd_capacity_positive s HO) as HC.
  assert (HA':Adm(W::cdec s)).
  { apply adm_W; [now apply cdec_adm|].
    destruct (cdec_counts s) as [E1 E2]; rewrite E1,E2.
    pose proof (capacity_one_bit s HA HC); lia. }
  eapply returns_trans; [apply progress_evstep; apply right_one|].
  eapply returns_trans; [apply progress_evstep; apply cdec_run; exact HC|].
  eapply returns_trans; [apply progress_evstep; apply right_V|].
  apply (returns_tail b4 2 (W::cdec s)); [exact HA'| |left; lia].
  rewrite bval_W,cdec_bval; cbn [cap]; rewrite cdec_capacity by exact HC.
  rewrite j_odd_pred,HO by exact HC; cbn [negb].
  rewrite N2Z.inj_div.
  assert (EC:Z.of_N(cap s-1)=Z.of_N(cap s)-1) by lia; rewrite EC.
  pose proof (good_bound s HG) as HGb.
  rewrite odd_of_N in HO; apply Z.eqb_eq in HO.
  pose proof (Z.div_mod (Z.of_N(cap s)) 2 ltac:(lia)).
  pose proof (div2_bounds (Z.of_N(cap s)-1)).
  pose proof (div2_bounds (bval s)); cbn [Z.of_N]; lia.
Qed.

Lemma returns_ct1 s : Adm s -> Good s ->
  Returns b4 (left s root {{A}}> cells [Y;V] *> S2 >> cells(repeat Y 2) *> S1 >> 0inf).
Proof.
  intros HA HG; eapply returns_trans; [apply progress_evstep; apply right_Y|].
  eapply returns_trans; [apply progress_evstep; apply right_V|].
  apply (returns_tail b4 2 (W::Z::s)).
  - apply adm_W; [now apply adm_Z|cbn [nbit nsh]; pose proof (adm_bound s HA); lia].
  - apply tail_bound_of_good,good_W_odd; [now apply good_Z|apply j_Z_odd].
  - left; lia.
Qed.

Lemma returns_ctk s k : Adm s -> Good s ->
  Returns b4 (left s root {{A}}> cells(kword(S(S k))) *> 0inf).
Proof.
  intros HA HG.
  destruct(ctpre_props k s HA) as [HAt [HHt [ECt [EBt HC]]]].
  destruct(Wrun_facts (S k) (ctpre k s) (cap s) HAt ECt HHt)
    as [HAf [ECf EBf]].
  assert (HS:Strong(pushW(S k)(ctpre k s))).
  { split; [exact HAf|rewrite ECf,EBf,EBt,pow2_succ].
    pose proof(good_bound s HG); pose proof(pow2_pos k); nia. }
  unfold kword; replace (S(S k)-1)%nat with (S k) by lia.
  rewrite cells_app,Str_app_assoc.
  eapply returns_trans; [apply Yrun|].
  change (Returns b4 (left(pushZ(S(S k))s) root {{A}}>
    S2>>S1>>S2>>S2>>S2>>S2>>S2>>S1>>S1>>S1>>cells(repeat V (S k))*>0inf)).
  eapply returns_trans; [apply progress_evstep; apply right_V|].
  eapply returns_trans; [apply progress_evstep; apply right_Y|].
  eapply returns_trans; [apply progress_evstep; apply right_Y|].
  eapply returns_trans; [apply progress_evstep; apply right_V|].
  eapply returns_trans; [apply progress_evstep; apply right_one|].
  change (Returns b4 (left(W::Z::Z::W::pushZ(S(S k))s) root <{{A}}
    S2>>S1>>cells(repeat V(S k))*>0inf)).
  eapply returns_trans; [apply progress_evstep; apply cdec_run; exact HC|].
  eapply returns_trans; [apply progress_evstep; apply right_V|].
  change (Returns b4 (left(ctpre k s) root {{A}}> cells(repeat V(S k))*>0inf)).
  eapply returns_trans; [apply Vrun|].
  apply returns_strong; exact HS.
Qed.

Lemma returns_j1_ord c T : (2<=cap c)%N ->
  Returns b4 (left(W::cdec(cdec c)) root {{A}}> S2 >> T) ->
  Returns b4 (left c root <{{A}} dc D *> S2 >> T).
Proof.
  intros HC HR; assert (H1:(0<cap c)%N) by lia.
  assert (H2:(0<cap(cdec c))%N) by (rewrite cdec_capacity by exact H1; lia).
  eapply returns_trans; [apply progress_evstep; apply cdec_run; exact H1|].
  eapply returns_trans; [apply progress_evstep; apply right_one|].
  eapply returns_trans; [apply progress_evstep; apply cdec_run; exact H2|].
  eapply returns_trans; [apply progress_evstep; apply right_V|exact HR].
Qed.

Lemma returns_j1_small c T : Adm c -> Good c -> (cap c<=1)%N ->
  Z.of_N(cap c)+2<=bval c ->
  ((cap c mod 2=0)%N -> Z.of_N(cap c)+4<=bval c) ->
  (2<=nbit c-nsh c)%nat ->
  (forall s,Adm s -> Good s -> N.odd(cap s)=true -> 7<=bval s ->
    Returns b4 (left s root {{A}}> T)) ->
  Returns b4 (left c root <{{A}} dc D *> S2 >> T).
Proof.
  intros HA HG HC HM HE HH Hcont.
  destruct (paid_stack_facts c HA HG HH) as [HAt [HGt [ECt [EBt HDt]]]].
  pose proof (good_bound _ HGt) as HBt.
  assert (HW:forall w,0<=rrun w 0 -> 3<=bval(tfold [] w) ->
    Returns b4 (root {{A}}> S2 >> cells w *> S2 >> T)).
  { intros w HR HB; apply (returns_merge [] w T); [exact HR|].
    destruct (tfold_empty_props w HR) as [HAs [HGs _]].
    apply Hcont; [now apply adm_Z|now apply good_Z|apply j_Z_odd|rewrite bval_Z; lia]. }
  destruct (N.eq_dec (cap c) 0) as [H0|H1].
  - assert (HB:4<=bval c) by (specialize (HE ltac:(rewrite H0; reflexivity)); rewrite H0 in HE; cbn [Z.of_N] in HE; lia).
    assert (HR:0<=rrun(pdec c++[D]) 0).
    { rewrite rrun_app; change (0<=bval c/2-1); pose proof (div2_bounds (bval c)); lia. }
    assert (H3:3<=bval(tfold [] (pdec c++[D]))).
    { rewrite tfold_app; cbn [tfold tstep]; rewrite cdec_bval,bval_W.
      destruct (N.odd(cap(tfold [] (pdec c)))) eqn:HO; [lia|].
      assert (H11:11<=bval(tfold [] (pdec c))).
      { destruct HDt; [rewrite odd_of_N in HO; apply Z.eqb_neq in HO; contradiction|assumption]. }
      pose proof (div2_bounds (bval(tfold [] (pdec c)))); lia. }
    eapply returns_trans; [apply progress_evstep; apply overflow_root_run; exact H0|].
    rewrite out_pdec,<-cells_snoc; apply HW; assumption.
  - assert (H1':cap c=1%N) by lia.
    assert (HP:(0<cap c)%N) by lia.
    assert (HZ:cap(cdec c)=0%N) by (rewrite cdec_capacity by exact HP; lia).
    assert (HB:3<=bval c) by (rewrite H1' in HM; cbn [Z.of_N] in HM; lia).
    assert (HR:0<=rrun(pdec c++[V]) 0) by (rewrite rrun_app; change (0<=2*bval c); lia).
    assert (H3:3<=bval(tfold [] (pdec c++[V]))).
    { rewrite tfold_app; cbn [tfold tstep]; rewrite bval_X; lia. }
    eapply returns_trans; [apply progress_evstep; apply cdec_run; exact HP|].
    eapply returns_trans; [apply progress_evstep; apply right_one|].
    eapply returns_trans; [apply progress_evstep; apply overflow_root_run; exact HZ|].
    rewrite out_pdec,cdec_pdec.
    change (Returns b4 (root {{A}}> S2 >> cells(pdec c) *> dc V *> S2 >> T)).
    rewrite <-cells_snoc; apply HW; assumption.
Qed.

Lemma returns_tau_Yrun s w : Adm s -> Good s -> 0<=rrun w (Z.of_N(cap s)) ->
  Returns b4 (left s root {{A}}> S2 >> cells w *> S2 >> cells(repeat Y 2) *> S1 >> 0inf).
Proof.
  intros HA HG HR; apply returns_merge; [exact HR|].
  destruct (tfold_props w s HA HG HR) as [HA' [HG' _]].
  apply returns_Yrun; [now apply adm_Z|now apply good_Z|lia|left; lia].
Qed.

Lemma core1RB_zero c : Adm c -> Good c ->
  Z.of_N(cap c)+2<=bval c ->
  ((cap c mod 2=0)%N -> Z.of_N(cap c)+4<=bval c) ->
  (2<=nbit c-nsh c)%nat ->
  Returns b4 ([S3;S1;S0] *> left c root <{{A}} marker_tail).
Proof.
  intros HA HG HM HE HH.
  eapply returns_trans; [apply progress_evstep; apply left_J1|].
  destruct (N.le_gt_cases (cap c) 1) as [Hsm|H2].
  - apply (returns_j1_small c marker_tail); try assumption.
    intros; now apply returns_ct0.
  - assert (HC:(2<=cap c)%N) by lia.
    destruct (marker_paid_props c HA HG HC) as [HAt HGt].
    destruct (values_W_cdec2 c HC) as [ECt EBt].
    apply returns_j1_ord; [exact HC|].
    set (t:=W::cdec(cdec c)) in *.
    destruct (N.le_gt_cases (cap t) 1) as [Ht|Ht].
    + assert (HAW:Adm(W::t)).
      { apply adm_W; [exact HAt|unfold t; cbn [nbit nsh]].
        destruct(cdec_counts c) as [E1 E2].
        destruct(cdec_counts(cdec c)) as [E3 E4].
        rewrite E3,E4,E1,E2; lia. }
      assert (HGW:Good(W::t)).
      { destruct (N.odd(cap t)) eqn:HO.
        - apply good_W_odd; assumption.
        - assert (HZ:cap t=0%N).
          { destruct (N.eq_dec (cap t) 0); [assumption|assert (cap t=1%N) by lia; rewrite H in HO; discriminate]. }
          apply good_W; [exact HGt|rewrite HZ; cbn [Z.of_N]].
          assert (HC23:cap c=2%N \/ cap c=3%N).
          { rewrite HZ in ECt; pose proof(N.div_mod (cap c-2) 2 ltac:(discriminate));
            pose proof(N.mod_lt (cap c-2) 2 ltac:(discriminate)); lia. }
          destruct HC23 as [H2'|H3'].
          + specialize (HE ltac:(rewrite H2'; reflexivity)); rewrite H2' in HE,EBt.
            change (bval t=bval c/2-1) in EBt; cbn [Z.of_N] in HE.
            pose proof(div2_bounds (bval c)); lia.
          + rewrite H3' in HM,EBt; change (bval t=2*bval c) in EBt; cbn [Z.of_N] in HM; lia. }
      eapply returns_trans; [apply progress_evstep; apply right_V|].
      eapply returns_trans; [apply progress_evstep; apply right_one|].
      change (Returns b4 (left(W::t) root <{{A}} cells(repeat Y 3) *> S1 >> 0inf)).
      apply marker_returns_Y3; assumption.
    + apply (returns_tau_Yrun t [D]); try assumption.
      change (0<=Z.of_N(cap t)/2-1); pose proof(div2_bounds (Z.of_N(cap t))); lia.
Qed.

Lemma core1RB_one c : Adm c -> Good c ->
  Z.of_N(cap c)+2<=bval c ->
  ((cap c mod 2=0)%N -> Z.of_N(cap c)+4<=bval c) ->
  (2<=nbit c-nsh c)%nat ->
  Returns b4 (left [Z] ([S3;S1;S0] *> left c root) <{{A}} marker_tail).
Proof.
  intros HA HG HM HE HH; rewrite left_cons; cbn [tc].
  eapply returns_trans; [apply progress_evstep; apply left_Z|].
  eapply returns_trans; [apply progress_evstep; apply right_one|].
  eapply returns_trans; [apply progress_evstep; apply left_X|].
  eapply returns_trans; [apply progress_evstep; apply left_J1|].
  change (Returns b4 (left c root <{{A}} dc D *> S2 >>
    cells [Y;V] *> S2 >> cells(repeat Y 2) *> S1 >> 0inf)).
  destruct (N.le_gt_cases (cap c) 1) as [Hsm|H2].
  - apply returns_j1_small; try assumption; intros; now apply returns_ct1.
  - assert (HC:(2<=cap c)%N) by lia.
    destruct (marker_paid_props c HA HG HC) as [HAt HGt].
    apply returns_j1_ord; [exact HC|].
    apply (returns_tau_Yrun (W::cdec(cdec c)) [Y;V]); try assumption.
    change (0<=2*(2*Z.of_N(cap(W::cdec(cdec c)))+1)); lia.
Qed.

Lemma kword_last k : exists w, kword(S(S k))=w++[V].
Proof.
  exists (repeat Y(S(S k))++[V;Y;Y;V;D]++repeat V k).
  unfold kword; replace (S(S k)-1)%nat with (S k) by lia.
  cbn [repeat]; rewrite (repeat_cons k V),<- !app_assoc; reflexivity.
Qed.

Lemma core1RB_big c k : Adm c -> Good c ->
  Z.of_N(cap c)+2<=bval c ->
  ((cap c mod 2=0)%N -> Z.of_N(cap c)+4<=bval c) ->
  (2<=nbit c-nsh c)%nat ->
  Returns b4 (left(pushZ(S(S k))[]) ([S3;S1;S0] *> left c root) <{{A}} marker_tail).
Proof.
  intros HA HG HM HE HH.
  eapply returns_trans; [apply progress_evstep; apply marker_drain|].
  eapply returns_trans; [apply progress_evstep; apply left_J1|].
  destruct (N.le_gt_cases (cap c) 1) as [Hsm|H2].
  - apply returns_j1_small; try assumption; intros; now apply returns_ctk.
  - assert (HC:(2<=cap c)%N) by lia.
    destruct (marker_paid_props c HA HG HC) as [HAt HGt].
    apply returns_j1_ord; [exact HC|].
    destruct (kword_last k) as [w EW]; rewrite EW.
    apply marker_reset_end; try assumption.
    rewrite <-EW; pose proof(rrun_kword_pos (S(S k)) ltac:(lia)).
    pose proof(rrun_mono (kword(S(S k))) 0 (Z.of_N(cap(W::cdec(cdec c)))) ltac:(lia)); lia.
Qed.

Lemma core1RB c n : Adm c -> Good c ->
  Z.of_N(cap c)+2<=bval c ->
  ((cap c mod 2=0)%N -> Z.of_N(cap c)+4<=bval c) ->
  (2<=nbit c-nsh c)%nat ->
  Returns b4 (left(pushZ n []) ([S3;S1;S0] *> left c root) <{{A}} marker_tail).
Proof.
  destruct n as [|[|n]]; intros.
  - now apply core1RB_zero.
  - now apply core1RB_one.
  - now apply core1RB_big.
Qed.

End Runs.

Theorem wcase_1RB : WCase (Some(S1,R,B)).
Proof.
  intros s n HA HG HC _ HE Hn.
  destruct n as [|[|n]]; [lia|lia|].
  assert (HAc:Adm(cdec(cdec s))) by now apply cdec_adm,cdec_adm.
  assert (HGc:Good(cdec(cdec s))) by now apply cdec_good,cdec_good.
  assert (EC:cap(cdec(cdec s))=(cap s-2)%N) by now apply cap_cdec_twice.
  assert (HM:(Z.of_N(cap(cdec(cdec s)))+2<=bval(cdec(cdec s)))%Z).
  { rewrite EC,!cdec_bval; pose proof(good_bound s HG); lia. }
  assert (HEc:(cap(cdec(cdec s)) mod 2=0)%N ->
    Z.of_N(cap(cdec(cdec s)))+4<=bval(cdec(cdec s))).
  { intro HCm; rewrite EC in HCm.
    assert (HSm:(cap s mod 2=0)%N).
    { pose proof(N.div_mod (cap s) 2 ltac:(discriminate)).
      pose proof(N.div_mod (cap s-2) 2 ltac:(discriminate)).
      pose proof(N.mod_lt (cap s) 2 ltac:(discriminate)); lia. }
    specialize (HE HSm); rewrite EC,!cdec_bval; lia. }
  assert (HH:(2<=nbit(cdec(cdec s))-nsh(cdec(cdec s)))%nat).
  { destruct(cdec_counts s) as [E1 E2]; destruct(cdec_counts(cdec s)) as [E3 E4].
    rewrite E3,E4,E1,E2; now apply capacity_two_bits. }
  eapply returns_trans; [apply progress_evstep; apply case_two_decrements; exact HC|].
  eapply returns_trans; [apply progress_evstep; apply G_B_right|].
  change (Returns (Some(S1,R,B))
    (left [] ([S3;S1;S0] *> left(cdec(cdec s)) root) {{A}}>
      cells(repeat Y(S(S n))) *> S1 >> 0inf)).
  eapply returns_trans; [apply Yrun|].
  eapply returns_trans; [apply progress_evstep; apply marker_tail_run|].
  apply core1RB; assumption.
Qed.
End BB25FamilyJOne.

Open Scope string_scope.
Module TM_1RB.
Definition tm := Eval compute in (TM_from_str "1RB2LA0RB1LB---_1LA3RA1RA4LB1RB").
Theorem nonhalt : ~halts tm c0.
Proof. change (~halts(family(Some(S1,R,B))) c0); apply family_nonhalt,BB25FamilyJOne.wcase_1RB. Qed.
End TM_1RB.

(* BB25FamilyReady.v *)
Close Scope Z_scope. Close Scope N_scope.
From BusyCoq Require Import Individual25.
Open Scope sym_scope.
From Coq Require Import List NArith ZArith Lia.
Import ListNotations BB25FamilyRules
  BB25FamilyCore BB25FamilyWord
  BB25FamilyStack BB25FamilyReset
  BB25FamilyMachine BB25FamilyDrain
  BB25FamilyReturn BB25FamilySeed.

Module BB25FamilyReady.

Fixpoint Strict s : Prop := match s with
| []=>True
| _::t=>Strict t /\ (1<=nbit s -> nsh s+1<=nbit s)%nat
end.
Lemma strict_nil : Strict []. Proof. exact I. Qed.
Lemma strict_tail b s : Strict(b::s) -> Strict s.
Proof. exact (fun H=>proj1 H). Qed.
Lemma strict_head s : Strict s -> (1<=nbit s -> nsh s+1<=nbit s)%nat.
Proof. destruct s; [cbn; lia|exact (fun H=>proj2 H)]. Qed.
Lemma strict_suffix p s : Strict(p++s) ->Strict s.
Proof. induction p; [auto|intro H; apply IHp; exact(proj1 H)]. Qed.
Lemma strict_Z s : Adm s ->Strict s ->Strict(Z::s).
Proof. intros HA HS; split; [exact HS|cbn[nbit nsh]; pose proof(adm_bound s HA); lia]. Qed.
Lemma strict_X s : Adm s ->Strict s ->Strict(X::s).
Proof. intros HA HS; split; [exact HS|cbn[nbit nsh]; pose proof(adm_bound s HA); lia]. Qed.
Lemma strict_W s : Strict s ->(nsh s+2<=nbit s)%nat ->Strict(W::s).
Proof. intros HS HH; split; [exact HS|cbn[nbit nsh]; lia]. Qed.

Lemma dec_strict w : forall d v, dec d w=Some v ->Strict w ->Strict v.
Proof.
  induction w as [|b w IH]; intros d v H HS; [discriminate|].
  destruct HS as [HS HB].
  destruct b,d; cbn[dec] in H;
    try (destruct(dec _ w) as [u|] eqn:E; [|discriminate]);
    inversion H; subst; cbn[Strict nbit nsh] in *;
    try (destruct(dec_counts _ _ _ E) as [EB ES]; rewrite EB,ES);
    split; eauto.
Qed.
Lemma strict_cdec s : Strict s ->Strict(cdec s).
Proof. intro H; unfold cdec; destruct(dec O s) eqn:E; eauto using dec_strict. Qed.
Lemma strict_pushZ n s : Adm s ->Strict s ->Strict(pushZ n s).
Proof.
  intros HA HS; induction n; [exact HS|rewrite pushZ_succ].
  apply strict_Z; [now apply pushZ_adm|exact IHn].
Qed.
Lemma strict_tstep s b : Adm s ->Strict s ->
  (0<=rstep b (Z.of_N(cap s)))%Z ->Strict(tstep s b).
Proof.
  intros HA HS HC; destruct b; cbn[tstep].
  - now apply strict_Z.
  - now apply strict_X.
  - apply strict_cdec,strict_W; [exact HS|].
    pose proof(pop_nonneg_capacity s HC) as H2.
    pose proof(capacity_two_bits s HA H2); lia.
Qed.
Lemma strict_tfold w s : Adm s ->Good s ->Strict s ->
  (0<=rrun w (Z.of_N(cap s)))%Z ->Strict(tfold s w).
Proof.
  revert s; induction w as [|b w IH]; intros s HA HG HS HC; [exact HS|].
  pose proof(rrun_nonneg_head b w (Z.of_N(cap s)) HC) as H1.
  destruct(tstep_props s b HA HG H1) as [HA1 [HG1 [EC _]]].
  apply IH; [exact HA1|exact HG1|now apply strict_tstep|rewrite EC; exact HC].
Qed.
Lemma strict_reset_empty w : (0<=rrun w 0)%Z ->Strict(tfold [] w).
Proof. intro H; exact(strict_tfold w [] I I I H). Qed.

Inductive Ready : list tok ->Prop :=
| ready_nil : Ready []
| ready_Z : forall s, Ready(Z::s)
| ready_X : forall s, Ready s ->Ready(X::s)
| ready_W : forall s, (2<=cap s)%N ->Ready(cdec(cdec s)) ->Ready(W::s).
Lemma ready_of_X s : Ready(X::s) ->Ready s.
Proof. intro H; inversion H; assumption. Qed.

Record ReadyCP s : Prop := {
  readycp_safe : SafeCP s;
  readycp_ready : Ready s;
  readycp_strict : Strict s
}.
Lemma ready_seedCP : ReadyCP seed.
Proof.
  constructor; [exact seed_safe|unfold seed; repeat constructor|].
  unfold seed; repeat split; cbn[nbit nsh]; lia.
Qed.

Definition RReturns b4 c :=
  (exists s, ReadyCP s /\ c -[family b4]->* cp s) \/ ~halts(family b4)c.
Lemma rreturns_trans b4 c c' : c -[family b4]->* c' ->RReturns b4 c' ->RReturns b4 c.
Proof.
  intros HR [[s [HS HT]]|HN].
  - left; exists s; split; [exact HS|eapply evstep_trans; eauto].
  - right; eapply multistep_nonhalt; eauto.
Qed.
Lemma rreturns_cp b4 s : ReadyCP s ->RReturns b4(cp s).
Proof. intro H; left; exists s; split; [exact H|apply evstep_refl]. Qed.

End BB25FamilyReady.

(* BB25FamilyExact.v *)
Close Scope Z_scope. Close Scope N_scope.
From BusyCoq Require Import Individual25.
Open Scope sym_scope.
From Coq Require Import List NArith ZArith Lia Arith.Wf_nat.
Import ListNotations BB25FamilyRules
  BB25FamilyCore BB25FamilyWord
  BB25FamilyStack BB25FamilyReset
  BB25FamilyMachine BB25FamilyDrain
  BB25FamilyBounds BB25FamilyReturn.

Module BB25FamilyExact.
Open Scope N_scope.
Notation npow := BB25FamilyCore.pow2.

(** Binary debts are only iterated abstractly in these lemmas, never expanded
    into an enormous unary counter.  The existing cdec saturates at zero. *)
Definition dpow (n:N) (s:list tok) := N.iter n cdec s.
Lemma dpow_zero s : dpow 0 s=s. Proof. reflexivity. Qed.
Lemma dpow_succ n s : dpow(N.succ n)s=cdec(dpow n s).
Proof. apply N.iter_succ. Qed.
Lemma dpow_succ_r n s : dpow(N.succ n)s=dpow n(cdec s).
Proof. apply N.iter_succ_r. Qed.
Lemma dpow_add n m s : dpow(n+m)s=dpow n(dpow m s).
Proof. apply N.iter_add. Qed.
Lemma dpow_cap n s : n<=cap s -> cap(dpow n s)=cap s-n.
Proof.
  induction n using N.peano_ind; intro H; [now rewrite dpow_zero,N.sub_0_r|].
  rewrite dpow_succ.
  assert (E:cap(dpow n s)=cap s-n) by (apply IHn; lia).
  rewrite cdec_capacity by (rewrite E; lia).
  rewrite E; lia.
Qed.
Lemma dpow_adm n s : Adm s -> Adm(dpow n s).
Proof. induction n using N.peano_ind; intro H; [exact H|rewrite dpow_succ; auto using cdec_adm]. Qed.
Lemma dpow_good n s : Good s -> Good(dpow n s).
Proof. induction n using N.peano_ind; intro H; [exact H|rewrite dpow_succ; auto using cdec_good]. Qed.
Lemma dpow_pdec n s : pdec(dpow n s)=pdec s.
Proof. induction n using N.peano_ind; [reflexivity|now rewrite dpow_succ,cdec_pdec]. Qed.
Lemma dpow_bval n s : bval(dpow n s)=bval s.
Proof. unfold bval; now rewrite dpow_pdec. Qed.
Lemma dpow_counts n s : nbit(dpow n s)=nbit s /\ nsh(dpow n s)=nsh s.
Proof.
  induction n using N.peano_ind; [split; reflexivity|].
  rewrite dpow_succ; destruct(cdec_counts(dpow n s)); destruct IHn; split; congruence.
Qed.

Lemma dpow_Z_even n s : n<=cap s -> dpow(2*n)(Z::s)=Z::dpow n s.
Proof.
  induction n using N.peano_ind; intro H; [reflexivity|].
  replace (2*N.succ n) with (N.succ(N.succ(2*n))) by lia.
  rewrite !dpow_succ,IHn by lia.
  rewrite cdec_Z,cdec_X by (rewrite dpow_cap by lia; lia).
  reflexivity.
Qed.
Lemma dpow_Z_odd n s : n<=cap s -> dpow(2*n+1)(Z::s)=X::dpow n s.
Proof.
  intro H; replace (2*n+1) with (N.succ(2*n)) by lia.
  now rewrite dpow_succ,dpow_Z_even,cdec_Z.
Qed.
Lemma dpow_X_even n s : n<=cap s -> dpow(2*n)(X::s)=X::dpow n s.
Proof.
  induction n using N.peano_ind; intro H; [reflexivity|].
  replace (2*N.succ n) with (N.succ(N.succ(2*n))) by lia.
  rewrite !dpow_succ,IHn by lia.
  rewrite cdec_X by (rewrite dpow_cap by lia; lia).
  now rewrite cdec_Z.
Qed.
Lemma dpow_X_odd n s : n+1<=cap s -> dpow(2*n+1)(X::s)=Z::dpow(n+1)s.
Proof.
  intro H; replace (2*n+1) with (N.succ(2*n)) by lia.
  rewrite dpow_succ,dpow_X_even by lia.
  rewrite cdec_X by (rewrite dpow_cap by lia; lia).
  replace (n+1) with (N.succ n) by lia; now rewrite dpow_succ.
Qed.
Lemma dpow_W n s : 2*n<=cap s -> dpow n(W::s)=W::dpow(2*n)s.
Proof.
  induction n using N.peano_ind; intro H; [reflexivity|].
  rewrite dpow_succ,IHn by lia.
  rewrite cdec_W by (rewrite dpow_cap by lia; lia).
  replace (2*N.succ n) with (N.succ(N.succ(2*n))) by lia.
  now rewrite !dpow_succ.
Qed.

(** Low binary digits, omitting the leading one; D is the source's RB.X. *)
Fixpoint pchi (p:positive) : list digit := match p with
  xH=>[] | xO p=>D::pchi p | xI p=>V::pchi p end.
Definition chi (n:N) := match n with 0=>[] | Npos p=>pchi p end.
Lemma chi_small n : n<2 -> chi n=[].
Proof. destruct n as [|p]; [reflexivity|destruct p; cbn; intros; try lia; reflexivity]. Qed.
Lemma chi_step n : 2<=n -> chi n=(if N.odd n then V else D)::chi(n/2).
Proof.
  destruct n as [|p]; [lia|]; destruct p; intro H; try lia;
    rewrite <-N.div2_div; reflexivity.
Qed.
Lemma chi_double n : 0<n -> chi(2*n)=D::chi n.
Proof.
  destruct n as [|p]; [lia|reflexivity].
Qed.
Lemma chi_two_pow k n : 0<n -> chi(npow k*n)=repeat D k++chi n.
Proof.
  intro H; induction k.
  - change (chi(1*n)=chi n); now rewrite N.mul_1_l.
  - change (chi(2*npow k*n)=D::(repeat D k++chi n)).
    rewrite <-N.mul_assoc,chi_double by (pose proof(BB25FamilyCore.pow2_pos k); nia).
    now rewrite IHk.
Qed.

End BB25FamilyExact.

(* BB25FamilyExactRun.v *)
Close Scope Z_scope. Close Scope N_scope.
From BusyCoq Require Import Individual25.
Open Scope sym_scope.
From Coq Require Import List NArith ZArith Lia Arith.Wf_nat.
Import ListNotations BB25FamilyRules
  BB25FamilyCore BB25FamilyWord
  BB25FamilyStack BB25FamilyReset
  BB25FamilyMachine BB25FamilyDrain
  BB25FamilyBounds BB25FamilyReturn
  BB25FamilyExact.

Module BB25FamilyExactRun.
Open Scope N_scope.
Notation npow := BB25FamilyCore.pow2.
Definition drain_word s := pdec s++chi(cap s+1)++[V].
Definition tail_word s (n:nat) :=
  pdec s++repeat Y n++[V]++chi(npow(n-1)*(cap s+1))++[V].

Lemma drain_word_zero s : cap s=0 -> drain_word s=pdec s++[V].
Proof. intro H; unfold drain_word; now rewrite H. Qed.
Lemma drain_word_round s : 0<cap s -> drain_word(W::cdec s)=drain_word s.
Proof.
  intro HC.
  assert (EC:cap(W::cdec s)+1=(cap s+1)/2).
  { change (cap(cdec s)/2+1=(cap s+1)/2).
    rewrite cdec_capacity by exact HC.
    pose proof(N.div_mod (cap s-1) 2 ltac:(discriminate)).
    pose proof(N.mod_lt (cap s-1) 2 ltac:(discriminate)).
    pose proof(N.div_mod (cap s+1) 2 ltac:(discriminate)).
    pose proof(N.mod_lt (cap s+1) 2 ltac:(discriminate)); lia. }
  assert (EO:N.odd(cap s-1)=N.odd(cap s+1)).
  { replace (cap s+1) with ((cap s-1)+2) by lia.
    rewrite N.odd_add; cbn; now rewrite Bool.xorb_false_r. }
  unfold drain_word; rewrite EC; cbn [pdec].
  rewrite cdec_pdec,cdec_capacity by exact HC.
  rewrite EO,(chi_step (cap s+1) ltac:(lia)); now rewrite <-app_assoc.
Qed.

Section Runs.
Variable b4 : control.
Notation tm := (family b4).
Notation "c -->* c'" := (c -[tm]->* c') (at level 40).
Notation "c -->+ c'" := (c -[tm]->+ c') (at level 40).

Lemma exact_zero s : cap s=0 -> (1<=bval s)%Z ->
  (0<=rrun(pdec s++[V])0)%Z /\ SafeCP(tfold [](pdec s++[V])) /\
  left s root {{A}}>0inf -->+ cp(tfold [](pdec s++[V])).
Proof.
  intros HC HB; set(w:=pdec s++[V]).
  assert (HW:rrun w 0=(2*bval s)%Z) by (unfold w; rewrite rrun_app; reflexivity).
  assert (HCw:(0<=rrun w 0)%Z) by (rewrite HW; lia).
  destruct(tfold_empty_props w HCw) as [HA [HG [EC HR]]].
  split; [exact HCw|split].
  - repeat split; try assumption.
    + rewrite HW in EC; lia.
    + exists(tfold [](pdec s)); unfold w; rewrite tfold_app; reflexivity.
  - eapply progress_trans; [apply right_blank|].
    eapply progress_trans; [apply overflow_root_run; exact HC|].
    rewrite out_pdec.
    assert (EW:cells w *>0inf=cells(pdec s) *>[S2;S1] *>0inf).
    { unfold w; rewrite cells_app,Str_app_assoc; reflexivity. }
    rewrite <-EW.
    eapply evstep_progress_trans; [apply (reset_run b4 w []); exact HCw|].
    apply right_two_blank.
Qed.

Theorem exact_drain s : Strong s ->
  (0<=rrun(drain_word s)0)%Z /\ SafeCP(tfold [](drain_word s)) /\
  left s root {{A}}>0inf -->+ cp(tfold [](drain_word s)).
Proof.
  induction s as [s IH] using
    (well_founded_induction (well_founded_ltof _ (fun s=>N.to_nat(cap s)))).
  intro HS; destruct(N.eq_dec (cap s) 0) as [HC|HC].
  - rewrite drain_word_zero by exact HC; apply exact_zero; [exact HC|now apply strong_zero].
  - assert (HP:0<cap s) by lia.
    destruct(strong_round s HS HP) as [HS' Hlt].
    destruct(IH (W::cdec s) ltac:(unfold ltof; lia) HS') as [HW [HT HR]].
    rewrite drain_word_round in HW,HT,HR by exact HP.
    split; [exact HW|split; [exact HT|]].
    eapply progress_trans; [apply right_blank|].
    eapply progress_trans; [apply cdec_run; exact HP|].
    eapply progress_trans; [apply right_V|exact HR].
Qed.

Lemma pending_word s n : (1<=n)%nat -> drain_word(W::pushZ n s)=tail_word s n.
Proof.
  intro Hn.
  assert (HO:N.odd(cap(pushZ n s))=true) by (apply pushZ_odd; left; exact Hn).
  assert (EC:cap(W::pushZ n s)+1=npow(n-1)*(cap s+1)).
  { destruct n as [|n]; [lia|].
    replace (S n-1)%nat with n by lia.
    change (cap(pushZ(S n)s)/2+1=npow n*(cap s+1)).
    rewrite pushZ_succ; cbn [cap].
    pose proof(N.div_mod (2*cap(pushZ n s)+1) 2 ltac:(discriminate)).
    pose proof(N.mod_lt (2*cap(pushZ n s)+1) 2 ltac:(discriminate)).
    pose proof(pushZ_capacity n s); lia. }
  unfold drain_word,tail_word; rewrite EC; cbn [pdec].
  rewrite HO,pushZ_pdec; now rewrite <-!app_assoc.
Qed.

Theorem exact_tail s n : Adm s ->
  (3*(Z.of_N(cap s)+1)<=4*(bval s+1))%Z -> (1<=n)%nat ->
  (0<=rrun(tail_word s n)0)%Z /\ SafeCP(tfold [](tail_word s n)) /\
  left s root {{A}}> S2 >>cells(repeat Y n) *>S1 >>0inf -->+
    cp(tfold [](tail_word s n)).
Proof.
  intros HA HB Hn.
  destruct(exact_drain (W::pushZ n s)
    (strong_pending n s HA HB (or_introl Hn))) as [HW [HT HR]].
  rewrite pending_word in HW,HT,HR by exact Hn.
  split; [exact HW|split; [exact HT|]].
  eapply evstep_progress_trans; [apply P2_Yrun|].
  eapply progress_trans; [apply right_V|exact HR].
Qed.

End Runs.
End BB25FamilyExactRun.

(* BB25FamilyLA.v *)
Close Scope Z_scope. Close Scope N_scope.
From BusyCoq Require Import Individual25.
Open Scope sym_scope.
From Coq Require Import List NArith ZArith Lia.
Import ListNotations BB25FamilyRules
  BB25FamilyCore BB25FamilyWord
  BB25FamilyStack BB25FamilyReset
  BB25FamilyMachine BB25FamilyDrain
  BB25FamilyBounds BB25FamilyReturn
  BB25FamilyCases BB25FamilyClosure
  BB25FamilySeed BB25FamilyReady.

Module BB25FamilyLA.
Open Scope Z_scope.
Definition ReadyTail b4 := forall s n, Adm s ->Good s ->(2<=n)%nat ->
  RReturns b4 (left s root {{A}}> S2>>cells(repeat Y n)*>S1>>0inf).

Section Control.
Variable b4 : control.
Hypothesis tail_ready : ReadyTail b4.

Lemma rreturns_Yrun s n : Adm s ->Good s ->Strict s ->(2<=n)%nat ->
  RReturns b4 (left s root {{A}}> cells(repeat Y n)*>S1>>0inf).
Proof.
  intros HA HG HS Hn; destruct n as [|[|n]]; [lia|lia|].
  pose proof(pushZ_checkpoint (S(S n)) s HA HG ltac:(lia) ltac:(left;lia))
    as [HA' [HG' [HC' HX']]].
  assert (HP:(0<cap(pushZ(S(S n))s))%N).
  { rewrite !pushZ_succ; cbn[cap]; lia. }
  eapply rreturns_trans; [apply Yrun|].
  eapply rreturns_trans; [apply progress_evstep; apply right_one|].
  eapply rreturns_trans; [apply progress_evstep; apply cdec_run; exact HP|].
  eapply rreturns_trans; [apply progress_evstep; apply right_two_blank|].
  apply rreturns_cp; constructor.
  - split; [exact HA'|split; [exact HG'|split; assumption]].
  - rewrite !pushZ_succ,cdec_Z; apply ready_X,ready_Z.
  - apply strict_cdec,strict_pushZ; assumption.
Qed.

Lemma rreturns_reset_P2 w n : 0<=rrun w 0 ->(1<=n)%nat ->
  RReturns b4 (root {{A}}> S2>>cells w*>S2>>cells(repeat Y n)*>S1>>0inf).
Proof.
  intros HR Hn.
  destruct(tfold_empty_props w HR) as [HA [HG _]].
  eapply rreturns_trans; [apply reset_zero_run; exact HR|].
  change (RReturns b4 (left(tfold [] w) root {{A}}>
    cells(repeat Y(S n))*>S1>>0inf)).
  apply rreturns_Yrun; auto using strict_reset_empty; lia.
Qed.
Lemma rreturns_reset_Yrun w n : 0<=rrun w 0 ->(2<=n)%nat ->
  RReturns b4 (root {{A}}> S2>>cells w*>cells(repeat Y n)*>S1>>0inf).
Proof.
  intros HR Hn; destruct(tfold_empty_props w HR) as [HA [HG _]].
  eapply rreturns_trans; [apply reset_zero_run; exact HR|].
  apply tail_ready; assumption.
Qed.

Lemma rreturns_overflow s b n : Adm s ->0<=bval s ->cap s=0%N ->(2<=n)%nat ->
  RReturns b4 (left s root <{{A}} dc b*>S2>>cells(repeat Y n)*>S1>>0inf).
Proof.
  intros HA HB HC Hn.
  destruct(Z_le_dec 0 (rstep b (bval s))) as [HR|HR].
  - eapply rreturns_trans; [apply progress_evstep; apply overflow_root_run; exact HC|].
    rewrite out_pdec,<-cells_snoc; apply rreturns_reset_P2; [rewrite rrun_app; exact HR|lia].
  - assert (EB:b=D) by (destruct b; cbn[rstep] in HR; try lia; reflexivity).
    subst b; assert (HB':bval s<=1).
    { cbn[rstep] in HR; pose proof(div2_bounds(bval s)); lia. }
    destruct(pdec s) as [|x xs] eqn:HE.
    + destruct n; [lia|].
      eapply rreturns_trans; [apply overflow_run; exact HC|].
      rewrite out_pdec,HE; right; unfold root; apply xy_spinout_nonhalt.
    + assert (Hne:pdec s<>[]) by (rewrite HE; discriminate).
      destruct(overflow_retry s HA HC ltac:(lia) Hne) as [HA' [HG' [HC' HB'']]].
      eapply rreturns_trans; [apply progress_evstep; apply overflow_root_run; exact HC|].
      rewrite out_pdec.
      eapply rreturns_trans; [apply reset_zero_run; exact HB|].
      eapply rreturns_trans; [apply progress_evstep; apply right_V|].
      eapply rreturns_trans; [apply progress_evstep; apply right_one|].
      eapply rreturns_trans;
        [apply progress_evstep; apply (overflow_root_run b4 (W::tfold [] (pdec s))); exact HC'|].
      rewrite out_pdec.
      change (RReturns b4 (root {{A}}> S2>>cells(pdec(W::tfold [] (pdec s)))*>
        cells(repeat Y(S n))*>S1>>0inf)).
      apply rreturns_reset_Yrun; [exact HB''|lia].
Qed.

Theorem zready s n : Adm s ->Good s ->(2<=n)%nat ->
  RReturns b4 (left s root <{{A}} dc D*>S2>>cells(repeat Y n)*>S1>>0inf).
Proof.
  intros HA HG Hn; destruct(N.eq_dec (cap s) 0) as [HC|HC].
  - apply rreturns_overflow; auto using good_bval_nonneg.
  - assert (HP:(0<cap s)%N) by lia.
    eapply rreturns_trans; [apply progress_evstep; apply cdec_run; exact HP|].
    eapply rreturns_trans; [apply progress_evstep; apply right_one|].
    destruct(N.eq_dec (cap(cdec s)) 0) as [HC'|HC'].
    + apply (rreturns_overflow (cdec s) V n); auto using cdec_adm,cdec_good,good_bval_nonneg.
    + assert (HP':(0<cap(cdec s))%N) by lia.
      assert (H2:(2<=cap s)%N) by (rewrite cdec_capacity in HP' by exact HP; lia).
      eapply rreturns_trans; [apply progress_evstep; apply cdec_run; exact HP'|].
      eapply rreturns_trans; [apply progress_evstep; apply right_V|].
      apply (tail_ready (W::cdec(cdec s)) n).
      * rewrite <-cdec_W by exact H2; apply cdec_adm,adm_W; [exact HA|].
        pose proof(capacity_two_bits s HA H2); lia.
      * rewrite <-cdec_W by exact H2; now apply good_paid_W.
      * exact Hn.
Qed.
End Control.

Section Closure.
Let b4 := Some(S1,L,A).
Hypothesis tail_ready : ReadyTail b4.
Notation tm := (family b4).

Lemma ready_sweep s : Ready s ->forall n, (2<=n)%nat ->Adm s ->Good s ->
  RReturns b4 (sweep s n).
Proof.
  intro HR; induction HR as [|s|s HR IH|s HC HR IH]; intros n Hn HA HG.
  - right; apply leftend_B1_nonhalt.
  - unfold sweep; rewrite left_cons; cbn[tc].
    eapply rreturns_trans; [apply progress_evstep; apply B1_Z|].
    apply zready; [exact tail_ready|exact(proj1 HA)|exact(proj1 HG)|exact Hn].
  - unfold sweep; rewrite left_cons; cbn[tc].
    eapply rreturns_trans; [apply progress_evstep; apply B1_X|].
    change (RReturns b4 (sweep s (S n))); apply IH; [lia|exact(proj1 HA)|exact(proj1 HG)].
  - unfold sweep; rewrite left_cons; cbn[tc].
    eapply rreturns_trans; [apply progress_evstep; apply B1_W|].
    eapply rreturns_trans; [apply progress_evstep; apply case_two_decrements; exact HC|].
    eapply rreturns_trans; [apply progress_evstep; apply G_1LA|].
    change (RReturns b4 (sweep(cdec(cdec s))(S n))).
    apply IH; [lia|apply cdec_adm,cdec_adm; exact(proj1 HA)|apply cdec_good,cdec_good; exact(proj1 HG)].
Qed.

Lemma ready_cp_progress s : ReadyCP s ->
  (exists t, cp s -[tm]->+ cp t /\ ReadyCP t) \/ ~halts tm (cp s).
Proof.
  intros [HS HR HSt]; destruct HS as [HA [HG [HC [t ->]]]].
  assert (Hrun:cp(X::t) -[tm]->+ sweep t 2).
  { unfold cp,sweep; rewrite left_cons; cbn[tc cells flat_map repeat dc]; apply B1_X. }
  assert (HT:RReturns b4 (sweep t 2)).
  { apply ready_sweep; [now apply ready_of_X|lia|exact(proj1 HA)|exact(proj1 HG)]. }
  destruct HT as [[s [HS HT]]|HN].
  - left; exists s; split; [eapply progress_evstep_trans; eassumption|exact HS].
  - right; eapply multistep_nonhalt; [apply progress_evstep; exact Hrun|exact HN].
Qed.
Lemma ready_nonhalt s : ReadyCP s ->~halts tm (cp s).
Proof.
  intro HS; apply(progress_nonhalt_or tm (fun c=>exists s,ReadyCP s /\ c=cp s)).
  - intros c [t [HT ->]]; destruct(ready_cp_progress t HT) as [[u [HR HU]]|HN].
    + left; exists(cp u); split; [exact HR|exists u; split; [exact HU|reflexivity]].
    + right; exact HN.
  - exists s; split; [exact HS|reflexivity].
Qed.
Theorem nonhalt_of_tail : ~halts tm c0.
Proof. eapply multistep_nonhalt; [apply seed_run|apply ready_nonhalt,ready_seedCP]. Qed.
End Closure.
End BB25FamilyLA.

(* BB25FamilyLADebt.v *)
Close Scope Z_scope. Close Scope N_scope.
From Coq Require Import List NArith ZArith Lia.
Import ListNotations BB25FamilyCore BB25FamilyWord
  BB25FamilyStack BB25FamilyReset
  BB25FamilyReady BB25FamilyExact.

Module BB25FamilyLADebt.
Open Scope N_scope.
Definition TW w := tfold [] w.
Lemma TW_nil : TW []=[]. Proof. reflexivity. Qed.
Lemma TW_Y u : TW(u++[Y])=Z::TW u.
Proof. unfold TW; rewrite tfold_app; reflexivity. Qed.
Lemma TW_V u : TW(u++[V])=X::TW u.
Proof. unfold TW; rewrite tfold_app; reflexivity. Qed.
Lemma TW_D u : 2<=cap(TW u) ->TW(u++[D])=W::dpow 2 (TW u).
Proof. intro H; unfold TW at 1; rewrite tfold_app; cbn[tfold tstep]; rewrite cdec_W by exact H; reflexivity. Qed.
Lemma TW_Y_cap u : cap(TW(u++[Y]))=2*cap(TW u)+1.
Proof. rewrite TW_Y; reflexivity. Qed.
Lemma TW_V_cap u : cap(TW(u++[V]))=2*cap(TW u).
Proof. rewrite TW_V; reflexivity. Qed.
Lemma TW_D_cap u : 2<=cap(TW u) ->cap(TW(u++[D]))=(cap(TW u)-2)/2.
Proof. intro H; rewrite TW_D by exact H; cbn[cap]; now rewrite dpow_cap. Qed.
Lemma TW_pdec_cap s : Good s ->(Z.of_N(cap(TW(pdec s)))=bval s)%Z.
Proof.
  intro HG; pose proof(good_bval_nonneg s HG) as HB.
  exact(proj1(proj2(proj2(tfold_empty_props (pdec s) HB)))).
Qed.
Lemma dpow_strict n s : Strict s ->Strict(dpow n s).
Proof. induction n using N.peano_ind; intro H; [exact H|rewrite dpow_succ; auto using strict_cdec]. Qed.

Lemma ready_Y_even u n : n<=cap(TW(u++[Y])) ->n mod 2=0 ->Ready(dpow n(TW(u++[Y]))).
Proof.
  intros HC HP; rewrite TW_Y_cap in HC; rewrite TW_Y.
  pose proof(N.div_mod n 2 ltac:(discriminate)) as HE.
  assert (EN:n=2*(n/2)) by lia; rewrite EN,dpow_Z_even by lia; apply ready_Z.
Qed.
Lemma ready_Y_odd u n : n<=cap(TW(u++[Y])) ->n mod 2=1 ->
  Ready(dpow(n/2)(TW u)) ->Ready(dpow n(TW(u++[Y]))).
Proof.
  intros HC HP HR; rewrite TW_Y_cap in HC; rewrite TW_Y.
  pose proof(N.div_mod n 2 ltac:(discriminate)) as HE.
  assert (EN:n=2*(n/2)+1) by lia; rewrite EN,dpow_Z_odd by lia; now apply ready_X.
Qed.
Lemma ready_V_odd u n : n<=cap(TW(u++[V])) ->n mod 2=1 ->Ready(dpow n(TW(u++[V]))).
Proof.
  intros HC HP; rewrite TW_V_cap in HC; rewrite TW_V.
  pose proof(N.div_mod n 2 ltac:(discriminate)) as HE.
  assert (EN:n=2*(n/2)+1) by lia; rewrite EN,dpow_X_odd by lia; apply ready_Z.
Qed.
Lemma ready_V_even u n : n<=cap(TW(u++[V])) ->n mod 2=0 ->
  Ready(dpow(n/2)(TW u)) ->Ready(dpow n(TW(u++[V]))).
Proof.
  intros HC HP HR; rewrite TW_V_cap in HC; rewrite TW_V.
  pose proof(N.div_mod n 2 ltac:(discriminate)) as HE.
  assert (EN:n=2*(n/2)) by lia; rewrite EN,dpow_X_even by lia; now apply ready_X.
Qed.
Lemma ready_D u n : 2*n+4<=cap(TW u) ->Ready(dpow(2*n+4)(TW u)) ->
  Ready(dpow n(TW(u++[D]))).
Proof.
  intros HC HR; rewrite TW_D by lia.
  rewrite dpow_W by (rewrite dpow_cap by lia; lia).
  rewrite <-dpow_add; apply ready_W.
  - rewrite dpow_cap by lia; lia.
  - replace (2*n+4) with (N.succ(N.succ(2*n+2))) in HR by lia.
    now rewrite !dpow_succ in HR.
Qed.

Definition Credit s n := 2*n+2<=cap s \/
  (n mod 2=0 /\ n+4<=2*cap s /\ (Z.of_N n+2<=bval s)%Z).

Lemma credit_debt s n : Good s ->Credit s n ->(Z.of_N n<=bval s)%Z.
Proof. intros HG [HC|[_ [_ HC]]]; pose proof(good_bound s HG); lia. Qed.
Lemma odd_Nmod a : N.odd a=(a mod 2 =? 1).
Proof. rewrite <-N.bit0_odd,N.bit0_eqb; reflexivity. Qed.

Theorem dual_credit s : forall n, Good s ->Credit s n ->Ready(dpow n(TW(pdec s))).
Proof.
  induction s as [|b s IH]; intros n HG HCr.
  - destruct HCr as [H|[_ [H _]]]; cbn[cap] in H; lia.
  - pose proof(credit_debt (b::s) n HG HCr) as Hdebt.
    pose proof(TW_pdec_cap (b::s) HG) as Hcv.
    assert (Hlim:n<=cap(TW(pdec(b::s)))) by lia.
    pose proof(proj1 HG) as HGs.
    pose proof(N.div_mod n 2 ltac:(discriminate)) as Hdiv.
    pose proof(N.mod_lt n 2 ltac:(discriminate)) as Hmod.
    destruct b.
    + change (Ready(dpow n(TW(pdec s++[Y])))).
      destruct(N.eq_dec (n mod 2) 0) as [HP|HP].
      * apply ready_Y_even; assumption.
      * apply ready_Y_odd; [exact Hlim|lia|].
        apply IH; [exact HGs|left].
        destruct HCr as [HC|[HE _]]; [cbn[cap] in HC; lia|contradiction].
    + change (Ready(dpow n(TW(pdec s++[Y])))).
      destruct(N.eq_dec (n mod 2) 0) as [HP|HP].
      * apply ready_Y_even; assumption.
      * apply ready_Y_odd; [exact Hlim|lia|].
        apply IH; [exact HGs|left].
        destruct HCr as [HC|[HE _]]; [cbn[cap] in HC; lia|contradiction].
    + change (Ready(dpow n(TW(pdec s++[if N.odd(cap s) then V else D])))).
      destruct(N.odd(cap s)) eqn:HO.
      * destruct(N.eq_dec (n mod 2) 1) as [HP|HP].
        -- apply ready_V_odd; [cbn[pdec] in Hlim; now rewrite HO in Hlim|exact HP].
        -- apply ready_V_even; [cbn[pdec] in Hlim; now rewrite HO in Hlim|lia|].
           apply IH; [exact HGs|left].
           destruct HCr as [HC|[_ [HC _]]]; cbn[cap] in HC;
             pose proof(N.div_mod (cap s) 2 ltac:(discriminate)); lia.
      * rewrite odd_Nmod in HO; apply N.eqb_neq in HO.
        assert (Hpar:cap s mod 2=0) by (pose proof(N.mod_lt (cap s) 2 ltac:(discriminate)); lia).
        assert (Hcap:cap s=2*cap(W::s)).
        { cbn[cap]; pose proof(N.div_mod (cap s) 2 ltac:(discriminate)); lia. }
        assert (Hbv:(2*bval(W::s)+2<=bval s)%Z).
        { assert (HOf:N.odd(cap s)=false) by (rewrite odd_Nmod; now apply N.eqb_neq).
          rewrite bval_W,HOf; pose proof(div2_bounds(bval s)); lia. }
        pose proof(good_bound (W::s) HG) as Hgood.
        pose proof(TW_pdec_cap s HGs) as Hpay.
        assert (Hbudget:2*n+4<=cap(TW(pdec s))).
        { destruct HCr as [HC|[_ [_ HC]]]; lia. }
        apply ready_D; [exact Hbudget|apply IH; [exact HGs|right]].
        split; [rewrite N.add_mod,N.mul_mod by discriminate; reflexivity|split].
        -- destruct HCr as [HC|[_ [HC _]]]; lia.
        -- destruct HCr as [HC|[_ [_ HC]]]; lia.
Qed.

Corollary ready_dpow_of_cap s n : Good s ->2*n+2<=cap s ->Ready(dpow n(TW(pdec s))).
Proof. intros HG HC; apply dual_credit; [exact HG|now left]. Qed.

End BB25FamilyLADebt.

(* BB25FamilyLAChi.v *)
Close Scope Z_scope. Close Scope N_scope.
From Coq Require Import List NArith ZArith Lia Arith.Wf_nat.
Import ListNotations BB25FamilyCore BB25FamilyWord
  BB25FamilyStack BB25FamilyReset
  BB25FamilyReady BB25FamilyExact
  BB25FamilyLADebt.

Module BB25FamilyLAChi.
Open Scope N_scope.
Notation npow := BB25FamilyCore.pow2.

Lemma TW_Yrun_cap k pre : cap(TW(pre++repeat Y k))+1=npow k*(cap(TW pre)+1).
Proof.
  induction k; [cbn[repeat]; rewrite app_nil_r; change (cap(TW pre)+1=1*(cap(TW pre)+1)); lia|].
  change (cap(TW(pre++Y::repeat Y k))+1=2*npow k*(cap(TW pre)+1)).
  rewrite (repeat_cons k Y),app_assoc,TW_Y_cap; lia.
Qed.
Lemma TW_Drun_cap k : forall q pre, 2<=q ->cap(TW pre)+2=npow k*q ->
  cap(TW(pre++repeat D k))+2=q.
Proof.
  induction k as [|k IH]; intros q pre HQ HC.
  - cbn[repeat]; rewrite app_nil_r; change (cap(TW pre)+2=1*q) in HC; lia.
  - pose proof(BB25FamilyCore.pow2_pos k) as HP.
    change (cap(TW pre)+2=2*npow k*q) in HC.
    assert (H2:2<=cap(TW pre)) by nia.
    replace (pre++repeat D(S k)) with ((pre++[D])++repeat D k)
      by (rewrite <-app_assoc; reflexivity).
    apply IH; [exact HQ|rewrite TW_D_cap by exact H2; div2].
Qed.
Lemma ready_Drun k : forall n pre, npow k*(n+4)<=cap(TW pre)+4 ->
  Ready(dpow(npow k*(n+4)-4)(TW pre)) ->Ready(dpow n(TW(pre++repeat D k))).
Proof.
  induction k as [|k IH]; intros n pre HC HR.
  - cbn[repeat]; rewrite app_nil_r.
    change (Ready(dpow(1*(n+4)-4)(TW pre))) in HR.
    replace (1*(n+4)-4) with n in HR by lia; exact HR.
  - pose proof(BB25FamilyCore.pow2_pos k) as HP.
    change (2*npow k*(n+4)<=cap(TW pre)+4) in HC.
    change (Ready(dpow(2*npow k*(n+4)-4)(TW pre))) in HR.
    assert (Hbig:4<=npow k*(n+4)) by nia.
    assert (H2:2<=cap(TW pre)) by nia.
    replace (pre++repeat D(S k)) with ((pre++[D])++repeat D k)
      by (rewrite <-app_assoc; reflexivity).
    apply IH.
    + rewrite TW_D_cap by exact H2; div2.
    + apply ready_D; [nia|].
      replace (2*(npow k*(n+4)-4)+4) with (2*npow k*(n+4)-4) by nia; exact HR.
Qed.

Lemma ready_chi m : 1<=m ->forall pre, 4*m<=cap(TW pre)+2 ->
  (forall n, n+4<=4*m ->(n mod 2=1 ->n+9<=2*m) ->Ready(dpow n(TW pre))) ->
  Ready(TW(pre++chi m)).
Proof.
  induction m as [m IH] using
    (well_founded_induction (well_founded_ltof _ N.to_nat)).
  intros HM pre HC HR; destruct(N.lt_ge_cases m 2) as [Hlt|Hge].
  - assert (HE:m=1) by lia; rewrite chi_small by exact Hlt; rewrite app_nil_r.
    apply (HR 0); [lia|discriminate].
  - pose proof(N.div_mod m 2 ltac:(discriminate)) as Hdiv.
    pose proof(N.mod_lt m 2 ltac:(discriminate)) as Hmod.
    assert (HM':1<=m/2) by lia.
    assert (Hlt':(N.to_nat(m/2)<N.to_nat m)%nat) by lia.
    rewrite chi_step by exact Hge; destruct(N.odd m) eqn:HO.
    + rewrite odd_Nmod in HO; apply N.eqb_eq in HO.
      replace (pre++V::chi(m/2)) with ((pre++[V])++chi(m/2))
        by (rewrite <-app_assoc; reflexivity).
      apply (IH (m/2) Hlt' HM').
      * rewrite TW_V_cap; lia.
      * intros n HN HNO.
        pose proof(N.div_mod n 2 ltac:(discriminate)) as Hndiv.
        pose proof(N.mod_lt n 2 ltac:(discriminate)) as Hnmod.
        destruct(N.eq_dec (n mod 2) 1) as [HP|HP].
        -- apply ready_V_odd; [rewrite TW_V_cap; lia|exact HP].
        -- apply ready_V_even; [rewrite TW_V_cap; lia|lia|].
           apply HR; [lia|intro HQ].
           pose proof(N.div_mod (n/2) 2 ltac:(discriminate)); lia.
    + rewrite odd_Nmod in HO; apply N.eqb_neq in HO.
      assert (HP:m mod 2=0) by lia.
      assert (H2:2<=cap(TW pre)) by lia.
      replace (pre++D::chi(m/2)) with ((pre++[D])++chi(m/2))
        by (rewrite <-app_assoc; reflexivity).
      apply (IH (m/2) Hlt' HM').
      * rewrite TW_D_cap by exact H2; div2.
      * intros n HN _; apply ready_D; [lia|].
        apply HR; [lia|].
        rewrite N.add_mod,N.mul_mod by discriminate; discriminate.
Qed.

End BB25FamilyLAChi.

(* BB25FamilyLADirect.v *)
Close Scope Z_scope. Close Scope N_scope.
From Coq Require Import List NArith ZArith Lia.
Import ListNotations BB25FamilyCore BB25FamilyWord
  BB25FamilyStack BB25FamilyReset
  BB25FamilyReady BB25FamilyExact
  BB25FamilyExactRun BB25FamilyLADebt
  BB25FamilyLAChi.

Module BB25FamilyLADirect.
Open Scope N_scope.
Notation npow := BB25FamilyCore.pow2.
Lemma ready_Yrun_even pre q n : n<=cap(TW(pre++repeat Y(S q))) ->n mod 2=0 ->
  Ready(dpow n(TW(pre++repeat Y(S q)))).
Proof.
  intros HC HP; change (Ready(dpow n(TW(pre++Y::repeat Y q)))).
  rewrite (repeat_cons q Y),app_assoc; apply ready_Y_even; [|exact HP].
  now rewrite <-app_assoc,<-repeat_cons.
Qed.

Theorem ready_drain_word s q : Good s ->(2<=q)%nat ->Ready(TW(tail_word s q)).
Proof.
  intros HG HQ; destruct q as [|[|k]]; [lia|lia|].
  set (m:=cap s+1); set (B:=cap(TW(pdec s))).
  assert (HM:1<=m) by (unfold m; lia).
  assert (HB:cap s<=B) by (unfold B; pose proof(TW_pdec_cap s HG); pose proof(good_bound s HG); lia).
  assert (HMB:m<=B+1) by (unfold m; lia).
  set (w1:=pdec s++repeat Y(S(S k))).
  set (w2:=w1++[V]).
  set (w3:=w2++repeat D(S k)).
  assert (EV1:cap(TW w1)+1=4*npow k*(B+1)).
  { pose proof(TW_Yrun_cap (S(S k)) (pdec s)); change (cap(TW w1)+1=2*(2*npow k)*(B+1)) in H; nia. }
  assert (EV2:cap(TW w2)=2*cap(TW w1)) by (unfold w2; apply TW_V_cap).
  assert (EQ2:cap(TW w2)+2=npow(S k)*(4*(B+1))).
  { change (cap(TW w2)+2=2*npow k*(4*(B+1))); nia. }
  assert (EV3:cap(TW w3)+2=4*(B+1)).
  { unfold w3; apply TW_Drun_cap; [lia|exact EQ2]. }
  unfold tail_word; replace (S(S k)-1)%nat with (S k) by lia.
  change (Ready(TW(pdec s++repeat Y(S(S k))++[V]++chi(npow(S k)*m)++[V]))).
  rewrite chi_two_pow by lia.
  replace (pdec s++repeat Y(S(S k))++[V]++(repeat D(S k)++chi m)++[V])
    with ((w3++chi m)++[V]) by (unfold w3,w2,w1; rewrite <-!app_assoc; reflexivity).
  rewrite TW_V; apply ready_X.
  apply ready_chi; [exact HM|lia|].
  intros n HN HO.
  unfold w3; apply ready_Drun.
  - change (2*npow k*(n+4)<=cap(TW w2)+4).
    pose proof(BB25FamilyCore.pow2_pos k); nia.
  - assert (HP:0<npow k) by apply BB25FamilyCore.pow2_pos.
    assert (Hbig:4<=npow k*(n+4)) by nia.
    assert (Hdebt:npow(S k)*(n+4)-4<=cap(TW w2)).
    { change (2*npow k*(n+4)-4<=cap(TW w2)); nia. }
    assert (Heven:(npow(S k)*(n+4)-4) mod 2=0).
    { change ((2*npow k*(n+4)-4) mod 2=0).
      replace (2*npow k*(n+4)-4) with (2*(npow k*(n+4)-2)) by nia.
      rewrite N.mul_mod by discriminate; reflexivity. }
    unfold w2; apply ready_V_even; [exact Hdebt|exact Heven|].
    assert (Ehalf:(npow(S k)*(n+4)-4)/2=npow k*(n+4)-2).
    { change ((2*npow k*(n+4)-4)/2=npow k*(n+4)-2); div2. }
    rewrite Ehalf.
    assert (Hbound:npow k*(n+4)-2<=cap(TW w1)) by nia.
    destruct k as [|k].
    + change (Ready(dpow(1*(n+4)-2)(TW w1))).
      replace (1*(n+4)-2) with (n+2) by lia.
      change (1*(n+4)-2<=cap(TW w1)) in Hbound.
      replace (1*(n+4)-2) with (n+2) in Hbound by lia.
      pose proof(N.div_mod n 2 ltac:(discriminate)) as Hdiv.
      pose proof(N.mod_lt n 2 ltac:(discriminate)) as Hmod.
      destruct(N.eq_dec (n mod 2) 0) as [Hpar|Hpar].
      * unfold w1; apply ready_Yrun_even; [exact Hbound|rewrite N.add_mod by discriminate; now rewrite Hpar].
      * assert (Hodd:n mod 2=1) by lia.
        specialize(HO Hodd).
        assert (Eword:w1=(pdec s++[Y])++[Y]) by (unfold w1; rewrite <-app_assoc; reflexivity).
        rewrite Eword; apply ready_Y_odd.
        -- now rewrite <-Eword.
        -- rewrite N.add_mod by discriminate; now rewrite Hodd.
        -- assert (Hbound':(n+2)/2<=cap(TW(pdec s++[Y]))).
           { rewrite TW_Y_cap; unfold m,B in *; pose proof(TW_pdec_cap s HG).
             pose proof(N.div_mod (n+2) 2 ltac:(discriminate)); lia. }
           pose proof(N.div_mod (n+2) 2 ltac:(discriminate)) as HD1.
           pose proof(N.mod_lt (n+2) 2 ltac:(discriminate)) as HM1.
           pose proof(N.div_mod ((n+2)/2) 2 ltac:(discriminate)) as HD2.
           pose proof(N.mod_lt ((n+2)/2) 2 ltac:(discriminate)) as HM2.
           destruct(N.eq_dec (((n+2)/2) mod 2) 0) as [HP2|HP2].
           ++ now apply ready_Y_even.
           ++ apply ready_Y_odd; [exact Hbound'|clear - HM2 HP2; lia|].
              apply ready_dpow_of_cap; [exact HG|].
              clear - HO HD1 HD2 HM1 HM2; unfold m in HO; lia.
    + unfold w1; apply ready_Yrun_even; [exact Hbound|].
      change ((2*npow k*(n+4)-2) mod 2=0).
      pose proof(BB25FamilyCore.pow2_pos k) as Hpow.
      replace (2*npow k*(n+4)-2) with (2*(npow k*(n+4)-1))
        by (clear - Hpow; nia).
      rewrite N.mul_mod by discriminate; reflexivity.
Qed.

End BB25FamilyLADirect.

(* BB25FamilyLAFinal.v *)
Close Scope Z_scope. Close Scope N_scope.
From BusyCoq Require Import Individual25.
Open Scope sym_scope.
From Coq Require Import List NArith ZArith Lia String.
Import ListNotations BB25FamilyRules
  BB25FamilyCore BB25FamilyWord
  BB25FamilyStack BB25FamilyReset
  BB25FamilyMachine BB25FamilyDrain
  BB25FamilyReturn BB25FamilyReady
  BB25FamilyExactRun BB25FamilyLADebt
  BB25FamilyLADirect BB25FamilyLA.

Module BB25FamilyLAFinal.
Theorem ready_tail b4 : ReadyTail b4.
Proof.
  intros s n HA HG Hn.
  destruct(exact_tail b4 s n HA (tail_bound_of_good s HG) ltac:(lia))
    as [HC [HS HR]].
  eapply rreturns_trans; [apply progress_evstep; exact HR|].
  apply rreturns_cp; constructor.
  - exact HS.
  - exact(ready_drain_word s n HG Hn).
  - now apply strict_reset_empty.
Qed.

Theorem zready b4 s n : Adm s ->Good s ->(2<=n)%nat ->
  RReturns b4 (left s root <{{A}} dc D*>S2>>cells(repeat Y n)*>S1>>0inf).
Proof. apply BB25FamilyLA.zready,ready_tail. Qed.
End BB25FamilyLAFinal.

Open Scope string_scope.
Module TM_1LA.
Definition tm := Eval compute in (TM_from_str "1RB2LA0RB1LB---_1LA3RA1RA4LB1LA").
Theorem nonhalt : ~halts tm c0.
Proof.
  change (~halts(family(Some(S1,L,A)))c0).
  apply nonhalt_of_tail,BB25FamilyLAFinal.ready_tail.
Qed.
End TM_1LA.

(* BB25FamilyEnergy.v *)
Close Scope Z_scope. Close Scope N_scope.
From Coq Require Import List NArith ZArith Lia ZifyNat.
Import ListNotations BB25FamilyCore BB25FamilyStack
  BB25FamilyReset BB25FamilyWord.

(** LB0/Energy.lean in the existing three-letter word algebra.  Source X is
    our D. The only change from reset arithmetic is the pop cost -3. *)
Module BB25FamilyEnergy.
Open Scope Z_scope.
Definition estep (b:digit) (e:BinNums.Z) : BinNums.Z :=
  match b with Y=>2*e+1 | V=>2*e | D=>e/2-3 end.
Fixpoint erun (w:list digit) (e:BinNums.Z) : BinNums.Z :=
  match w with []=>e | b::w=>erun w (estep b e) end.
Lemma erun_app w v e : erun(w++v) e=erun v (erun w e).
Proof. revert e; induction w; intros; cbn [erun app]; auto. Qed.
Lemma estep_le_rstep b e a : e<=a ->estep b e<=rstep b a.
Proof. destruct b; unfold estep,rstep; lia. Qed.
Lemma erun_le_rrun w e a : e<=a ->erun w e<=rrun w a.
Proof.
  revert e a; induction w as [|b w IH]; intros e a H; [exact H|].
  apply IH,estep_le_rstep; exact H.
Qed.
Lemma erun_margin_two w e a : e+2<=a ->erun w e+2<=rrun w a.
Proof.
  revert e a; induction w as [|b w IH]; intros e a H; [exact H|].
  apply IH. destruct b; unfold estep,rstep; lia.
Qed.
Lemma erun_add_two_le_rrun w e a : In D w ->e<=a ->erun w e+2<=rrun w a.
Proof.
  revert e a; induction w as [|b w IH]; intros e a Hin H; [contradiction|].
  destruct Hin as [->|Hin].
  - change (erun w (e/2-3)+2<=rrun w (a/2-1)); apply erun_margin_two; lia.
  - apply IH; [exact Hin|apply estep_le_rstep; exact H].
Qed.

Definition qw := qword.
Lemma qw_app w v a : qw(w++v) a=qw w a++qw v (rrun w a).
Proof. unfold qw; revert a; induction w; intros; cbn [qword app rrun]; [reflexivity|rewrite IHw; reflexivity]. Qed.
Lemma trun_eq_rrun_qw w a c : trun w a c=rrun(qw w a) c.
Proof. symmetry; apply qword_rrun. Qed.
Fixpoint etrun (w:list digit) (a e:BinNums.Z) : BinNums.Z :=
  match w with []=>e | b::w=>etrun w (rstep b a) (estep(qout b a) e) end.
Lemma etrun_app w v a e : etrun(w++v) a e=etrun v (rrun w a) (etrun w a e).
Proof. revert a e; induction w; intros; cbn [etrun rrun app]; auto. Qed.
Lemma etrun_eq_erun_qw w a e : etrun w a e=erun(qw w a) e.
Proof. unfold qw; revert a e; induction w; intros; cbn [etrun qword erun]; auto. Qed.

Fixpoint ht (w:list digit) : BinNums.Z :=
  match w with []=>0 | D::w=>ht w-1 | _::w=>ht w+1 end.
Lemma ht_app w v : ht(w++v)=ht w+ht v.
Proof. induction w as [|b w IH]; [reflexivity|destruct b; cbn [ht app]; rewrite IH; ring]. Qed.
Lemma bal_le_ht w : bal w<=ht w.
Proof. induction w as [|b w IH]; [reflexivity|destruct b; cbn [bal ht]; lia]. Qed.
Lemma bal_qw w a : bal(qw w a)=ht w.
Proof.
  unfold qw; revert a; induction w as [|b w IH]; intro a; [reflexivity|].
  destruct b; cbn [qw qword qout ht]; try destruct (_ =? _);
    cbn [bal]; rewrite IH; lia.
Qed.
Lemma ht_le_bal_qcnt w a : ht w<=bal w+2*Z.of_nat(qcnt w a).
Proof.
  revert a; induction w as [|b w IH]; intro a; [reflexivity|].
  specialize (IH (rstep b a)). destruct b; cbn [ht bal qcnt qstep];
    try destruct (_ =? _); rewrite ?Nat2Z.inj_succ; lia.
Qed.
Lemma ht_ge_neg_length w : -Z.of_nat(length w)<=ht w.
Proof. induction w as [|b w IH]; [reflexivity|destruct b; cbn [ht length]; lia]. Qed.

Lemma dyck_snoc w b : DyckPre w ->0<=bal(w++[b]) ->DyckPre(w++[b]).
Proof.
  intros HD HB p s E.
  destruct (prefix_app_cases p w [b] (ex_intro _ s E)) as [[q HQ]|[q [-> HQ]]].
  - exact (HD _ _ HQ).
  - destruct (prefix_singleton _ _ HQ) as [-> | ->].
    + rewrite app_nil_r; apply dyck_nonneg; exact HD.
    + exact HB.
Qed.
Lemma dyckPre_qw w a : DyckPre w ->DyckPre(qw w a).
Proof.
  revert a; induction w as [|b w IH] using rev_ind; intros a HD; [apply dyck_nil|].
  rewrite qw_app. change (DyckPre(qw w a++[qout b (rrun w a)])).
  apply dyck_snoc.
  - apply IH; eapply dyck_prefix; exact HD.
  - change (0<=bal(qw w a++qw [b] (rrun w a))). rewrite <-qw_app,bal_qw.
    pose proof (dyck_nonneg _ HD). pose proof (bal_le_ht (w++[b])); lia.
Qed.

Definition egain (q:nat) (e:BinNums.Z) := pow4 q*(e+1)-5*qloss q.
Lemma egain_zero e : egain O e=e+1. Proof. unfold egain; change (1*(e+1)-5*0=e+1); ring. Qed.
Lemma egain_succ q e : egain(S q) e=4*egain q e-5.
Proof. unfold egain; rewrite pow4_succ; cbn [qloss]; ring. Qed.
Lemma egain_two_le q e : 1<=e ->2<=egain q e.
Proof. intro H; induction q; [rewrite egain_zero|rewrite egain_succ]; lia. Qed.
Lemma egain_mono q Q e : 1<=e ->(q<=Q)%nat ->egain q e<=egain Q e.
Proof.
  intros He Hq; induction Hq; [reflexivity|].
  rewrite egain_succ; pose proof (egain_two_le m e He); lia.
Qed.
Lemma egain_add i j e : egain(i+j) e=pow4 j*egain i e-5*qloss j.
Proof. unfold egain; rewrite pow4_add,qloss_add; ring. Qed.
Lemma egain_double j e : egain j (2*e+1)=2*(pow4 j*(e+1))-5*qloss j.
Proof. unfold egain; ring. Qed.
Lemma qloss_odd q : (1<=q)%nat ->qloss q mod 2=1.
Proof. destruct q; [lia|cbn [qloss]; lia]. Qed.

Definition Pops (w:list digit) : Prop := forall b, In b w ->b=D \/ b=V.

Definition TW (w:list digit) := tfold [] w.
Lemma tfold_height w s : Z.of_nat(nbit(tfold s w))-Z.of_nat(nsh(tfold s w))=
  Z.of_nat(nbit s)-Z.of_nat(nsh s)+ht w.
Proof.
  revert s; induction w as [|b w IH]; intro s; [cbn [tfold ht]; lia|].
  cbn [tfold]; rewrite IH. destruct b; cbn [tstep ht].
  - cbn [nbit nsh]; lia.
  - cbn [nbit nsh]; lia.
  - destruct (cdec_counts (W::s)) as [HN HS]; rewrite HN,HS; cbn [nbit nsh]; lia.
Qed.
Theorem TW_facts w : 0<=rrun w 0 ->
  Adm(TW w) /\ Good(TW w) /\ Z.of_N(cap(TW w))=rrun w 0 /\
  bval(TW w)=trun w 0 0 /\ pdec(TW w)=qw w 0 /\
  Z.of_nat(nbit(TW w))-Z.of_nat(nsh(TW w))=ht w.
Proof.
  intro H; destruct (tfold_empty_props w H) as [HA [HG [HC [HB _]]]].
  unfold TW; split; [exact HA|split; [exact HG|split; [exact HC|split; [exact HB|split]]]].
  - exact (tfold_pdec w [] H).
  - pose proof (tfold_height w []); cbn [nbit nsh] in H0; lia.
Qed.

End BB25FamilyEnergy.

(* BB25FamilyClock.v *)
Close Scope Z_scope. Close Scope N_scope.
From Coq Require Import List NArith ZArith Lia ZifyNat.
Import ListNotations BB25FamilyCore BB25FamilyStack
  BB25FamilyReset BB25FamilyWord
  BB25FamilyEnergy BB25FamilyExact.

(** Energy growth, clock bounds, and pure arithmetic of one LB0 return.
    The exact-qcnt induction shares the existing Dyck split, not a new parser. *)
Module BB25FamilyClock.
Open Scope Z_scope.

Lemma etrun_gain_exact_aux n : forall w, (length w<=n)%nat ->DyckPre w ->
  forall h, bal w=Z.of_nat h ->forall a e, 1<=e ->
  pow2 h*egain(qcnt w a) e<=etrun w a e+1.
Proof.
  induction n as [|n IH]; intros w Hl Hd h Hb a e He.
  - destruct w; simpl in Hl; [|lia]. simpl in Hb; assert (h=O) by lia; subst h.
    cbn [qcnt etrun pow2 wpow]; rewrite egain_zero; lia.
  - destruct (list_snoc w) as [->|[p [b ->]]].
    + simpl in Hb; assert (h=O) by lia; subst h.
      cbn [qcnt etrun pow2 wpow]; rewrite egain_zero; lia.
    + assert (Hp:DyckPre p) by (eapply dyck_prefix; eassumption).
      assert (Hlp:(length p<=n)%nat) by (rewrite length_app in Hl; simpl in Hl; lia).
      pose proof (dyck_nonneg p Hp) as Hbp.
      pose proof (pow2_pos h) as Hph.
      rewrite bal_app in Hb.
      rewrite etrun_app,qcnt_app; cbn [etrun qcnt].
      destruct b.
      * simpl in Hb; destruct h as [|h]; [lia|].
        assert (Hb':bal p=Z.of_nat h) by (rewrite Nat2Z.inj_succ in Hb; lia).
        pose proof (IH p Hlp Hp h Hb' a e He) as A.
        cbn [qstep qout estep]; rewrite Nat.add_0_r,pow2_succ; lia.
      * simpl in Hb; assert (Hb':bal p=Z.of_nat(S h)) by (rewrite Nat2Z.inj_succ; lia).
        pose proof (IH p Hlp Hp (S h) Hb' a e He) as A.
        rewrite pow2_succ in A; cbn [qstep qout estep].
        rewrite Nat.add_1_r,egain_succ; nia.
      * simpl in Hb; assert (Hb':bal p=Z.of_nat(S h)) by (rewrite Nat2Z.inj_succ; lia).
        cbn [qstep qout]; destruct (Z.eqb (rrun p a mod 2) 1) eqn:Ho.
        -- pose proof (IH p Hlp Hp (S h) Hb' a e He) as A.
           rewrite pow2_succ in A; cbn [estep].
           rewrite Nat.add_1_r,egain_succ; nia.
        -- rewrite Nat.add_0_r; cbn [estep].
           destruct (dyck_split p Hp ltac:(lia)) as [u [v [Ep [Hu [Hv Bv]]]]].
           assert (Hlu:(length u<=n)%nat) by (rewrite Ep,length_app in Hlp; simpl in Hlp; lia).
           assert (Hlv:(length v<=n)%nat) by (rewrite Ep,length_app in Hlp; simpl in Hlp; lia).
           assert (Hbu:bal u=Z.of_nat h) by (rewrite Ep,bal_app in Hb; simpl in Hb; lia).
           set (cu:=etrun u a e). set (au:=rrun u a).
           set (qv:=qcnt v (2*au+1)). set (qu:=qcnt u a).
           set (cc:=etrun v (2*au+1) (2*cu+1)).
           assert (Eq:qcnt p a=(qu+qv)%nat).
           { rewrite Ep,qcnt_app; cbn [qcnt qstep rstep]; reflexivity. }
           assert (Et:etrun p a e=cc).
           { rewrite Ep,etrun_app; cbn [etrun qout estep rstep]; reflexivity. }
           assert (En:v<>[]).
           { intro E; subst v; rewrite Ep,rrun_app in Ho; cbn [rrun rstep] in Ho.
             apply Z.eqb_neq in Ho; lia. }
           assert (Hqv:(1<=qv)%nat) by
             (apply qcnt_pos_of_hasCl; [exact Hv|apply bal_has_close; auto; split; auto]).
           pose proof (IH u Hlu Hu h Hbu a e He) as A.
           change (pow2 h*egain qu e<=cu+1) in A.
           assert (Hcu:1<=cu) by (pose proof (egain_two_le qu e He); nia).
           pose proof (IH v Hlv Hv O Bv (2*au+1) (2*cu+1) ltac:(lia)) as B.
           change (1*egain qv (2*cu+1)<=cc+1) in B.
           rewrite egain_double in B.
           pose proof (pow4_pos qv) as HF.
           pose proof (qloss_pos qv Hqv) as HM.
           pose proof (three_qloss qv) as EF.
           assert (HB:2*(pow4 qv*cu)+qloss qv+1<=cc) by nia.
           assert (HC:pow4 qv*cu-2*qloss qv<=cc/2-3).
           { pose proof (div2_bounds cc); nia. }
           rewrite Eq,Et,egain_add.
           pose proof (Z.mul_le_mono_nonneg_l _ _ (pow4 qv) ltac:(lia) A) as HA.
           assert (HMp:5*qloss qv<=5*qloss qv*pow2 h) by nia.
           nia.
Qed.
Theorem etrun_ge_egain w h a e q : DyckPre w ->bal w=Z.of_nat h ->1<=e ->
  (q<=qcnt w a)%nat ->pow2 h*egain q e<=etrun w a e+1.
Proof.
  intros Hd Hb He Hq.
  pose proof (etrun_gain_exact_aux (length w) w ltac:(lia) Hd h Hb a e He).
  pose proof (egain_mono q (qcnt w a) e He Hq). pose proof (pow2_pos h); nia.
Qed.

Theorem dpow_TW_facts w k : Z.of_N k<=rrun w 0 ->
  Adm(dpow k (TW w)) /\ Good(dpow k (TW w)) /\
  Z.of_N(cap(dpow k (TW w)))=rrun w 0-Z.of_N k /\
  bval(dpow k (TW w))=trun w 0 0 /\ pdec(dpow k (TW w))=qw w 0 /\
  Z.of_nat(nbit(dpow k (TW w)))-Z.of_nat(nsh(dpow k (TW w)))=ht w.
Proof.
  intro H; destruct (TW_facts w ltac:(lia)) as [HA [HG [HC [HB [HP HH]]]]].
  split; [apply dpow_adm; exact HA|split; [apply dpow_good; exact HG|split]].
  - rewrite dpow_cap by lia; lia.
  - split; [rewrite dpow_bval; exact HB|split; [rewrite dpow_pdec; exact HP|]].
    destruct (dpow_counts k (TW w)) as [HN HS]; rewrite HN,HS; exact HH.
Qed.

Lemma Pops_app w v : Pops(w++v) ->Pops w /\ Pops v.
Proof.
  unfold Pops; intro H; split; intros b Hb; apply H; apply in_or_app; auto.
Qed.

Lemma chi_pops m : Pops(chi m).
Proof.
  destruct m as [|p]; [intros b H; contradiction|].
  change (Pops(pchi p)); induction p; unfold Pops in *; cbn [pchi];
    intros b H; try contradiction; destruct H as [->|H]; auto.
Qed.
Lemma chi_length_le s m : (1<=m<BB25FamilyCore.pow2 (S s))%N ->
  (length(chi m)<=s)%nat.
Proof.
  revert m; induction s as [|s IH]; intros m H.
  - rewrite chi_small by (change (1<=m<2)%N in H; lia); reflexivity.
  - destruct (N.lt_ge_cases m 2) as [Hm|Hm].
    + rewrite chi_small by exact Hm; cbn; lia.
    + rewrite chi_step by exact Hm; cbn [length]. apply le_n_S,IH.
      change (1<=m<2*BB25FamilyCore.pow2 (S s))%N in H; lia.
Qed.
Lemma erun_replicate_Y n e : erun(repeat Y n) e=pow2 n*(e+1)-1.
Proof.
  revert e; induction n as [|n IH]; intro e.
  - change (e=1*(e+1)-1); ring.
  - cbn [repeat erun estep]; rewrite IH,pow2_succ; ring.
Qed.
Lemma erun_replicate_D n e : erun(repeat D n) e=(e+6)/pow2 n-6.
Proof.
  revert e; induction n as [|n IH]; intro e.
  - change (e=(e+6)/1-6); rewrite Z.div_1_r; ring.
  - cbn [repeat erun estep]; rewrite IH,pow2_succ.
    replace (e/2-3+6) with ((e+6)/2) by lia.
    rewrite Z.div_div by (pose proof (pow2_pos n); lia); reflexivity.
Qed.
Theorem erun_buffer r e : (4<=r)%nat ->
  erun(repeat Y r++[V]++repeat D (r-1)) e=4*e-2.
Proof.
  intro Hr; rewrite !erun_app,erun_replicate_Y.
  change (erun(repeat D (r-1)) (2*(pow2 r*(e+1)-1))=4*e-2).
  rewrite erun_replicate_D.
  assert (EP:pow2 r=2*pow2(r-1)).
  { replace r with (S(r-1)) at 1 by lia; apply pow2_succ. }
  pose proof (pow2_mono 3 (r-1) ltac:(lia)) as HP.
  change (8<=pow2(r-1)) in HP. rewrite EP.
  replace (2*(2*pow2(r-1)*(e+1)-1)+6) with (4*(e+1)*pow2(r-1)+4) by ring.
  rewrite Z.div_add_l by lia; rewrite Z.div_small by lia; ring.
Qed.
Theorem erun_pops_nonneg w e : Pops w ->6*(pow2(length w)-1)<=e ->0<=erun w e.
Proof.
  revert e; induction w as [|b w IH]; intros e HP HE.
  - change (6*(1-1)<=e) in HE; exact HE.
  - assert (Hb:b=D \/ b=V) by (apply HP; now left).
    assert (Hw:Pops w) by (intros d Hd; apply HP; now right).
    cbn [length] in HE; rewrite pow2_succ in HE.
    pose proof (pow2_pos (length w)) as Hpow.
    change (0<=erun w (estep b e)); apply IH; [exact Hw|].
    destruct Hb as [->| ->]; unfold estep; lia.
Qed.

Theorem density_bounds v h : DyckPre v ->bal([Y;Y;Y]++v)=Z.of_nat h ->
  23*pow2(h+2*qcnt([Y;Y;Y]++v) 0)+pow2 h<=24*(trun([Y;Y;Y]++v) 0 0+1) /\
  19*pow2(h+2*qcnt([Y;Y;Y]++v) 0)+5*pow2 h<=24*(etrun([Y;Y;Y]++v) 0 0+1).
Proof.
  intros HD HL.
  assert (Hh:(3<=h)%nat) by (pose proof (dyck_nonneg v HD); change (bal v+1+1+1=Z.of_nat h) in HL; lia).
  assert (HB:bal v=Z.of_nat(h-3)) by (change (bal v+1+1+1=Z.of_nat h) in HL; lia).
  change (23*pow2(h+2*qcnt v 7)+pow2 h<=24*(trun v 7 7+1) /\
    19*pow2(h+2*qcnt v 7)+5*pow2 h<=24*(etrun v 7 7+1)).
  pose proof (trun_ge_qgain v (h-3) 7 7 (qcnt v 7) HD HB ltac:(lia) ltac:(lia)) as A.
  pose proof (etrun_ge_egain v (h-3) 7 7 (qcnt v 7) HD HB ltac:(lia) ltac:(lia)) as B.
  pose proof (three_qloss (qcnt v 7)) as HM.
  assert (EP:pow2 h=8*pow2(h-3)).
  { replace h with ((h-3)+3)%nat at 1 by lia; rewrite pow2_add; change (pow2(h-3)*8=8*pow2(h-3)); ring. }
  rewrite pow2_add,<-pow4_two,EP.
  unfold qgain in A; unfold egain in B.
  assert (Hloss:3*(pow2(h-3)*qloss(qcnt v 7))=pow2(h-3)*pow4(qcnt v 7)-pow2(h-3)) by nia.
  split; nia.
Qed.

Lemma Pops_bal w : Pops w ->bal w= -Z.of_nat(length w).
Proof.
  induction w as [|b w IH]; intro H; [reflexivity|].
  assert (Hw:Pops w) by (intros d Hd; apply H; now right).
  specialize (IH Hw). destruct (H b (or_introl eq_refl)) as [-> | ->];
    cbn [bal length]; lia.
Qed.
Lemma append_pops x eta : DyckPre x ->Pops eta ->Z.of_nat(length eta)<=bal x ->
  DyckPre(x++eta).
Proof.
  intros HD HP HL p s E.
  destruct (prefix_app_cases p x eta (ex_intro _ s E)) as [[q HQ]|[q [-> [r HE]]]].
  - exact (HD _ _ HQ).
  - rewrite HE in HP,HL; destruct (Pops_app _ _ HP) as [HQ _].
    rewrite bal_app,(Pops_bal q HQ). rewrite length_app in HL; lia.
Qed.
Lemma dyck_replicate_Y n : DyckPre(repeat Y n).
Proof. induction n; [apply dyck_nil|apply dyck_Y; exact IHn]. Qed.
Theorem buffer_dyck r : (1<=r)%nat ->
  DyckPre(repeat Y r++[V]++repeat D (r-1)) /\
  bal(repeat Y r++[V]++repeat D (r-1))=0.
Proof.
  intro Hr.
  assert (HP:Pops([V]++repeat D (r-1))).
  { intros b H; cbn [app In] in H; destruct H as [<-|H]; [auto|].
    apply repeat_spec in H; subst b; auto. }
  assert (HL:Z.of_nat(length([V]++repeat D (r-1)))=Z.of_nat r).
  { rewrite length_app,repeat_length; cbn [length]; lia. }
  split.
  - apply append_pops; [apply dyck_replicate_Y|exact HP|rewrite HL,bal_repeat_Y; reflexivity].
  - rewrite bal_app,bal_repeat_Y,(Pops_bal _ HP); rewrite HL; lia.
Qed.
Lemma ht_replicate_Y n : ht(repeat Y n)=Z.of_nat n.
Proof. induction n; cbn [repeat ht]; lia. Qed.
Lemma ht_replicate_D n : ht(repeat D n)= -Z.of_nat n.
Proof. induction n; cbn [repeat ht]; lia. Qed.

Theorem height_close v : DyckPre v ->4<=bal([Y;Y;Y]++v) ->6<=ht([Y;Y;Y]++v) ->
  exists h, ht([Y;Y;Y]++v)=Z.of_nat h /\ (5<=h)%nat /\
    23*pow2 h<=24*(trun([Y;Y;Y]++v) 0 0+1) /\
    3*pow2(h-2)+4<=etrun([Y;Y;Y]++v) 0 0.
Proof.
  intros HD HL HH.
  set (lw:=[Y;Y;Y]++v) in *.
  set (lv:=Z.to_nat(bal lw)). set (h:=Z.to_nat(ht lw)).
  assert (EL:bal lw=Z.of_nat lv) by (unfold lv; rewrite Z2Nat.id; lia).
  assert (EH:ht lw=Z.of_nat h) by (unfold h; rewrite Z2Nat.id; lia).
  destruct (density_bounds v lv HD EL) as [A B].
  fold lw in A,B.
  pose proof (ht_le_bal_qcnt lw 0) as Hheight.
  assert (Hnat:(h<=lv+2*qcnt lw 0)%nat) by lia.
  pose proof (pow2_mono h (lv+2*qcnt lw 0) Hnat) as HP.
  pose proof (pow2_mono 4 lv ltac:(lia)) as H16; change (16<=pow2 lv) in H16.
  assert (HH6:(6<=h)%nat) by lia.
  exists h; split; [exact EH|split; [lia|split]].
  - lia.
  - assert (Epow:pow2 h=4*pow2(h-2)).
    { replace h with ((h-2)+2)%nat at 1 by lia; rewrite pow2_add; change (pow2(h-2)*4=4*pow2(h-2)); ring. }
    pose proof (pow2_mono 4 (h-2) ltac:(lia)) as Hsmall.
    change (16<=pow2(h-2)) in Hsmall; rewrite Epow in HP; lia.
Qed.

Theorem drain_energy F h t d : (5<=h)%nat ->3*pow2(h-2)+4<=F ->
  (t<=h-2)%nat ->(d=D \/ d=V) ->6*(pow2 t-1)<=4*estep d F-2.
Proof.
  intros Hh HF Ht Hd.
  assert (EP:pow2(h-2)=8*pow2(h-5)).
  { replace (h-2)%nat with ((h-5)+3)%nat by lia; rewrite pow2_add; change (pow2(h-5)*8=8*pow2(h-5)); ring. }
  pose proof (pow2_mono t (h-2) Ht) as HP.
  pose proof (pow2_pos (h-5)) as HQ.
  rewrite EP in HF,HP; destruct Hd as [-> | ->]; unfold estep; lia.
Qed.
Theorem buffer_counter b h t (n1:N) d : (5<=h)%nat ->23*pow2 h<=24*(b+1) ->
  (t<=h-2)%nat ->Z.of_N n1+6<=6*pow2 t ->(d=D \/ d=V) ->
  Z.of_N n1+8<=4*(rstep d b+1).
Proof.
  intros Hh HB Ht Hn Hd.
  assert (EP:pow2(h-2)=8*pow2(h-5)).
  { replace (h-2)%nat with ((h-5)+3)%nat by lia; rewrite pow2_add; change (pow2(h-5)*8=8*pow2(h-5)); ring. }
  assert (EP':pow2 h=32*pow2(h-5)).
  { replace h with ((h-5)+5)%nat at 1 by lia; rewrite pow2_add; change (pow2(h-5)*32=32*pow2(h-5)); ring. }
  pose proof (pow2_mono t (h-2) Ht) as HP.
  pose proof (pow2_pos (h-5)) as HQ.
  rewrite EP in HP; rewrite EP' in HB; destruct Hd as [-> | ->]; unfold rstep; lia.
Qed.
Theorem counter_close (count n1:N) s x :
  Z.of_N count=pow2 s*(Z.of_N n1+6) -> Z.of_N n1+8<=4*(x+1) ->
  Z.of_N(count-1)+2<=pow2(s+2)*(x+1)-1.
Proof.
  intros HC HB; pose proof (pow2_pos s) as HP.
  assert (HCpos:(1<=count)%N) by nia.
  rewrite N2Z.inj_sub by exact HCpos; rewrite pow2_add.
  change (Z.of_N count-1+2<=pow2 s*4*(x+1)-1).
  pose proof (Z.mul_le_mono_nonneg_l _ _ (pow2 s) ltac:(lia) HB); nia.
Qed.

End BB25FamilyClock.

(* BB25FamilyLB0Shape.v *)
Close Scope Z_scope. Close Scope N_scope.
From Coq Require Import List ZArith Lia.
Import ListNotations BB25FamilyWord
  BB25FamilyEnergy BB25FamilyClock.

Module BB25FamilyLB0Shape.
Open Scope Z_scope.

Lemma protected_prefix v d h : DyckPre v ->ht v=Z.of_nat h-3 ->(5<=h)%nat ->
  (d=D \/ d=V) ->
  DyckPre(qw v 7++[d]) /\ bal(qw v 7++[d])=Z.of_nat h-4 /\
    Z.of_nat h-4<=ht(qw v 7++[d]).
Proof.
  intros HD HH Hh Hd.
  assert (EB:bal(qw v 7++[d])=Z.of_nat h-4).
  { rewrite bal_app,bal_qw,HH; destruct Hd as [-> | ->]; cbn [bal]; lia. }
  split.
  - apply dyck_snoc; [now apply dyckPre_qw|rewrite EB; lia].
  - split; [exact EB|rewrite <-EB; apply bal_le_ht].
Qed.

Theorem protected_pop_stop v d r eta h : DyckPre v ->ht v=Z.of_nat h-3 ->
  (5<=h)%nat ->(4<=r)%nat ->(d=D \/ d=V) ->Pops eta ->
  (length eta+5<=h)%nat ->
  let v':=qw v 7++[d]++(repeat Y r++[V]++repeat D(r-1))++eta in
  DyckPre v' /\ 4<=bal([Y;Y;Y]++v') /\ 6<=ht([Y;Y;Y]++v').
Proof.
  intros HD HH Hh Hr Hd HP HL.
  destruct(protected_prefix v d h HD HH Hh Hd) as [HDp [EBp EHp]].
  destruct(buffer_dyck r ltac:(lia)) as [HDb EBb].
  assert (EHb:ht(repeat Y r++[V]++repeat D(r-1))=2).
  { rewrite !ht_app,ht_replicate_Y,ht_replicate_D; cbn [ht]; lia. }
  assert (HDe:DyckPre((qw v 7++[d])++(repeat Y r++[V]++repeat D(r-1))++eta)).
  { rewrite app_assoc; apply append_pops.
    - now apply dyck_app.
    - exact HP.
    - rewrite bal_app,EBp,EBb; lia. }
  cbn zeta; split; [repeat rewrite <-app_assoc in HDe |- *; exact HDe|split].
  - change (4<=bal(qw v 7++[d]++(repeat Y r++[V]++repeat D(r-1))++eta)+1+1+1).
    rewrite !bal_app,bal_qw,HH,(Pops_bal eta HP).
    pose proof EBb; rewrite !bal_app in H; destruct Hd as [-> | ->]; cbn [bal] in *; lia.
  - change (6<=ht(qw v 7++[d]++(repeat Y r++[V]++repeat D(r-1))++eta)+1+1+1).
    rewrite (app_assoc (qw v 7) [d] ((repeat Y r++[V]++repeat D(r-1))++eta)).
    rewrite (ht_app (qw v 7++[d]) ((repeat Y r++[V]++repeat D(r-1))++eta)),
      (ht_app (repeat Y r++[V]++repeat D(r-1)) eta),EHb.
    pose proof(ht_ge_neg_length eta).
    lia.
Qed.

Theorem protected_buffer_stop v d s h : DyckPre v ->ht v=Z.of_nat h-3 ->
  (5<=h)%nat ->(d=D \/ d=V) ->
  let v':=qw v 7++[d]++repeat Y(s+2) in
  DyckPre v' /\ 4<=bal([Y;Y;Y]++v') /\ 6<=ht([Y;Y;Y]++v').
Proof.
  intros HD HH Hh Hd.
  destruct(protected_prefix v d h HD HH Hh Hd) as [HDp [EBp EHp]].
  assert (HB:6<=bal([Y;Y;Y]++(qw v 7++[d]++repeat Y(s+2)))).
  { change (6<=bal(qw v 7++[d]++repeat Y(s+2))+1+1+1).
    rewrite app_assoc,bal_app,EBp,bal_repeat_Y; lia. }
  cbn zeta; split.
  - rewrite app_assoc; apply dyck_app; [exact HDp|apply dyck_replicate_Y].
  - split; [lia|pose proof(bal_le_ht ([Y;Y;Y]++(qw v 7++[d]++repeat Y(s+2)))); lia].
Qed.

End BB25FamilyLB0Shape.

(* BB25FamilyLB0Scan.v *)
Close Scope Z_scope. Close Scope N_scope.
From BusyCoq Require Import Individual25.
Open Scope sym_scope.
From Coq Require Import List NArith ZArith Lia.
Import ListNotations BB25FamilyRules
  BB25FamilyCore BB25FamilyWord
  BB25FamilyStack BB25FamilyReset
  BB25FamilyMachine BB25FamilyReturn
  BB25FamilyClosure BB25FamilyExact
  BB25FamilyEnergy.

Module BB25FamilyLB0Scan.
Notation lb0 := (family(Some(S0,L,B))).
Notation "c -->* c'" := (c -[lb0]->* c') (at level 40).
Notation "c -->+ c'" := (c -[lb0]->+ c') (at level 40).

Definition zCfg s r := sweep (Z::s) r.

(** A pop in the B1 sweep requires four units of the counter below it.
    All intermediate excursions preserve the arbitrary unread tails. *)
Lemma pop_four s : (4<=cap s)%N ->forall l r,
  left(W::s) l <{{B}} S1 >> r -->+
  left(cdec(cdec(cdec(cdec s)))) l <{{B}} S1 >> [S2;S2] *> r.
Proof.
  intros HC l r.
  assert (H1:(0<cap s)%N) by lia.
  assert (E1:cap(cdec s)=(cap s-1)%N) by now apply cdec_capacity.
  assert (H2:(0<cap(cdec s))%N) by lia.
  assert (E2:cap(cdec(cdec s))=(cap s-2)%N).
  { rewrite cdec_capacity by exact H2; rewrite E1; lia. }
  assert (H3:(0<cap(cdec(cdec s)))%N) by lia.
  assert (E3:cap(cdec(cdec(cdec s)))=(cap s-3)%N).
  { rewrite cdec_capacity by exact H3; rewrite E2; lia. }
  assert (H4:(0<cap(cdec(cdec(cdec s))))%N) by lia.
  rewrite left_cons; cbn [tc].
  eapply progress_trans; [apply B1_W|].
  eapply progress_trans; [apply cdec_run; exact H1|].
  eapply progress_trans; [apply right_one|].
  eapply progress_trans; [apply cdec_run; exact H2|].
  eapply progress_trans; [apply G_B_left|].
  eapply progress_trans; [apply cdec_run; exact H3|].
  eapply progress_trans; [apply right_one|].
  eapply progress_trans; [apply cdec_run; exact H4|].
  apply right_N2.
Qed.

(** The member-independent one-bit branch, with its two guarded decrements. *)
Lemma z_depart s r : (2<=cap s)%N ->
  zCfg s r -->+ left(W::cdec(cdec s)) root {{A}}>
    S2 >> cells(repeat Y r) *> S1 >> 0inf.
Proof.
  intro HC; assert (H1:(0<cap s)%N) by lia.
  assert (H2:(0<cap(cdec s))%N) by (rewrite cdec_capacity by exact H1; lia).
  unfold zCfg,sweep; rewrite !left_cons; cbn [tc].
  eapply progress_trans; [apply B1_Z|].
  eapply progress_trans; [apply cdec_run; exact H1|].
  eapply progress_trans; [apply right_one|].
  eapply progress_trans; [apply cdec_run; exact H2|].
  apply right_V.
Qed.

Definition entry_core : list tok := [X;Z;Z;X;Z].
Lemma entry_run_931 : c0 -[lb0]->> 931 / (zCfg entry_core 7).
Proof. apply multistep_c_spec; reflexivity. Qed.
Lemma entry_run : c0 -->* zCfg entry_core 7.
Proof. apply multistep_evstep_iff; exists 931%nat; apply entry_run_931. Qed.

Definition tw u := tfold [] u.
Lemma tw_snoc u d : tw(u++[d])=tstep (tw u) d.
Proof. unfold tw; rewrite tfold_app; reflexivity. Qed.
Lemma tw_capacity u : (0<=rrun u 0)%Z ->Z.of_N(cap(tw u))=rrun u 0.
Proof. intro H; exact (proj1(proj2(proj2(tfold_empty_props u H)))). Qed.
Lemma debt_bound u n : (Z.of_N n<=erun u 0)%Z ->(n<=cap(tw u))%N.
Proof.
  intro HE; pose proof (erun_le_rrun u 0 0 ltac:(lia)) as HR.
  pose proof (tw_capacity u ltac:(lia)); lia.
Qed.

Lemma sweep_X s j : sweep(X::s) j -->+ sweep s (S j).
Proof. unfold sweep; rewrite left_cons; cbn [tc cells flat_map repeat dc]; apply B1_X. Qed.

(** All reverse-debt identities are used only under an energy budget;
    this supplies the guards required by the saturating Coq cdec. *)
Lemma scan_V_even u n j : (n mod 2=0)%N ->
  (Z.of_N n<=erun(u++[V]) 0)%Z ->
  sweep(dpow n(tw(u++[V]))) j -->+ sweep(dpow(n/2)(tw u)) (S j) /\
  (Z.of_N(n/2)<=erun u 0)%Z.
Proof.
  intros Hpar HE; rewrite erun_app in HE; cbn [erun estep] in HE.
  assert (HE':(Z.of_N(n/2)<=erun u 0)%Z) by lia.
  split; [|exact HE']; rewrite tw_snoc; cbn [tstep].
  replace n with (2*(n/2))%N at 1 by lia.
  rewrite dpow_X_even by (apply debt_bound; exact HE'); apply sweep_X.
Qed.

Lemma scan_Y_odd u n j : (n mod 2=1)%N ->
  (Z.of_N n<=erun(u++[Y]) 0)%Z ->
  sweep(dpow n(tw(u++[Y]))) j -->+ sweep(dpow((n-1)/2)(tw u)) (S j) /\
  (Z.of_N((n-1)/2)<=erun u 0)%Z.
Proof.
  intros Hpar HE; rewrite erun_app in HE; cbn [erun estep] in HE.
  assert (HE':(Z.of_N((n-1)/2)<=erun u 0)%Z) by lia.
  split; [|exact HE']; rewrite tw_snoc; cbn [tstep].
  replace n with (2*((n-1)/2)+1)%N at 1 by lia.
  rewrite dpow_Z_odd by (apply debt_bound; exact HE'); apply sweep_X.
Qed.

Lemma scan_Y_even u n j : (n mod 2=0)%N ->
  (Z.of_N n<=erun(u++[Y]) 0)%Z ->
  sweep(dpow n(tw(u++[Y]))) j=zCfg(dpow(n/2)(tw u)) j /\
  (Z.of_N(n/2)<=erun u 0)%Z.
Proof.
  intros Hpar HE; rewrite erun_app in HE; cbn [erun estep] in HE.
  assert (HE':(Z.of_N(n/2)<=erun u 0)%Z) by lia.
  split; [|exact HE']; rewrite tw_snoc; cbn [tstep].
  replace n with (2*(n/2))%N at 1 by lia.
  rewrite dpow_Z_even by (apply debt_bound; exact HE'); reflexivity.
Qed.

Lemma scan_V_odd u n j : (n mod 2=1)%N ->
  (Z.of_N n<=erun(u++[V]) 0)%Z ->
  sweep(dpow n(tw(u++[V]))) j=zCfg(dpow((n+1)/2)(tw u)) j /\
  (Z.of_N((n+1)/2)<=erun u 0)%Z.
Proof.
  intros Hpar HE; rewrite erun_app in HE; cbn [erun estep] in HE.
  assert (HE':(Z.of_N((n+1)/2)<=erun u 0)%Z) by lia.
  split; [|exact HE']; rewrite tw_snoc; cbn [tstep].
  replace n with (2*((n-1)/2)+1)%N at 1 by lia.
  rewrite dpow_X_odd by
    (replace ((n-1)/2+1)%N with ((n+1)/2)%N by lia; apply debt_bound; exact HE').
  replace ((n-1)/2+1)%N with ((n+1)/2)%N by lia; reflexivity.
Qed.

Lemma scan_D u n j : (Z.of_N n<=erun(u++[D]) 0)%Z ->
  sweep(dpow n(tw(u++[D]))) j -->+ sweep(dpow(2*n+6)(tw u)) (S j) /\
  (Z.of_N(2*n+6)<=erun u 0)%Z.
Proof.
  intro HE; rewrite erun_app in HE; cbn [erun estep] in HE.
  assert (HE':(Z.of_N(2*n+6)<=erun u 0)%Z) by lia.
  pose proof (debt_bound u (2*n+6)%N HE') as HC.
  split; [|exact HE']; rewrite tw_snoc; cbn [tstep].
  rewrite cdec_W by lia.
  change (sweep(dpow n(W::dpow 2 (tw u))) j -->+ sweep(dpow(2*n+6)(tw u)) (S j)).
  rewrite dpow_W by (rewrite dpow_cap by lia; lia).
  rewrite <-dpow_add.
  assert (HR:=pop_four (dpow(2*n+2)(tw u)) ltac:(rewrite dpow_cap by lia; lia)
    root (cells(repeat Y j) *> S1 >> 0inf)).
  change (sweep(W::dpow(2*n+2)(tw u)) j -->+
    sweep(dpow 4(dpow(2*n+2)(tw u))) (S j)) in HR.
  rewrite <-dpow_add in HR; replace (4+(2*n+2))%N with (2*n+6)%N in HR by lia.
  exact HR.
Qed.

Notation npow := BB25FamilyCore.pow2.
Lemma scan_Drun count : forall pre n j,
  (Z.of_N n<=erun(pre++repeat D count) 0)%Z ->
  sweep(dpow n(tw(pre++repeat D count))) j -->*
    sweep(dpow(npow count*(n+6)-6)(tw pre)) (j+count)%nat /\
  (Z.of_N(npow count*(n+6)-6)<=erun pre 0)%Z.
Proof.
  induction count as [|count IH]; intros pre n j HE.
  - cbn [repeat npow]; rewrite app_nil_r in *.
    replace (1*(n+6)-6)%N with n by lia; rewrite Nat.add_0_r.
    split; [apply evstep_refl|exact HE].
  - assert (ER:repeat D (S count)=repeat D count++[D]) by apply repeat_cons.
    rewrite ER,app_assoc in HE |- *.
    destruct (scan_D (pre++repeat D count) n j HE) as [HR1 HE1].
    destruct (IH pre (2*n+6)%N (S j) HE1) as [HR2 HE2].
    assert (EN:(npow count*(2*n+6+6)-6=npow(S count)*(n+6)-6)%N)
      by (cbn [npow]; f_equal; ring).
    rewrite EN in HR2,HE2; split; [|exact HE2].
    replace (j+S count)%nat with (S j+count)%nat by lia.
    apply progress_evstep; eapply progress_evstep_trans; eassumption.
Qed.

Lemma scan_pops t : Pops t ->forall pre n j,
  (Z.of_N n<=erun(pre++t) 0)%Z ->
  (exists eta tail debt,
      t=eta++V::tail /\ (Z.of_N debt<=erun(pre++eta) 0)%Z /\
      ((n mod 2=0)%N ->(1<=List.length tail)%nat) /\
      (n=0%N ->(2<=List.length tail)%nat) /\
      sweep(dpow n(tw(pre++t))) j -->* zCfg(dpow debt(tw(pre++eta))) (j+List.length tail)%nat)
  \/ (exists debt,
      (Z.of_N debt<=erun pre 0)%Z /\ (debt+6<=npow(List.length t)*(n+6))%N /\
      sweep(dpow n(tw(pre++t))) j -->* sweep(dpow debt(tw pre)) (j+List.length t)%nat).
Proof.
  induction t as [|b t IH] using rev_ind; intros HT pre n j HE.
  - right; exists n; rewrite app_nil_r in *; cbn [List.length npow].
    split; [exact HE|split; [lia|rewrite Nat.add_0_r; apply evstep_refl]].
  - assert (HT':Pops t) by (intros x Hx; apply HT; apply in_or_app; left; exact Hx).
    assert (Hb:b=D \/ b=V) by (apply HT; apply in_or_app; right; now left).
    rewrite app_assoc in HE.
    destruct Hb as [-> | ->].
    + destruct (scan_D (pre++t) n j HE) as [HR1 HE1].
      destruct (IH HT' pre (2*n+6)%N (S j) HE1)
        as [[eta [tail [debt [Et [Hd [Hpar [Hz HR2]]]]]]]|[debt [Hd [Hbound HR2]]]].
      * left; exists eta,(tail++[D]),debt; split.
        -- rewrite Et,<-app_assoc; reflexivity.
        -- split; [exact Hd|split].
           ++ intros _; rewrite List.length_app; cbn; lia.
           ++ split.
              ** intros _; specialize (Hpar ltac:(lia)); rewrite List.length_app; cbn; lia.
              ** rewrite List.length_app; cbn; replace (j+(List.length tail+1))%nat
                   with (S j+List.length tail)%nat by lia.
                 rewrite app_assoc; apply progress_evstep; eapply progress_evstep_trans; eassumption.
      * right; exists debt; split; [exact Hd|split].
        -- rewrite List.length_app; cbn [List.length]; rewrite Nat.add_1_r; cbn [npow]; nia.
        -- rewrite List.length_app; cbn; replace (j+(List.length t+1))%nat
             with (S j+List.length t)%nat by lia.
           rewrite app_assoc; apply progress_evstep; eapply progress_evstep_trans; eassumption.
    + destruct (N.eq_dec (n mod 2) 1) as [Ho|He].
      * destruct (scan_V_odd (pre++t) n j Ho HE) as [EC HC].
        left; exists t,(nil:list digit),((n+1)/2)%N; split; [reflexivity|split; [exact HC|split]].
        -- intro H; lia.
        -- split; [intro H; subst n; discriminate|].
           cbn [List.length]; rewrite Nat.add_0_r,app_assoc,EC; apply evstep_refl.
      * assert (He':(n mod 2=0)%N) by (pose proof (N.mod_lt n 2 ltac:(discriminate)); lia).
        destruct (scan_V_even (pre++t) n j He' HE) as [HR1 HE1].
        destruct (IH HT' pre (n/2)%N (S j) HE1)
          as [[eta [tail [debt [Et [Hd [Hpar [Hz HR2]]]]]]]|[debt [Hd [Hbound HR2]]]].
        -- left; exists eta,(tail++[V]),debt; split.
           ++ rewrite Et,<-app_assoc; reflexivity.
           ++ split; [exact Hd|split].
              ** intros _; rewrite List.length_app; cbn; lia.
              ** split.
                 --- intro Hn; subst n; specialize (Hz eq_refl); rewrite List.length_app; cbn; lia.
                 --- rewrite List.length_app; cbn; replace (j+(List.length tail+1))%nat
                       with (S j+List.length tail)%nat by lia.
                     rewrite app_assoc; apply progress_evstep; eapply progress_evstep_trans; eassumption.
        -- right; exists debt; split; [exact Hd|split].
           ++ rewrite List.length_app; cbn [List.length]; rewrite Nat.add_1_r; cbn [npow].
              pose proof (N.div_le_upper_bound n 2 n ltac:(discriminate) ltac:(lia)); nia.
           ++ rewrite List.length_app; cbn; replace (j+(List.length t+1))%nat
                with (S j+List.length t)%nat by lia.
              rewrite app_assoc; apply progress_evstep; eapply progress_evstep_trans; eassumption.
Qed.

End BB25FamilyLB0Scan.

(* BB25FamilyLB0.v *)
Close Scope Z_scope. Close Scope N_scope.
From BusyCoq Require Import Individual25.
Open Scope sym_scope.
From Coq Require Import List NArith ZArith Lia String.
Import ListNotations BB25FamilyRules
  BB25FamilyCore BB25FamilyWord
  BB25FamilyStack BB25FamilyReset
  BB25FamilyMachine BB25FamilyDrain
  BB25FamilyReturn BB25FamilyClosure
  BB25FamilyExact BB25FamilyExactRun
  BB25FamilyEnergy BB25FamilyClock
  BB25FamilyLB0Scan BB25FamilyLB0Shape.

Module BB25FamilyLB0.
Open Scope Z_scope.
Notation zpow := BB25FamilyWord.pow2.
Notation npow := BB25FamilyCore.pow2.
Notation lb0 := (family(Some(S0,L,B))).
Notation "c -->* c'" := (c -[lb0]->* c') (at level 40).
Notation "c -->+ c'" := (c -[lb0]->+ c') (at level 40).

Record ZInv (w:list digit) (k:N) (r:nat) : Prop := {
  zinv_protected : exists v,w=[Y;Y;Y]++v /\ DyckPre v;
  zinv_energy : Z.of_N k<=erun w 0;
  zinv_counter : Z.of_N k+2<=rrun w 0;
  zinv_height : exists h,ht w=Z.of_nat h /\ (5<=h)%nat /\
    23*zpow h<=24*(trun w 0 0+1) /\ 3*zpow(h-2)+4<=etrun w 0 0;
  zinv_right : (4<=r)%nat
}.

Definition lb_digit w k := if N.odd(cap(dpow(k+2)(tw w))) then V else D.
Definition lb_m w k := (cap(dpow k(tw w))/2)%N.
Definition lb_base w k := qw w 0++[lb_digit w k].
Definition lb_buffer r := repeat Y r++[V]++repeat D(r-1).
Definition lb_prefix w k r := lb_base w k++lb_buffer r.
Definition lb_word w k r := lb_prefix w k r++chi(lb_m w k).

Lemma lb_digit_cases w k : lb_digit w k=D \/ lb_digit w k=V.
Proof. unfold lb_digit; destruct (N.odd _); auto. Qed.
Lemma two_debts w k : cdec(cdec(dpow k(tw w)))=dpow(k+2)(tw w).
Proof. replace (k+2)%N with (2+k)%N by lia; rewrite dpow_add; reflexivity. Qed.

Lemma return_chi_bound w k h : Z.of_N k+2<=rrun w 0 ->
  ht w=Z.of_nat h ->(5<=h)%nat ->(List.length(chi(lb_m w k))<=h-2)%nat.
Proof.
  intros HC HH Hh.
  destruct (dpow_TW_facts w k ltac:(lia)) as [HA [HG [Hcap [HB [HP Hheight]]]]].
  pose proof (adm_bound _ HA) as Hcount.
  pose proof (capacity_bound _ HA) as Hbound.
  assert (HE:(nbit(dpow k(TW w))-nsh(dpow k(TW w)))%nat=h) by lia.
  rewrite HE in Hbound.
  assert (Hpow:(npow h=2*npow(S(h-2)))%N).
  { replace h with (S(S(h-2))) at 1 by lia; reflexivity. }
  rewrite Hpow in Hbound.
  apply chi_length_le; unfold lb_m; change (1<=cap(dpow k(TW w))/2<npow(S(h-2)))%N; lia.
Qed.

Lemma prefix_energy w k r : (4<=r)%nat ->
  erun(lb_prefix w k r) 0=4*estep(lb_digit w k)(etrun w 0 0)-2.
Proof.
  intro Hr; unfold lb_prefix,lb_buffer,lb_base.
  rewrite erun_app,erun_buffer by exact Hr.
  rewrite erun_app; cbn [erun]; rewrite <-etrun_eq_erun_qw; reflexivity.
Qed.
Lemma return_energy w k r : ZInv w k r ->0<=erun(lb_word w k r) 0.
Proof.
  intros HI; destruct (zinv_height _ _ _ HI) as [h [HH [Hh [HB HF]]]].
  unfold lb_word; rewrite erun_app.
  apply erun_pops_nonneg; [apply chi_pops|].
  rewrite prefix_energy by (exact (zinv_right _ _ _ HI)).
  apply (drain_energy _ h); [exact Hh|exact HF| |apply lb_digit_cases].
  apply return_chi_bound; [exact (zinv_counter _ _ _ HI)|exact HH|exact Hh].
Qed.

(** First reach the exact deposited word, then strip its final V. This
    physical first step makes the eventual whole return strictly positive. *)
Lemma initial_return w k r : ZInv w k r ->
  zCfg(dpow k(tw w)) r -->+ sweep(dpow 0(tw(lb_word w k r))) 2.
Proof.
  intro HI; pose proof (zinv_counter _ _ _ HI) as Hcounter.
  pose proof (zinv_right _ _ _ HI) as Hright.
  destruct (dpow_TW_facts w k ltac:(lia)) as [HA [HG [HC [HB [HP HH]]]]].
  destruct (dpow_TW_facts w (k+2)%N ltac:(lia)) as [HA2 [HG2 [HC2 [HB2 [HP2 HH2]]]]].
  change (Adm(dpow k(tw w))) in HA.
  change (Good(dpow k(tw w))) in HG.
  change (pdec(dpow(k+2)(tw w))=qw w 0) in HP2.
  change (Z.of_N(cap(dpow k(tw w)))=rrun w 0-Z.of_N k) in HC.
  assert (Hcap:(2<=cap(dpow k(tw w)))%N) by lia.
  set (s:=W::dpow(k+2)(tw w)).
  assert (HAs:Adm s).
  { unfold s; rewrite <-two_debts,<-cdec_W by exact Hcap.
    apply cdec_adm,adm_W; [exact HA|pose proof (capacity_two_bits _ HA Hcap); lia]. }
  assert (HGs:Good s).
  { unfold s; rewrite <-two_debts,<-cdec_W by exact Hcap.
    apply good_paid_W; assumption. }
  assert (Hcs:(cap s+1=lb_m w k)%N).
  { unfold s,lb_m; cbn [cap]; rewrite <-two_debts,cap_cdec_twice by exact Hcap; lia. }
  assert (Hm:(0<lb_m w k)%N) by (unfold lb_m; lia).
  assert (Hps:pdec s=qw w 0++[lb_digit w k]).
  { unfold s,lb_digit; cbn [pdec]; now rewrite HP2. }
  assert (EW:tail_word s r=lb_word w k r++[V]).
  { unfold tail_word; rewrite Hps,Hcs,chi_two_pow by exact Hm.
    unfold lb_word,lb_prefix,lb_base,lb_buffer; rewrite <-!app_assoc; reflexivity. }
  destruct (exact_tail (Some(S0,L,B)) s r HAs (tail_bound_of_good s HGs) ltac:(lia))
    as [HW [HS HR]].
  rewrite EW in HR.
  eapply progress_trans.
  - pose proof (z_depart (dpow k(tw w)) r Hcap) as HR0.
    rewrite two_debts in HR0; exact HR0.
  - eapply progress_trans; [exact HR|].
    change (sweep(tw(lb_word w k r++[V])) 1 -->+ sweep(tw(lb_word w k r)) 2).
    rewrite tw_snoc; cbn [tstep]; apply sweep_X.
Qed.

Lemma buffer_scan pre s n j :
  Z.of_N n<=erun(pre++lb_buffer(s+4)) 0 ->
  let count:=(npow s*(n+6))%N in
  sweep(dpow n(tw(pre++lb_buffer(s+4)))) j -->*
    zCfg(dpow(count-1)(tw(pre++repeat Y(s+2)))) (j+(s+3)+2)%nat /\
  Z.of_N(count-1)<=erun(pre++repeat Y(s+2)) 0.
Proof.
  intro HE; cbn zeta.
  set (count:=(npow s*(n+6))%N).
  assert (HC:(6<=count)%N).
  { unfold count; pose proof (BB25FamilyCore.pow2_pos s); nia. }
  assert (EP:(npow(s+3)*(n+6)-6=8*count-6)%N).
  { replace (s+3)%nat with (S(S(S s))) by lia; cbn [npow]; unfold count; nia. }
  unfold lb_buffer in HE |- *.
  replace (s+4-1)%nat with (s+3)%nat in * by lia.
  rewrite !app_assoc in HE |- *.
  destruct (scan_Drun (s+3) ((pre++repeat Y(s+4))++[V]) n j HE)
    as [HR1 HE1].
  rewrite EP in HR1,HE1.
  destruct (scan_V_even (pre++repeat Y(s+4)) (8*count-6)%N (j+(s+3))
    ltac:(lia) HE1) as [HR2 HE2].
  replace ((8*count-6)/2)%N with (4*count-3)%N in HR2,HE2 by lia.
  assert (EY4:repeat Y(s+4)=repeat Y(s+3)++[Y]).
  { replace (s+4)%nat with (S(s+3)) by lia; apply repeat_cons. }
  rewrite EY4,app_assoc in HE2,HR2.
  destruct (scan_Y_odd (pre++repeat Y(s+3)) (4*count-3)%N (S(j+(s+3)))
    ltac:(lia) HE2) as [HR3 HE3].
  replace ((4*count-3-1)/2)%N with (2*count-2)%N in HR3,HE3 by lia.
  assert (EY3:repeat Y(s+3)=repeat Y(s+2)++[Y]).
  { replace (s+3)%nat with (S(s+2)) by lia; apply repeat_cons. }
  rewrite EY3,app_assoc in HE3,HR3.
  destruct (scan_Y_even (pre++repeat Y(s+2)) (2*count-2)%N (S(S(j+(s+3))))
    ltac:(lia) HE3) as [EC HE4].
  replace ((2*count-2)/2)%N with (count-1)%N in EC,HE4 by lia.
  split; [|exact HE4].
  replace (j+(s+3)+2)%nat with (S(S(j+(s+3)))) by lia.
  rewrite <-EC; eapply evstep_trans; [exact HR1|].
  rewrite EY4,app_assoc.
  apply progress_evstep; eapply progress_trans; [exact HR2|].
  rewrite EY3,app_assoc; exact HR3.
Qed.

Lemma invariant_close v k r : DyckPre v ->
  4<=bal([Y;Y;Y]++v) ->6<=ht([Y;Y;Y]++v) ->
  Z.of_N k<=erun([Y;Y;Y]++v) 0 ->
  Z.of_N k+2<=rrun([Y;Y;Y]++v) 0 ->(4<=r)%nat ->
  ZInv ([Y;Y;Y]++v) k r.
Proof.
  intros HD HB HH HE HC HR; constructor; auto.
  - exists v; auto.
  - now apply height_close.
Qed.

Lemma qw_protected v : qw([Y;Y;Y]++v) 0=[Y;Y;Y]++qw v 7.
Proof. rewrite qw_app; reflexivity. Qed.

Lemma buffer_has_D r : (4<=r)%nat ->In D(lb_buffer r).
Proof.
  intro Hr; unfold lb_buffer; apply in_or_app; right; apply in_or_app; right.
  destruct (r-1)%nat eqn:Er; [lia|cbn; auto].
Qed.

Definition entry_word : list digit := [Y;Y;Y;Y;Y].
Lemma entry_paid : dpow 9 (tw entry_word)=entry_core.
Proof. reflexivity. Qed.
Lemma entry_invariant : ZInv entry_word 9 7.
Proof.
  constructor.
  - exists [Y;Y]; split; [reflexivity|apply dyck_Y,dyck_Y,dyck_nil].
  - vm_compute; discriminate.
  - vm_compute; discriminate.
  - exists 5%nat; split; [reflexivity|split; [lia|split; vm_compute; discriminate]].
  - lia.
Qed.

Definition ZReturn : Prop := forall w k r, ZInv w k r ->
  exists w' k' r',
    zCfg(dpow k(tw w)) r -->+ zCfg(dpow k'(tw w')) r' /\ ZInv w' k' r'.

Theorem zinv_return : ZReturn.
Proof.
  intros w k r HI.
  destruct (zinv_protected _ _ _ HI) as [v [Ew HD]].
  destruct (zinv_height _ _ _ HI) as [h [HH [Hh [HB HF]]]].
  pose proof (zinv_right _ _ _ HI) as Hr.
  pose proof (return_chi_bound w k h (zinv_counter _ _ _ HI) HH Hh) as Hlen.
  assert (HHv:ht v=Z.of_nat h-3).
  { rewrite Ew in HH; change (ht v+1+1+1=Z.of_nat h) in HH; lia. }
  pose proof (lb_digit_cases w k) as Hd.
  pose proof (initial_return w k r HI) as HR0.
  assert (HE:Z.of_N 0<=erun(lb_prefix w k r++chi(lb_m w k)) 0)
    by (apply return_energy; exact HI).
  destruct (scan_pops (chi(lb_m w k)) (chi_pops _) (lb_prefix w k r) 0 2 HE)
    as [[eta [tail [debt [Et [HE1 [Hpar [Hz HR1]]]]]]]|[n1 [HE1 [Hbound HR1]]]].
  - specialize (Hz eq_refl).
    assert (HP:Pops eta).
    { intros b Hb; apply (chi_pops (lb_m w k) b); rewrite Et; apply in_or_app; auto. }
    assert (HL:(List.length eta+5<=h)%nat).
    { rewrite Et,List.length_app in Hlen; cbn [List.length] in Hlen; lia. }
    destruct (protected_pop_stop v (lb_digit w k) r eta h HD HHv Hh Hr Hd HP HL)
      as [HD' [HB' HH']].
    set (v':=qw v 7++[lb_digit w k]++lb_buffer r++eta).
    assert (Enew:lb_prefix w k r++eta=[Y;Y;Y]++v').
    { unfold lb_prefix,lb_base,v'; rewrite Ew,qw_protected; rewrite <-!app_assoc; reflexivity. }
    assert (Hmargin:erun(lb_prefix w k r++eta) 0+2<=rrun(lb_prefix w k r++eta) 0).
    { apply erun_add_two_le_rrun; [|lia].
      apply in_or_app; left; unfold lb_prefix; apply in_or_app; right.
      apply buffer_has_D; exact Hr. }
    exists (lb_prefix w k r++eta),debt,(2+List.length tail)%nat.
    split.
    + eapply progress_evstep_trans; [exact HR0|exact HR1].
    + rewrite Enew; apply invariant_close.
      * exact HD'.
      * exact HB'.
      * exact HH'.
      * rewrite <-Enew; exact HE1.
      * rewrite <-Enew; lia.
      * lia.
  - set (s:=(r-4)%nat).
    assert (Er:r=(s+4)%nat) by (unfold s; lia).
    assert (HEbuf:Z.of_N n1<=erun(lb_base w k++lb_buffer(s+4)) 0).
    { rewrite <-Er; exact HE1. }
    destruct (buffer_scan (lb_base w k) s n1 (2+List.length(chi(lb_m w k))) HEbuf)
      as [HR2 HE2].
    set (count:=(npow s*(n1+6))%N) in *.
    assert (Hn:Z.of_N n1+6<=6*zpow(List.length(chi(lb_m w k)))).
    { apply N2Z.inj_le in Hbound.
      rewrite N2Z.inj_add,N2Z.inj_mul,pow2_of_N in Hbound.
      change (Z.of_N n1+6<=zpow(List.length(chi(lb_m w k)))*6) in Hbound; lia. }
    pose proof (buffer_counter (trun w 0 0) h (List.length(chi(lb_m w k)))
      n1 (lb_digit w k) Hh HB Hlen Hn Hd) as HC0.
    assert (Ec:Z.of_N count=zpow s*(Z.of_N n1+6)).
    { unfold count; rewrite N2Z.inj_mul,N2Z.inj_add,pow2_of_N; reflexivity. }
    pose proof (counter_close count n1 s (rstep(lb_digit w k)(trun w 0 0)) Ec HC0) as HC1.
    assert (HC:Z.of_N(count-1)+2<=rrun(lb_base w k++repeat Y(s+2)) 0).
    { unfold lb_base; rewrite !rrun_app,rrun_repeat_Y.
      change (Z.of_N(count-1)+2<=zpow(s+2)*(rstep(lb_digit w k)(rrun(qw w 0) 0)+1)-1).
      rewrite <-trun_eq_rrun_qw; exact HC1. }
    destruct (protected_buffer_stop v (lb_digit w k) s h HD HHv Hh Hd)
      as [HD' [HB' HH']].
    set (v':=qw v 7++[lb_digit w k]++repeat Y(s+2)).
    assert (Enew:lb_base w k++repeat Y(s+2)=[Y;Y;Y]++v').
    { unfold lb_base,v'; rewrite Ew,qw_protected; rewrite <-!app_assoc; reflexivity. }
    exists (lb_base w k++repeat Y(s+2)),(count-1)%N,
      (2+List.length(chi(lb_m w k))+(s+3)+2)%nat.
    split.
    + eapply progress_evstep_trans; [exact HR0|].
      eapply evstep_trans; [exact HR1|].
      rewrite <-Er in HR2; exact HR2.
    + rewrite Enew; apply invariant_close.
      * exact HD'.
      * exact HB'.
      * exact HH'.
      * rewrite <-Enew; exact HE2.
      * rewrite <-Enew; exact HC.
      * lia.
Qed.

Lemma nonhalt_of_zreturn : ZReturn ->~halts lb0 c0.
Proof.
  intro Hreturn.
  eapply multistep_nonhalt; [apply entry_run|].
  rewrite <-entry_paid.
  apply (progress_nonhalt lb0
    (fun c=>exists w k r,ZInv w k r /\ c=zCfg(dpow k(tw w)) r)).
  - intros c [w [k [r [HI ->]]]].
    destruct (Hreturn w k r HI) as [w' [k' [r' [HR HI']]]].
    exists (zCfg(dpow k'(tw w')) r'); split; [|exact HR].
    exists w',k',r'; split; [exact HI'|reflexivity].
  - exists entry_word,9%N,7%nat; split; [exact entry_invariant|reflexivity].
Qed.

End BB25FamilyLB0.

Module TM_0LB.
Definition tm := Eval compute in (TM_from_str "1RB2LA0RB1LB---_1LA3RA1RA4LB0LB").
Theorem nonhalt : ~halts tm c0.
Proof. apply BB25FamilyLB0.nonhalt_of_zreturn,BB25FamilyLB0.zinv_return. Qed.
End TM_0LB.

(* BB25FamilyRBScan.v *)
Close Scope Z_scope. Close Scope N_scope.
From Coq Require Import List NArith ZArith Lia.
Import ListNotations BB25FamilyWord.
Open Scope Z_scope.

Module BB25FamilyRBScan.

(** Reverse debts are binary naturals. The only unary quantities below are
    lengths and counts of letters in a finite word. *)
Fixpoint scanRev (w:list digit) (n:N) (a:Z) (Q:N->Prop) : Prop :=
  match w with
  | [] => Q n
  | Y::w => (n mod 2=0)%N \/ ((n mod 2=1)%N /\ scanRev w ((n-1)/2)%N a Q)
  | V::w => (n mod 2=1)%N \/ ((n mod 2=0)%N /\ scanRev w (n/2)%N a Q)
  | D::w => 2*Z.of_N n+4<=rrun (rev w) a /\ scanRev w (2*n+4)%N a Q
  end.
Definition Scan w n a Q := scanRev (rev w) n a Q.

Lemma Scan_nil n a Q : Scan [] n a Q <-> Q n.
Proof. reflexivity. Qed.
Lemma Scan_snoc_Y w n a Q : Scan (w++[Y]) n a Q <->
  (n mod 2=0)%N \/ ((n mod 2=1)%N /\ Scan w ((n-1)/2)%N a Q).
Proof. unfold Scan; rewrite rev_app_distr; reflexivity. Qed.
Lemma Scan_snoc_V w n a Q : Scan (w++[V]) n a Q <->
  (n mod 2=1)%N \/ ((n mod 2=0)%N /\ Scan w (n/2)%N a Q).
Proof. unfold Scan; rewrite rev_app_distr; reflexivity. Qed.
Lemma Scan_snoc_D w n a Q : Scan (w++[D]) n a Q <->
  2*Z.of_N n+4<=rrun w a /\ Scan w (2*n+4)%N a Q.
Proof. unfold Scan; rewrite rev_app_distr; cbn [rev app scanRev]; now rewrite rev_involutive. Qed.

Lemma scanRev_mono w n a (Q Q':N->Prop) :
  (forall m,Q m->Q' m) ->scanRev w n a Q ->scanRev w n a Q'.
Proof.
  revert n; induction w as [|b w IH]; intros n HQ; cbn [scanRev]; [apply HQ|].
  destruct b; cbn [scanRev]; intros H; intuition eauto.
Qed.
Lemma Scan_mono w n a (Q Q':N->Prop) :
  (forall m,Q m->Q' m) ->Scan w n a Q ->Scan w n a Q'.
Proof. apply scanRev_mono. Qed.
Lemma Scan_of_stops w n a Q : Scan w n a (fun _=>False) ->Scan w n a Q.
Proof. apply Scan_mono; contradiction. Qed.

(** Exact compositionality: the suffix is scanned over the value of the
    prefix, and its exit condition is the scan of that prefix. *)
Lemma scanRev_app u v n a Q :
  scanRev (u++v) n a Q <->
  scanRev u n (rrun (rev v) a) (fun m=>scanRev v m a Q).
Proof.
  revert n; induction u as [|b u IH]; intro n; [reflexivity|].
  destruct b; cbn [app scanRev]; rewrite ?rev_app_distr,?rrun_app;
    rewrite !IH; reflexivity.
Qed.
Lemma Scan_app u v n a Q :
  Scan (u++v) n a Q <-> Scan v n (rrun u a) (fun m=>Scan u m a Q).
Proof.
  unfold Scan; rewrite rev_app_distr,scanRev_app,rev_involutive; reflexivity.
Qed.

Fixpoint nxw (w:list digit) : nat :=
  match w with []=>O | D::w=>S(nxw w) | _::w=>nxw w end.
Lemma nxw_app u v : nxw(u++v)=(nxw u+nxw v)%nat.
Proof. induction u as [|b u IH]; [reflexivity|destruct b; cbn [app nxw]; rewrite IH; lia]. Qed.
Lemma nxw_Yrun n : nxw(repeat Y n)=O.
Proof. induction n; cbn [repeat nxw]; assumption || reflexivity. Qed.
Lemma nxw_Vrun n : nxw(repeat V n)=O.
Proof. induction n; cbn [repeat nxw]; assumption || reflexivity. Qed.
Lemma nxw_Drun n : nxw(repeat D n)=n.
Proof. induction n; cbn [repeat nxw]; congruence. Qed.

(** Forward credit: with enough initial credit all pops can be paid. *)
Lemma rrun_credit w b : pow2 (S(nxw w))<=b+2 ->
  (b+2)/pow2(nxw w)<=rrun w b+2.
Proof.
  revert b; induction w as [|d w IH]; intros b HB.
  - change ((b+2)/1<=b+2); rewrite Z.div_1_r; lia.
  - pose proof (pow2_pos (nxw w)) as HP.
    destruct d; cbn [nxw rrun rstep] in *.
    + assert (HB0:0<=b) by (rewrite pow2_succ in HB; nia).
      eapply Z.le_trans with (m:=((2*b+1)+2)/pow2(nxw w));
        [apply Z.div_le_mono; [lia|lia]|].
      apply IH; lia.
    + assert (HB0:0<=b) by (rewrite pow2_succ in HB; nia).
      eapply Z.le_trans with (m:=(2*b+2)/pow2(nxw w));
        [apply Z.div_le_mono; [lia|lia]|].
      apply IH; lia.
    + assert (HH:pow2 (S(nxw w))<=b/2+1).
      { rewrite pow2_succ in HB; pose proof (div2_bounds b); lia. }
      rewrite pow2_succ,<-Z.div_div by lia.
      replace ((b+2)/2) with (b/2+1) by
        (pose proof (div2_bounds b); pose proof (div2_bounds (b+2)); lia).
      replace (b/2+1) with ((b/2-1)+2) by lia.
      apply IH; lia.
Qed.

(** The debt crossing a suffix grows only at a D. Forward credit supplies
    each D; its exit debt is bounded by the suffix's number of D letters. *)
Lemma scan_tail s pre a n K Q :
  Z.of_N n+4<=4*pow2 K ->
  pow2 (nxw s+K+2)<=rrun pre a+2 ->
  (forall m,Z.of_N m+4<=4*pow2(K+nxw s)->Scan pre m a Q) ->
  Scan (pre++s) n a Q.
Proof.
  revert n K; induction s using rev_ind; intros n K HN HC HQ.
  - cbn [nxw] in *; rewrite app_nil_r.
    apply HQ; now rewrite Nat.add_0_r.
  - rewrite nxw_app in HC,HQ; rewrite app_assoc.
    destruct x; cbn [nxw] in HC,HQ.
    + rewrite Nat.add_0_r in HC,HQ.
      apply Scan_snoc_Y.
      destruct (N.eq_dec (n mod 2) 0) as [HE|HE]; [now left|].
      right; split; [pose proof (N.mod_lt n 2 ltac:(discriminate)) as HM;
        clear - HE HM; generalize dependent (n mod 2)%N; intros z HE HM; lia|].
      apply IHs with K; try assumption.
      assert (((n-1)/2)<=n)%N by (apply N.div_le_upper_bound; lia); lia.
    + rewrite Nat.add_0_r in HC,HQ.
      apply Scan_snoc_V.
      destruct (N.eq_dec (n mod 2) 1) as [HE|HE]; [now left|].
      right; split; [pose proof (N.mod_lt n 2 ltac:(discriminate)) as HM;
        clear - HE HM; generalize dependent (n mod 2)%N; intros z HE HM; lia|].
      apply IHs with K; try assumption.
      assert ((n/2)<=n)%N by (apply N.div_le_upper_bound; lia); lia.
    + apply Scan_snoc_D; split.
      * pose proof (pow2_mono (S(nxw s)) (nxw s+1+K+2) ltac:(lia)) as HP.
        pose proof (rrun_credit s (rrun pre a) ltac:(lia)) as HR.
        assert (HL:pow2(K+3)<=(rrun pre a+2)/pow2(nxw s)).
        { apply Z.div_le_lower_bound; [pose proof (pow2_pos (nxw s)); lia|].
          rewrite <-pow2_add; replace (nxw s+(K+3))%nat with
            (nxw s+1+K+2)%nat by lia; exact HC. }
        rewrite rrun_app.
        replace (K+3)%nat with (S(S(S K))) in HL by lia.
        rewrite !pow2_succ in HL; lia.
      * apply IHs with (S K).
        -- rewrite N2Z.inj_add,N2Z.inj_mul; cbn [Z.of_N]; rewrite pow2_succ; lia.
        -- replace (nxw s+S K+2)%nat with (nxw s+1+K+2)%nat by lia; exact HC.
        -- intros m HM; apply HQ.
           replace (K+(nxw s+1))%nat with (S K+nxw s)%nat by lia; exact HM.
Qed.

Lemma scan_Yrun L n a Q : (1<=L)%nat ->Z.of_N n+2<=pow2 L ->
  Scan (repeat Y L) n a Q.
Proof.
  revert n; induction L as [|L IH]; intros n HL HN; [lia|].
  replace (repeat Y (S L)) with (repeat Y L++[Y]) by (symmetry; apply repeat_cons).
  apply Scan_snoc_Y.
  destruct (N.eq_dec (n mod 2) 0) as [HE|HE]; [now left|].
  right; split; [pose proof (N.mod_lt n 2 ltac:(discriminate)) as HM;
    clear - HE HM; generalize dependent (n mod 2)%N; intros z HE HM; lia|].
  destruct L as [|L].
  - change (Z.of_N n+2<=2) in HN.
    assert (n=0%N) by lia; subst n; contradiction.
  -
  apply IH; [lia|].
  rewrite pow2_succ in HN.
  assert (HN0:n<>0%N) by (intro E; subst n; apply HE; reflexivity).
  assert (EN:Z.of_N((n-1)/2)=(Z.of_N n-1)/2).
  { rewrite N2Z.inj_div.
    rewrite N2Z.inj_sub by lia; reflexivity. }
  rewrite EN; pose proof (div2_bounds (Z.of_N n-1)); lia.
Qed.

Theorem scan_leading_run L s a : 0<=a ->(nxw s+2<=L)%nat ->
  Scan (repeat Y L++s) 0 a (fun _=>False).
Proof.
  intros HA HL; pose proof (pow2_mono (nxw s+2) L HL) as HP.
  pose proof (pow2_pos L) as HP0.
  apply (scan_tail s (repeat Y L) a 0 O); [change (4<=4); lia| |].
  - rewrite rrun_repeat_Y; replace (nxw s+0+2)%nat with (nxw s+2)%nat by lia; nia.
  - intros m HM; apply scan_Yrun; [lia|].
    change (Z.of_N m+4<=4*pow2(nxw s)) in HM.
    replace (nxw s+2)%nat with (S(S(nxw s))) in HP by lia.
    rewrite !pow2_succ in HP; lia.
Qed.

Theorem rrun_pos_leading_run L s a : 0<=a ->(nxw s+2<=L)%nat ->
  2<=rrun(repeat Y L++s) a.
Proof.
  intros HA HL; set (b:=rrun(repeat Y L) a).
  assert (HB:pow2(nxw s+2)<=b+2).
  { unfold b; rewrite rrun_repeat_Y.
    pose proof (pow2_mono (nxw s+2) L HL); pose proof (pow2_pos L); nia. }
  pose proof (pow2_mono (S(nxw s)) (nxw s+2) ltac:(lia)) as HP.
  pose proof (rrun_credit s b ltac:(lia)) as HR.
  assert (HD:4<=(b+2)/pow2(nxw s)).
  { apply Z.div_le_lower_bound; [pose proof (pow2_pos (nxw s)); lia|].
    replace (nxw s+2)%nat with (S(S(nxw s))) in HB by lia.
    rewrite !pow2_succ in HB; lia. }
  rewrite rrun_app; change (2<=rrun s b); lia.
Qed.

End BB25FamilyRBScan.

(* BB25FamilyRBReady.v *)
Close Scope Z_scope. Close Scope N_scope.
From Coq Require Import List NArith ZArith Lia.
Import ListNotations BB25FamilyCore BB25FamilyWord
  BB25FamilyStack BB25FamilyReset
  BB25FamilyExact BB25FamilyReady
  BB25FamilyRBScan.

Module BB25FamilyRBReady.
Open Scope N_scope.

(** The source's unguarded parity formulas are false for a saturated cdec.
    All four bit cases below retain the exact affordable-debt hypothesis. *)
Lemma ready_dpow_Z_even s n : n<=cap(Z::s) ->n mod 2=0 ->
  Ready(dpow n (Z::s)).
Proof.
  intros HC HE; cbn [cap] in HC.
  pose proof (N.div_mod n 2 ltac:(discriminate)) as HD.
  assert (EN:n=2*(n/2)) by lia.
  rewrite EN,dpow_Z_even by lia; apply ready_Z.
Qed.
Lemma ready_dpow_Z_odd s n : n<=cap(Z::s) ->n mod 2=1 ->
  Ready(dpow ((n-1)/2) s) ->Ready(dpow n (Z::s)).
Proof.
  intros HC HE HR; cbn [cap] in HC.
  pose proof (N.div_mod n 2 ltac:(discriminate)) as HD.
  pose proof (N.div_mod (n-1) 2 ltac:(discriminate)) as HD'.
  pose proof (N.mod_lt (n-1) 2 ltac:(discriminate)) as HM.
  assert (EN:n=2*((n-1)/2)+1) by lia.
  rewrite EN,dpow_Z_odd by lia; now apply ready_X.
Qed.
Lemma ready_dpow_X_odd s n : n<=cap(X::s) ->n mod 2=1 ->
  Ready(dpow n (X::s)).
Proof.
  intros HC HE; cbn [cap] in HC.
  pose proof (N.div_mod n 2 ltac:(discriminate)) as HD.
  assert (EN:n=2*(n/2)+1) by lia.
  rewrite EN,dpow_X_odd by lia; apply ready_Z.
Qed.
Lemma ready_dpow_X_even s n : n<=cap(X::s) ->n mod 2=0 ->
  Ready(dpow (n/2) s) ->Ready(dpow n (X::s)).
Proof.
  intros HC HE HR; cbn [cap] in HC.
  pose proof (N.div_mod n 2 ltac:(discriminate)) as HD.
  assert (EN:n=2*(n/2)) by lia.
  rewrite EN,dpow_X_even by lia; now apply ready_X.
Qed.
Lemma ready_dpow_pop s n : 2*n+4<=cap s ->Ready(dpow (2*n+4) s) ->
  Ready(dpow n (cdec(W::s))).
Proof.
  intros HC HR; rewrite cdec_W by lia.
  change (Ready(dpow n (W::dpow 2 s))).
  rewrite dpow_W by (rewrite dpow_cap by lia; lia).
  rewrite <-dpow_add.
  apply ready_W.
  - rewrite dpow_cap by lia; lia.
  - change (Ready(dpow 2 (dpow (2*n+2) s))).
    rewrite <-dpow_add.
    replace (2+(2*n+2)) with (2*n+4) by lia; exact HR.
Qed.

Open Scope Z_scope.

(** Readiness from a reverse scan over any admissible good base. The extra
    budget bound is propagated at each bit and supplied explicitly at a pop. *)
Theorem ready_scan w s n Q : Adm s ->Good s ->
  0<=rrun w (Z.of_N(cap s)) ->Z.of_N n<=rrun w (Z.of_N(cap s)) ->
  Scan w n (Z.of_N(cap s)) Q ->
  (forall m,Q m->Ready(dpow m s)) ->Ready(dpow n (tfold s w)).
Proof.
  revert s n; induction w using rev_ind; intros s n HA HG HC HN HS HQ.
  - apply HQ; exact HS.
  - assert (HC':0<=rrun w (Z.of_N(cap s))) by
      (eapply rrun_nonneg_of_nonneg; exact HC).
    destruct (tfold_props w s HA HG HC') as [HAt [HGt [EC _]]].
    rewrite rrun_app in HN; rewrite tfold_app.
    destruct x.
    + change (Ready(dpow n (Z::tfold s w))).
      assert (HD:(n<=cap(Z::tfold s w))%N).
      { cbn [cap]; change (Z.of_N n<=2*rrun w (Z.of_N(cap s))+1) in HN.
        rewrite <-EC in HN; lia. }
      apply Scan_snoc_Y in HS; destruct HS as [HE|[HE HS]].
      * now apply ready_dpow_Z_even.
      * apply ready_dpow_Z_odd; try assumption.
        apply IHw; try assumption.
        rewrite <-EC.
        assert (((n-1)/2)<=cap(tfold s w))%N.
        { apply N.div_le_upper_bound; cbn [cap] in HD; lia. }
        lia.
    + change (Ready(dpow n (X::tfold s w))).
      assert (HD:(n<=cap(X::tfold s w))%N).
      { cbn [cap]; change (Z.of_N n<=2*rrun w (Z.of_N(cap s))) in HN.
        rewrite <-EC in HN; lia. }
      apply Scan_snoc_V in HS; destruct HS as [HE|[HE HS]].
      * now apply ready_dpow_X_odd.
      * apply ready_dpow_X_even; try assumption.
        apply IHw; try assumption.
        rewrite <-EC.
        assert ((n/2)<=cap(tfold s w))%N.
        { apply N.div_le_upper_bound; cbn [cap] in HD; lia. }
        lia.
    + change (Ready(dpow n (cdec(W::tfold s w)))).
      apply Scan_snoc_D in HS; destruct HS as [HB HS].
      apply ready_dpow_pop.
      * rewrite <-EC in HB; lia.
      * apply IHw; try assumption.
        rewrite N2Z.inj_add,N2Z.inj_mul; exact HB.
Qed.

Corollary ready_tfold_of_stops w s : Adm s ->Good s ->
  0<=rrun w (Z.of_N(cap s)) ->
  Scan w 0 (Z.of_N(cap s)) (fun _=>False) ->Ready(tfold s w).
Proof.
  intros HA HG HC HS.
  apply (ready_scan w s 0 (fun _=>False)); auto; contradiction.
Qed.

Corollary ready_leading_run L w s : Adm s ->Good s ->(nxw w+2<=L)%nat ->
  Ready(tfold s (repeat Y L++w)).
Proof.
  intros HA HG HL; apply ready_tfold_of_stops; try assumption.
  - pose proof (rrun_pos_leading_run L w (Z.of_N(cap s)) ltac:(lia) HL); lia.
  - apply scan_leading_run; lia.
Qed.

End BB25FamilyRBReady.

(* BB25FamilyRBGen.v *)
Close Scope Z_scope. Close Scope N_scope.
From Coq Require Import List NArith ZArith Lia ZifyNat.
Import ListNotations BB25FamilyCore
  BB25FamilyWord BB25FamilyDrainWord.

(** Source RB/Gen.lean and the value portion of RB/Gap.lean.  Source X is D;
    counts are structural nat, values Z, and kword is the frozen drain word. *)
Module BB25FamilyRBGen.
Open Scope Z_scope.
Definition h0 (r:nat) : nat := if Nat.eqb r 3 then 2%nat else 1%nat.
Definition w0 (r:nat) : list digit :=
  match r with
  | 2%nat=>[Y;D;Y;Y;V]
  | 3%nat=>[Y;Y;V;Y;Y;V]
  | _=>Y::kword(r-2)
  end.
Lemma w0_two : w0 2=[Y;D;Y;Y;V]. Proof. reflexivity. Qed.
Lemma w0_three : w0 3=[Y;Y;V;Y;Y;V]. Proof. reflexivity. Qed.
Lemma w0_big k : w0(k+4)=Y::kword(k+2).
Proof.
  replace (k+4)%nat with (S(S(S(S k)))) by lia.
  change (Y::kword(S(S k))=Y::kword(k+2)). f_equal; f_equal; lia.
Qed.
Lemma h0_big k : h0(k+4)=1%nat.
Proof. unfold h0; destruct (Nat.eqb_spec (k+4) 3); lia. Qed.

Inductive Gen : list digit ->nat ->Prop :=
| gen_base r : (2<=r)%nat ->Gen(w0 r)(h0 r)
| gen_pre w h : Gen w h ->Gen(Y::w)(S h)
| gen_mark w h : Gen w h ->Gen(Y::(w++repeat D h++[V])) O.

Lemma rrun_Drun_val n v : rrun(repeat D n) v+2=(v+2)/pow2 n.
Proof.
  revert v; induction n as [|n IH]; intro v.
  - change (v+2=(v+2)/1); now rewrite Z.div_1_r.
  - cbn [repeat rrun rstep]; rewrite IH,pow2_succ.
    replace (v/2-1+2) with ((v+2)/2) by lia.
    rewrite Z.div_div by (pose proof (pow2_pos n); lia); reflexivity.
Qed.
Lemma rrun_core a : rrun [V;Y;Y;V;D] a=8*a+2.
Proof. cbn [rrun rstep]; lia. Qed.
Lemma rrun_kword_gen m a :
  rrun(kword(S m)) a=pow2(2*m+4)*(a+1)-3*pow2(S m).
Proof.
  unfold kword; replace (S m-1)%nat with m by lia.
  rewrite !rrun_app,rrun_repeat_Y,rrun_core,rrun_repeat_V,pow2_succ.
  assert (EP:pow2(2*m+4)=pow2 m*(pow2 m*16)).
  { replace (2*m+4)%nat with ((m+m)+4)%nat by lia.
    rewrite !pow2_add; change (pow2 m*pow2 m*16=pow2 m*(pow2 m*16)); ring. }
  rewrite EP; ring.
Qed.
Lemma rrun_w0_big k a : rrun(w0(k+4)) a=
  pow2(2*k+7)*(a+1)-3*pow2(k+2).
Proof.
  rewrite w0_big. replace (k+2)%nat with (S(S k)) by lia.
  change (rrun(kword(S(S k))) (2*a+1)=
    pow2(2*k+7)*(a+1)-3*pow2(S(S k))).
  rewrite rrun_kword_gen.
  assert (EP:pow2(2*k+7)=pow2(2*S k+4)*2).
  { replace (2*k+7)%nat with (S(2*S k+4)) by lia; rewrite pow2_succ; ring. }
  rewrite EP; ring.
Qed.
Lemma rrun_w0_two a : rrun(w0 2) a=8*a-2.
Proof. rewrite w0_two; cbn [rrun rstep]; lia. Qed.
Lemma rrun_w0_three a : rrun(w0 3) a=64*a+54.
Proof. rewrite w0_three; cbn [rrun rstep]; ring. Qed.

Lemma buffer_value w h a : pow2(S h)*(2*a)<=rrun w a+2 ->
  4*a-2<=rrun(w++repeat D h) a.
Proof.
  intro H; rewrite rrun_app.
  pose proof (rrun_Drun_val h (rrun w a)) as HV.
  pose proof (pow2_pos h) as HP.
  pose proof (Z.div_le_mono _ _ (pow2 h) ltac:(lia) H) as HD.
  rewrite pow2_succ in HD.
  replace (2*pow2 h*(2*a)) with ((4*a)*pow2 h) in HD by ring.
  rewrite Z.div_mul in HD by lia; lia.
Qed.
Theorem gen_rrun_lb w h : Gen w h ->forall a, 0<=a ->
  pow2(S h)*(2*a)<=rrun w a+2.
Proof.
  intro HG; induction HG as [r Hr|w h HG IH|w h HG IH]; intros a Ha.
  - destruct r as [|[|[|[|k]]]]; try lia.
    + rewrite rrun_w0_two; change (4*(2*a)<=8*a-2+2); lia.
    + rewrite rrun_w0_three; change (8*(2*a)<=64*a+54+2); lia.
    + replace (S(S(S(S k)))) with (k+4)%nat by lia.
      rewrite rrun_w0_big,h0_big.
      assert (EP:pow2(2*k+7)=pow2 k*pow2 k*128).
      { replace (2*k+7)%nat with ((k+k)+7)%nat by lia; rewrite !pow2_add; reflexivity. }
      assert (EP':3*pow2(k+2)=pow2 k*12).
      { rewrite pow2_add; change (3*(pow2 k*4)=pow2 k*12); ring. }
      rewrite EP,EP'; change (4*(2*a)<=pow2 k*pow2 k*128*(a+1)-pow2 k*12+2).
      pose proof (pow2_pos k) as HP; nia.
  - change (pow2(S(S h))*(2*a)<=rrun w (2*a+1)+2).
    pose proof (IH (2*a+1) ltac:(lia)). rewrite pow2_succ; pose proof (pow2_pos (S h)); nia.
  - pose proof (buffer_value w h (2*a+1) (IH (2*a+1) ltac:(lia))) as HB.
    change (2*(2*a)<=rrun(w++repeat D h++[V]) (2*a+1)+2).
    rewrite app_assoc,rrun_app; change (2*(2*a)<=2*rrun(w++repeat D h) (2*a+1)+2); lia.
Qed.
Theorem gen_rrun_buf w h : Gen w h ->forall a, 0<=a ->
  4*a-2<=rrun(w++repeat D h) a.
Proof. intros HG a Ha; apply buffer_value,gen_rrun_lb; assumption. Qed.
Theorem gen_rrun_buf' w h : Gen w h ->forall a, 0<=a ->
  2*a-2<=rrun(w++repeat D (h+1)) a.
Proof.
  intros HG a Ha; pose proof (gen_rrun_buf w h HG a Ha) as HB.
  replace (h+1)%nat with (S h) by lia.
  change (2*a-2<=rrun(w++D::repeat D h) a).
  rewrite repeat_cons,app_assoc,rrun_app.
  change (2*a-2<=rrun(w++repeat D h) a/2-1); lia.
Qed.

(** A finite word's prefix-balance budget, used only for the Dyck proof. *)
Definition DyckAt a w : Prop := forall p s, w=p++s ->0<=a+bal p.
Lemma dyckAt_nil a : 0<=a ->DyckAt a [].
Proof. intros H p s E; destruct p; [cbn; lia|discriminate]. Qed.
Lemma dyckAt_mono a b w : a<=b ->DyckAt a w ->DyckAt b w.
Proof. intros H HD p s E; specialize (HD p s E); lia. Qed.
Lemma dyckAt_cons a b w : 0<=a ->DyckAt(a+bal[b]) w ->DyckAt a (b::w).
Proof.
  intros H HD p s E; destruct p as [|x p]; [cbn; lia|].
  inversion E; subst x. specialize (HD p s H2). destruct b; cbn [bal] in *; lia.
Qed.
Lemma dyckAt_app a w v : DyckAt a w ->DyckAt(a+bal w) v ->DyckAt a (w++v).
Proof.
  intros HW HV p s E.
  destruct (prefix_app_cases p w v (ex_intro _ s E)) as [[q HQ]|[q [-> [r HR]]]].
  - exact (HW p q HQ).
  - specialize (HV q r HR); rewrite bal_app; lia.
Qed.
Lemma dyckAt_Yrun n a : 0<=a ->DyckAt a (repeat Y n).
Proof.
  revert a; induction n as [|n IH]; intros a H; [apply dyckAt_nil; exact H|].
  apply dyckAt_cons; [exact H|apply IH; cbn [bal]; lia].
Qed.
Lemma dyckAt_poprun n a b : (b=D \/ b=V) ->Z.of_nat n<=a ->DyckAt a (repeat b n).
Proof.
  intros Hb; revert a; induction n as [|n IH]; intros a H.
  - apply dyckAt_nil; exact H.
  - apply dyckAt_cons; [lia|apply IH; destruct Hb as [-> | ->]; cbn [bal]; lia].
Qed.
Lemma bal_poprun b n : (b=D \/ b=V) ->bal(repeat b n)= -Z.of_nat n.
Proof.
  intro H; induction n as [|n IH]; [reflexivity|].
  destruct H as [-> | ->]; cbn [repeat bal]; lia.
Qed.
Lemma dyckAt_core a : 1<=a ->DyckAt a [V;Y;Y;V;D].
Proof.
  intro H; do 5 (apply dyckAt_cons; [cbn [bal]; lia|]); apply dyckAt_nil; cbn [bal]; lia.
Qed.
Lemma w0_dyck r : (2<=r)%nat ->DyckAt 0 (w0 r) /\ bal(w0 r)=Z.of_nat(h0 r).
Proof.
  intro Hr; destruct r as [|[|[|[|k]]]]; try lia.
  - split; [|reflexivity].
    change (DyckAt 0 [Y;D;Y;Y;V]).
    do 5 (apply dyckAt_cons; [cbn [bal]; lia|]); apply dyckAt_nil; cbn [bal]; lia.
  - split; [|reflexivity].
    change (DyckAt 0 [Y;Y;V;Y;Y;V]).
    do 6 (apply dyckAt_cons; [cbn [bal]; lia|]); apply dyckAt_nil; cbn [bal]; lia.
  - replace (S(S(S(S k)))) with (k+4)%nat by lia.
    rewrite w0_big,h0_big; unfold kword.
    replace (k+2-1)%nat with (k+1)%nat by lia; split.
    + apply dyckAt_cons; [lia|].
      apply dyckAt_app; [apply dyckAt_Yrun; cbn [bal]; lia|].
      apply dyckAt_app; [apply dyckAt_core; rewrite bal_repeat_Y; cbn [bal]; lia|].
      apply dyckAt_poprun; [auto|rewrite bal_repeat_Y; cbn [bal]; lia].
    + change (bal(repeat Y(k+2)++[V;Y;Y;V;D]++repeat V(k+1))+1=1).
      rewrite !bal_app,bal_repeat_Y,(bal_poprun V (k+1) ltac:(auto)).
      cbn [bal]; lia.
Qed.
Theorem gen_dyck w h : Gen w h ->DyckPre w /\ bal w=Z.of_nat h.
Proof.
  intro HG.
  assert (H:DyckAt 0 w /\ bal w=Z.of_nat h).
  { induction HG as [r Hr|w h HG [HD HB]|w h HG [HD HB]].
    - apply w0_dyck; exact Hr.
    - split; [apply dyckAt_cons; [lia|eapply dyckAt_mono; [|exact HD]; cbn [bal]; lia]|].
      cbn [bal]; lia.
    - split.
      + apply dyckAt_cons; [lia|].
        apply dyckAt_app; [eapply dyckAt_mono; [|exact HD]; cbn [bal]; lia|].
        apply dyckAt_app; [apply dyckAt_poprun; [auto|cbn [bal]; lia]|].
        apply dyckAt_cons; [rewrite (bal_poprun D h ltac:(auto)); cbn [bal]; lia|].
        apply dyckAt_nil; rewrite (bal_poprun D h ltac:(auto)); cbn [bal]; lia.
      + change (bal(w++repeat D h++[V])+1=0).
        rewrite !bal_app,HB,(bal_poprun D h ltac:(auto)); cbn [bal]; lia. }
  destruct H as [HD HB]; split; [intros p s E; specialize (HD p s E); lia|exact HB].
Qed.

End BB25FamilyRBGen.

(* BB25FamilyRBClassify.v *)
Close Scope Z_scope. Close Scope N_scope.
From Coq Require Import List NArith ZArith Lia.
Import ListNotations BB25FamilyWord
  BB25FamilyDrainWord BB25FamilyRBScan
  BB25FamilyRBGen.

Module BB25FamilyRBClassify.
Open Scope nat_scope.

Fixpoint lead (w:list digit) : nat :=
  match w with Y::w=>S(lead w) | _=>O end.
Lemma lead_app w v : lead w<length w ->lead(w++v)=lead w.
Proof.
  induction w as [|b w IH]; [cbn; lia|].
  destruct b; cbn [lead app length]; intro H; [rewrite IH by lia| |]; reflexivity.
Qed.
Lemma lead_Yrun L w : lead(repeat Y L++w)=L+lead w.
Proof. induction L; cbn [repeat app lead]; [lia|rewrite IHL; lia]. Qed.
Lemma lead_split w : w=repeat Y (lead w)++skipn (lead w) w.
Proof.
  induction w as [|b w IH]; [reflexivity|].
  destruct b; cbn [lead repeat app skipn]; [now rewrite <-IH|reflexivity|reflexivity].
Qed.

Definition cD : list digit := [D;Y;Y;V].
Definition cV : list digit := [V;Y;Y;V].
Definition E3 w h := exists k,w=repeat Y (k+1)++cD /\ h=k+1.
Definition E2a w h := exists k,w=repeat Y (k+2)++cV /\ h=k+2.
Definition E2b w h := exists j k,
  w=repeat Y (j+k+2)++(cD++repeat D (k+1)++[V]) /\ h=j.
Definition F5 w := exists k,w=repeat Y (k+3)++(cV++repeat D (k+2)++[V]).
Definition F6 w := exists j k,
  w=repeat Y (j+k+3)++(cD++repeat D (k+1)++[V]++repeat D j++[V]).
Definition Exc w :=
  (exists k,k<=1 /\ w=repeat Y (k+1)++cD) \/
  (exists j k,j<=1 /\ w=repeat Y (j+k+2)++(cD++repeat D (k+1)++[V])) \/
  F5 w \/ F6 w.
Definition Cls w h :=
  nxw w+h+2<=lead w \/
  (nxw w+h+2=lead w+1 /\ (h=0 ->F5 w \/ F6 w)) \/
  (nxw w+h+2=lead w+2 /\ (E2a w h \/ E2b w h)) \/
  (nxw w+h+2=lead w+3 /\ E3 w h).

Lemma w0_big_shape k : w0(k+4)=
  repeat Y (k+3)++[V;Y;Y;V;D]++repeat V (k+1).
Proof.
  rewrite w0_big; unfold kword.
  replace (k+2-1) with (k+1) by lia.
  replace (k+3) with (S(k+2)) by lia; reflexivity.
Qed.
Lemma w0_big_counts k : nxw(w0(k+4))=1 /\ lead(w0(k+4))=k+3 /\
  lead(w0(k+4))<length(w0(k+4)).
Proof.
  rewrite !w0_big_shape,!nxw_app,nxw_Yrun,nxw_Vrun,!lead_Yrun.
  cbn [nxw lead app]; rewrite !length_app,!repeat_length.
  cbn [length]; repeat split; lia.
Qed.

Theorem gen_classify w h : Gen w h ->Cls w h /\ lead w<length w.
Proof.
  intro H; induction H as [r HR|w h H [HC HL]|w h H [HC HL]].
  - destruct r as [|[|[|[|k]]]]; try lia.
    + split; [right; right; right; split; [reflexivity|exists O; split; reflexivity]|].
      change (1<5); lia.
    + split; [right; right; left; split; [reflexivity|left; exists O; split; reflexivity]|].
      change (2<6); lia.
    + replace (S(S(S(S k)))) with (k+4) by lia.
      destruct (w0_big_counts k) as [EN [EL HL]].
      split; [|exact HL]; unfold Cls; rewrite EN,EL,h0_big.
      destruct k as [|k].
      * right; left; split; [lia|discriminate].
      * left; lia.
  - split; [|cbn [lead length]; lia].
    unfold Cls in *; cbn [lead nxw].
    destruct HC as [HC|[[HE HS]|[[HE HS]|[HE HS]]]].
    + left; lia.
    + right; left; split; [lia|discriminate].
    + right; right; left; split; [lia|].
      destruct HS as [[k [EW EH]]|[j [k [EW EH]]]]; subst w h.
      * left; exists (S k); split; [|lia].
        replace (S k+2) with (S(k+2)) by lia; reflexivity.
      * right; exists (S j),k; split; [|reflexivity].
        replace (S j+k+2) with (S(j+k+2)) by lia; reflexivity.
    + right; right; right; split; [lia|].
      destruct HS as [k [EW EH]]; subst w h; exists (S k); split; [|lia].
      replace (S k+1) with (S(k+1)) by lia; reflexivity.
  - assert (EN:nxw(Y::(w++repeat D h++[V]))=nxw w+h).
    { cbn [nxw]; rewrite !nxw_app,nxw_Drun; cbn [nxw]; lia. }
    assert (EL:lead(Y::(w++repeat D h++[V]))=S(lead w)).
    { cbn [lead]; now rewrite lead_app. }
    split.
    2:{ rewrite EL; cbn [length]; rewrite !length_app; lia. }
    unfold Cls in *; rewrite EN,EL.
    destruct HC as [HC|[[HE HS]|[[HE HS]|[HE HS]]]].
    + left; lia.
    + left; lia.
    + right; left; split; [lia|intros _].
      destruct HS as [[k [EW EH]]|[j [k [EW EH]]]]; subst w h.
      * left; exists k.
        replace (k+3) with (S(k+2)) by lia; cbn [repeat app].
        repeat rewrite <-app_assoc; reflexivity.
      * right; exists j,k.
        replace (j+k+3) with (S(j+k+2)) by lia; cbn [repeat app].
        repeat rewrite <-app_assoc; reflexivity.
    + right; right; left; split; [lia|right].
      destruct HS as [k [EW EH]]; subst w h; exists O,k; split; [|reflexivity].
      replace (0+k+2) with (S(k+1)) by lia; cbn [repeat app].
      repeat rewrite <-app_assoc; reflexivity.
Qed.

Theorem gen_lead_or_exc w h : Gen w h ->nxw w+2<=lead w \/ Exc w.
Proof.
  intro HG; destruct (gen_classify w h HG) as [HC _].
  destruct HC as [HC|[[HE HS]|[[HE HS]|[HE HS]]]].
  - left; lia.
  - destruct h; [right; right; right; apply HS; reflexivity|left; lia].
  - destruct HS as [[k [EW EH]]|[j [k [EW EH]]]].
    + left; lia.
    + destruct (le_lt_dec j 1).
      * right; right; left; exists j,k; auto.
      * left; lia.
  - destruct HS as [k [EW EH]]; destruct (le_lt_dec k 1).
    + right; left; exists k; auto.
    + left; lia.
Qed.

End BB25FamilyRBClassify.

(* BB25FamilyRBFamilies.v *)
Close Scope Z_scope. Close Scope N_scope.
From Coq Require Import List NArith ZArith Lia.
Import ListNotations BB25FamilyWord BB25FamilyDrain
  BB25FamilyRBScan BB25FamilyRBGen
  BB25FamilyRBClassify.

Module BB25FamilyRBFamilies.
Open Scope Z_scope.
Notation npow := BB25FamilyCore.pow2.

Lemma mod_zero_of_cast n d z : Z.of_N n=z*Z.of_N d ->d<>0%N ->(n mod d=0)%N.
Proof.
  intros HE HD; apply N2Z.inj; rewrite N2Z.inj_mod,HE.
  rewrite Z.mod_mul by lia; reflexivity.
Qed.
Lemma scan_stop_YV u n a Q : (n mod 4=0)%N ->Scan (u++[Y;V]) n a Q.
Proof.
  intro HM; replace (u++[Y;V]) with ((u++[Y])++[V]) by now rewrite <-app_assoc.
  pose proof (N.div_mod n 4 ltac:(discriminate)) as HD.
  assert (HN:n=(n/4*4)%N) by lia.
  assert (HE:(n mod 2=0)%N).
  { apply (mod_zero_of_cast n 2 (2*Z.of_N(n/4))); [lia|discriminate]. }
  apply Scan_snoc_V; right; split; [exact HE|].
  apply Scan_snoc_Y; left.
  apply (mod_zero_of_cast (n/2) 2 (Z.of_N(n/4))); [|discriminate].
  rewrite N2Z.inj_div; cbn [Z.of_N];
    pose proof (div2_bounds (Z.of_N n)); lia.
Qed.

Lemma scan_Drun c pre n m a Q :
  Z.of_N m+4=pow2 c*(Z.of_N n+4) ->Z.of_N m+4<=rrun pre a+2 ->
  Scan pre m a Q ->Scan (pre++repeat D c) n a Q.
Proof.
  revert n; induction c as [|c IH]; intros n HM HB HS.
  - change (Z.of_N m+4=1*(Z.of_N n+4)) in HM.
    assert (m=n) by lia; subst m; cbn [repeat]; now rewrite app_nil_r.
  - replace (repeat D (S c)) with (repeat D c++[D]) by (symmetry; apply repeat_cons).
    rewrite app_assoc; apply Scan_snoc_D; split.
    + pose proof (pow2_pos c) as HP.
      assert (HC:pow2(S(nxw(repeat D c)))<=rrun pre a+2).
      { rewrite nxw_Drun; rewrite pow2_succ in HM|-*; nia. }
      pose proof (rrun_credit (repeat D c) (rrun pre a) HC) as HR.
      rewrite nxw_Drun in HR.
      assert (HL:2*(Z.of_N n+4)<=(rrun pre a+2)/pow2 c).
      { apply Z.div_le_lower_bound; [lia|rewrite pow2_succ in HM; nia]. }
      rewrite rrun_app; lia.
    + apply (IH (2*n+4)%N); try assumption.
      rewrite N2Z.inj_add,N2Z.inj_mul; cbn [Z.of_N]; rewrite pow2_succ in HM; nia.
Qed.

Definition debt c (n:N) := (npow c*(n+4)-4)%N.
Lemma debt_z c n : Z.of_N(debt c n)+4=pow2 c*(Z.of_N n+4).
Proof.
  pose proof (BB25FamilyCore.pow2_pos c) as HP.
  unfold debt; rewrite N2Z.inj_sub by nia.
  rewrite N2Z.inj_mul,N2Z.inj_add,pow2_of_N; cbn [Z.of_N]; ring.
Qed.
Lemma debt_zero_mod c : (debt c 0 mod 4=0)%N.
Proof.
  apply (mod_zero_of_cast (debt c 0) 4 (pow2 c-1)); [pose proof (debt_z c 0); cbn [Z.of_N] in *; lia|discriminate].
Qed.
Lemma debt_zero_half c : Z.of_N(debt c 0/2)+4=2*pow2 c+2.
Proof.
  rewrite N2Z.inj_div; cbn [Z.of_N].
  pose proof (debt_z c 0); pose proof (div2_bounds (Z.of_N(debt c 0))); cbn [Z.of_N] in *; lia.
Qed.

Lemma rrun_YcD M a : rrun(repeat Y (M+1)++cD) a=pow2(M+3)*(a+1)-10.
Proof.
  rewrite rrun_app,rrun_repeat_Y.
  replace (M+1)%nat with (S M) by lia.
  replace (M+3)%nat with (S(S(S M))) by lia; rewrite !pow2_succ.
  unfold cD; cbn [rrun rstep].
  assert (HE:(2*pow2 M*(a+1)-1)/2=pow2 M*(a+1)-1).
  { pose proof (div2_bounds (2*pow2 M*(a+1)-1)); lia. }
  rewrite HE; ring.
Qed.
Lemma rrun_YcV M a : rrun(repeat Y (M+1)++cV) a=pow2(M+5)*(a+1)-10.
Proof.
  rewrite rrun_app,rrun_repeat_Y.
  replace (M+1)%nat with (S M) by lia.
  replace (M+5)%nat with (S(S(S(S(S M))))) by lia; rewrite !pow2_succ.
  unfold cV; cbn [rrun rstep]; ring.
Qed.
Lemma scan_core u c n m a Q : Z.of_N m+4=pow2 c*(Z.of_N n+4) ->
  (m mod 4=0)%N ->Z.of_N m+4<=rrun(u++[Y;V]) a+2 ->
  Scan ((u++[Y;V])++repeat D c) n a Q.
Proof. intros HM HE HB; apply (scan_Drun c _ n m); auto using scan_stop_YV. Qed.

Lemma scan_fam12 k a Q : Scan (repeat Y (k+1)++cD) 0 a Q.
Proof.
  replace (repeat Y (k+1)++cD) with ((repeat Y (k+1)++[D;Y])++[Y;V])
    by (rewrite <-app_assoc; reflexivity).
  apply scan_stop_YV; reflexivity.
Qed.

Lemma scan_fam34 j k a Q : 0<=a ->
  Scan (repeat Y (j+k+2)++(cD++repeat D (k+1)++[V])) 0 a Q.
Proof.
  intro HA.
  replace (repeat Y (j+k+2)++(cD++repeat D (k+1)++[V])) with
    ((((repeat Y (j+k+2)++[D;Y])++[Y;V])++repeat D (k+1))++[V])
    by (repeat rewrite <-app_assoc; reflexivity).
  apply Scan_snoc_V; right; split; [reflexivity|].
  apply (scan_core _ (k+1) 0 (debt (k+1) 0)); [apply debt_z|apply debt_zero_mod|].
  rewrite debt_z.
  replace ((repeat Y (j+k+2)++[D;Y])++[Y;V]) with
    (repeat Y ((j+k+1)+1)++cD) by
    (replace ((j+k+1)+1)%nat with (j+k+2)%nat by lia; rewrite <-app_assoc; reflexivity).
  rewrite rrun_YcD.
  replace (j+k+1+3)%nat with (j+k+4)%nat by lia.
  pose proof (pow2_mono (k+4) (j+k+4) ltac:(lia)) as HP.
  pose proof (pow2_mono 1 (k+1) ltac:(lia)) as H2; change (2<=pow2(k+1)) in H2.
  pose proof (pow2_pos (j+k+4)) as HL.
  replace (k+4)%nat with (S(S(S(k+1)))) in HP by lia.
  rewrite !pow2_succ in HP; cbn [Z.of_N]; nia.
Qed.

Lemma scan_fam5 k a Q : 0<=a ->
  Scan (repeat Y (k+3)++(cV++repeat D (k+2)++[V])) 0 a Q.
Proof.
  intro HA.
  replace (repeat Y (k+3)++(cV++repeat D (k+2)++[V])) with
    ((((repeat Y (k+3)++[V;Y])++[Y;V])++repeat D (k+2))++[V])
    by (repeat rewrite <-app_assoc; reflexivity).
  apply Scan_snoc_V; right; split; [reflexivity|].
  apply (scan_core _ (k+2) 0 (debt (k+2) 0)); [apply debt_z|apply debt_zero_mod|].
  rewrite debt_z.
  replace ((repeat Y (k+3)++[V;Y])++[Y;V]) with
    (repeat Y ((k+2)+1)++cV) by
    (replace ((k+2)+1)%nat with (k+3)%nat by lia; rewrite <-app_assoc; reflexivity).
  rewrite rrun_YcV.
  replace (k+2+5)%nat with (S(S(S(S(S(k+2)))))) by lia.
  rewrite !pow2_succ; pose proof (pow2_pos (k+2)); cbn [Z.of_N]; nia.
Qed.

Lemma scan_fam6 j k a Q : 0<=a ->
  Scan (repeat Y (j+k+3)++
    (cD++repeat D (k+1)++[V]++repeat D j++[V])) 0 a Q.
Proof.
  intro HA; set (u:=repeat Y (j+k+3)++[D;Y]).
  assert (HV:rrun(u++[Y;V]) a=pow2(j+k+5)*(a+1)-10).
  { unfold u; replace ((repeat Y (j+k+3)++[D;Y])++[Y;V]) with
      (repeat Y ((j+k+2)+1)++cD) by
      (replace ((j+k+2)+1)%nat with (j+k+3)%nat by lia; rewrite <-app_assoc; reflexivity).
    rewrite rrun_YcD; replace (j+k+2+3)%nat with (j+k+5)%nat by lia; reflexivity. }
  pose proof (pow2_mono 2 (j+k+2) ltac:(lia)) as H4.
  change (4<=pow2(j+k+2)) in H4.
  pose proof (pow2_mono (k+2) (j+k+2) ltac:(lia)) as HK.
  pose proof (pow2_pos (j+k+5)) as HP.
  assert (HM:pow2(j+k+5)<=pow2(j+k+5)*(a+1)) by nia.
  assert (EP:pow2(j+k+5)=8*pow2(j+k+2)).
  { replace (j+k+5)%nat with (S(S(S(j+k+2)))) by lia; rewrite !pow2_succ; ring. }
  assert (Eprod:pow2(k+1)*(4*pow2 j)=2*pow2(j+k+2)).
  { replace (j+k+2)%nat with (j+(k+2))%nat by lia; rewrite (pow2_add j (k+2)).
    replace (k+1)%nat with (S k) by lia.
    replace (k+2)%nat with (S(S k)) by lia; rewrite !pow2_succ; ring. }
  assert (Eprod':pow2(k+1)*(2*pow2 j+2)=pow2(j+k+2)+pow2(k+2)).
  { replace (j+k+2)%nat with (j+(k+2))%nat by lia; rewrite (pow2_add j (k+2)).
    replace (k+1)%nat with (S k) by lia.
    replace (k+2)%nat with (S(S k)) by lia; rewrite !pow2_succ; ring. }
  replace (repeat Y (j+k+3)++
    (cD++repeat D (k+1)++[V]++repeat D j++[V])) with
    (((((u++[Y;V])++repeat D (k+1))++[V])++repeat D j)++[V])
    by (unfold u; repeat rewrite <-app_assoc; reflexivity).
  apply Scan_snoc_V; right; split; [reflexivity|].
  apply (scan_Drun j _ 0 (debt j 0)); [apply debt_z| |].
  - assert (HC:pow2(S(nxw(repeat D (k+1)++[V])))<=rrun(u++[Y;V]) a+2).
    { rewrite nxw_app,nxw_Drun; cbn [nxw].
      replace (S(k+1+0)) with (k+2)%nat by lia.
      rewrite HV; lia. }
    pose proof (rrun_credit (repeat D (k+1)++[V]) (rrun(u++[Y;V]) a) HC) as HR.
    rewrite nxw_app,nxw_Drun in HR; cbn [nxw] in HR; rewrite Nat.add_0_r in HR.
    assert (HD:4*pow2 j<=(rrun(u++[Y;V]) a+2)/pow2(k+1)).
    { apply Z.div_le_lower_bound; [pose proof (pow2_pos (k+1)); lia|].
      rewrite Eprod,HV; lia. }
    rewrite debt_z; cbn [Z.of_N].
    rewrite <-app_assoc,rrun_app; nia.
  - apply Scan_snoc_V; right; split.
    + apply (mod_zero_of_cast (debt j 0) 2 (2*pow2 j-2));
        [pose proof (debt_z j 0); cbn [Z.of_N] in *; lia|discriminate].
    + apply (scan_core u (k+1) (debt j 0/2)%N (debt (k+1) (debt j 0/2)%N)).
      * apply debt_z.
      * apply (mod_zero_of_cast _ 4 (pow2 k*(pow2 j+1)-1)); [|discriminate].
        pose proof (debt_z (k+1) (debt j 0/2)%N) as ED.
        rewrite debt_zero_half in ED.
        assert (EK:pow2(k+1)=2*pow2 k).
        { replace (k+1)%nat with (S k) by lia; apply pow2_succ. }
        rewrite EK in ED.
        cbn [Z.of_N]; nia.
      * rewrite debt_z,debt_zero_half,Eprod',HV; lia.
Qed.

Theorem scan_exceptional w a Q : Exc w ->0<=a ->Scan w 0 a Q.
Proof.
  intros [[k [_ ->]]|[[j [k [_ ->]]]|[[k ->]|[j [k ->]]]]] HA;
    auto using scan_fam12,scan_fam34,scan_fam5,scan_fam6.
Qed.

Theorem gen_scan_stops w h a Q : Gen w h ->0<=a ->Scan w 0 a Q.
Proof.
  intros HG HA; destruct (gen_lead_or_exc w h HG) as [HC|HE].
  - pose proof (f_equal nxw (lead_split w)) as EN.
    rewrite nxw_app,nxw_Yrun in EN; cbn [Nat.add] in EN.
    apply Scan_of_stops; rewrite (lead_split w).
    apply scan_leading_run; [exact HA|lia].
  - apply scan_exceptional; assumption.
Qed.

(** Positivity has a shorter direct proof by Gen induction. Prefix and
    marker constructors feed a positive value into the already proved buffer
    bound; only the unextended w0 2 at zero is exceptional. *)
Theorem gen_rrun_pos w h a : Gen w h ->0<=a ->(w<>w0 2 \/ 1<=a) ->
  1<=rrun w a.
Proof.
  intro HG; destruct HG as [r HR|w h HG|w h HG]; intros HA HE.
  - destruct r as [|[|[|[|k]]]]; try lia.
    + destruct HE as [HE|HE]; [contradiction|rewrite rrun_w0_two; lia].
    + rewrite rrun_w0_three; lia.
    + replace (S(S(S(S k)))) with (k+4)%nat by lia.
      rewrite rrun_w0_big.
      assert (EP:pow2(2*k+7)=pow2 k*pow2 k*128).
      { replace (2*k+7)%nat with ((k+k)+7)%nat by lia; rewrite !pow2_add; reflexivity. }
      assert (EP':pow2(k+2)=4*pow2 k).
      { replace (k+2)%nat with (S(S k)) by lia; rewrite !pow2_succ; ring. }
      rewrite EP,EP'; pose proof (pow2_pos k); nia.
  - change (1<=rrun w (2*a+1)).
    pose proof (gen_rrun_lb w h HG (2*a+1) ltac:(lia)) as HB.
    rewrite pow2_succ in HB; pose proof (pow2_pos h); nia.
  - change (1<=rrun(w++repeat D h++[V]) (2*a+1)).
    rewrite app_assoc,rrun_app.
    change (1<=2*rrun(w++repeat D h) (2*a+1)).
    pose proof (gen_rrun_buf w h HG (2*a+1) ltac:(lia)); lia.
Qed.

End BB25FamilyRBFamilies.

(* BB25FamilyRBGap.v *)
Close Scope Z_scope. Close Scope N_scope.
From Coq Require Import List NArith ZArith Lia ZifyNat.
Import ListNotations BB25FamilyCore
  BB25FamilyWord BB25FamilyDrainWord
  BB25FamilyRBGen BB25FamilyRBScan.

Module BB25FamilyRBGap.
Open Scope Z_scope.
Notation npow := BB25FamilyCore.pow2.

Lemma parity n : (n mod 2=0 \/ n mod 2=1)%N.
Proof.
  pose proof (N.mod_lt n 2 ltac:(discriminate)) as H.
  generalize dependent (n mod 2)%N; intros z H; lia.
Qed.
Lemma double_four_even n : ((2*n+4) mod 2=0)%N.
Proof. lia. Qed.
Lemma Scan_append_of p s n a Q :
  Scan s n (rrun p a) (fun m=>Scan p m a Q) ->Scan(p++s) n a Q.
Proof. apply Scan_app. Qed.
Lemma Scan_single_Y n a Q :
  ((n mod 2=1)%N ->Q ((n-1)/2)%N) ->Scan [Y] n a Q.
Proof.
  intro H; change (Scan ([]++[Y]) n a Q); apply Scan_snoc_Y.
  destruct (parity n) as [HE|HE]; [now left|right; split; [exact HE|apply H; exact HE]].
Qed.

Lemma scan_Yrun_gap L n j a Q : (j<=L)%nat ->
  (forall m,(npow j*(m+1)<=n+1)%N ->Q m) ->Scan(repeat Y L) n a Q.
Proof.
  revert n j; induction L as [|L IH]; intros n j HJ HQ.
  - assert (j=O) by lia; subst j; apply Scan_nil,HQ; cbn [npow]; lia.
  - replace (repeat Y (S L)) with (repeat Y L++[Y]) by (symmetry; apply repeat_cons).
    apply Scan_snoc_Y; destruct (parity n) as [HE|HE]; [now left|].
    right; split; [exact HE|].
    destruct j as [|j].
    + apply (IH ((n-1)/2)%N O); [lia|].
      intros m HM; apply HQ; cbn [npow] in *; lia.
    + apply (IH ((n-1)/2)%N j); [lia|].
      intros m HM; apply HQ; change (2*npow j*(m+1)<=n+1)%N.
      assert (2*((n-1)/2)+1=n)%N by lia; nia.
Qed.
Lemma scan_Vrun_gap L n j a Q : (j<=L)%nat ->
  (forall m,(npow j*m<=n)%N ->Q m) ->Scan(repeat V L) n a Q.
Proof.
  revert n j; induction L as [|L IH]; intros n j HJ HQ.
  - assert (j=O) by lia; subst j; apply Scan_nil,HQ; cbn [npow]; lia.
  - replace (repeat V (S L)) with (repeat V L++[V]) by (symmetry; apply repeat_cons).
    apply Scan_snoc_V; destruct (parity n) as [HE|HE]; [|now left].
    right; split; [exact HE|].
    destruct j as [|j].
    + apply (IH (n/2)%N O); [lia|].
      intros m HM; apply HQ; cbn [npow] in *; lia.
    + apply (IH (n/2)%N j); [lia|].
      intros m HM; apply HQ; change (2*npow j*m<=n)%N.
      assert (2*(n/2)=n)%N by lia; nia.
Qed.

Lemma scan_w0_two n a Q : Z.of_N n+4<=4*a-1 ->
  Scan(w0 2++repeat D (h0 2)) n a Q.
Proof.
  intro HN.
  change (Scan ((((([Y]++[D])++[Y])++[Y])++[V])++[D]) n a Q).
  apply Scan_snoc_D; split.
  - change (2*Z.of_N n+4<=rrun(w0 2) a); rewrite rrun_w0_two; lia.
  - apply Scan_snoc_V; right; split; [lia|].
    apply Scan_snoc_Y; destruct (parity ((2*n+4)/2)%N) as [H1|H1]; [now left|].
    right; split; [exact H1|].
    apply Scan_snoc_Y; destruct (parity (((2*n+4)/2-1)/2)%N) as [H2|H2]; [now left|].
    right; split; [exact H2|].
    apply Scan_snoc_D; split.
    + change (2*Z.of_N ((((2*n+4)/2-1)/2-1)/2)%N+4<=2*a+1); lia.
    + apply Scan_single_Y; intro Hodd; rewrite double_four_even in Hodd; discriminate.
Qed.
Lemma scan_w0_three n a Q : Z.of_N n+4<=4*a-1 ->
  Scan(w0 3++repeat D (h0 3)) n a Q.
Proof.
  intro HN.
  change (Scan ((((((([Y]++[Y])++[V])++[Y])++[Y])++[V])++[D])++[D]) n a Q).
  apply Scan_snoc_D; split.
  - change (2*Z.of_N n+4<=rrun(w0 3) a/2-1); rewrite rrun_w0_three; lia.
  - apply Scan_snoc_D; split.
    + change (2*Z.of_N (2*n+4)%N+4<=rrun(w0 3) a); rewrite rrun_w0_three; lia.
    + apply Scan_snoc_V; right; split; [lia|].
      apply Scan_snoc_Y; left; lia.
Qed.

Lemma scan_w0_big k n a Q : Z.of_N n+4<=4*a-1 ->
  (forall m,(16*(m+1)<=n+4)%N ->Q m) ->
  Scan(w0(k+4)++repeat D(h0(k+4))) n a Q.
Proof.
  intros HN HQ; assert (HA:2<=a) by lia.
  pose proof (pow2_pos k) as HP.
  assert (HPP:1<=pow2 k*pow2 k) by nia.
  assert (HPP':pow2 k<=pow2 k*pow2 k) by nia.
  assert (HW:w0(k+4)=(repeat Y(k+3)++[V;Y;Y;V;D])++repeat V(k+1)).
  { rewrite w0_big; unfold kword.
    replace (k+2-1)%nat with (k+1)%nat by lia.
    replace (k+3)%nat with (S(k+2)) by lia; cbn [repeat app].
    now rewrite <-app_assoc. }
  assert (VT:rrun((repeat Y(k+3)++[V;Y;Y;V;D])++repeat V(k+1)) a=
    pow2 k*pow2 k*128*(a+1)-pow2 k*12).
  { rewrite <-HW,rrun_w0_big.
    replace (2*k+7)%nat with ((k+k)+7)%nat by lia.
    rewrite !pow2_add; change (pow2 k*pow2 k*128*(a+1)-3*(pow2 k*4)=
      pow2 k*pow2 k*128*(a+1)-pow2 k*12); ring. }
  assert (VM:rrun(repeat Y(k+3)++[V;Y;Y]) a=pow2 k*64*(a+1)-5).
  { rewrite rrun_app,rrun_repeat_Y,pow2_add.
    cbn [rrun rstep]; change (2*(2*(2*(pow2 k*8*(a+1)-1))+1)+1=
      pow2 k*64*(a+1)-5). ring. }
  assert (VM4:rrun((repeat Y(k+3)++[V;Y;Y])++[V]) a=
    pow2 k*128*(a+1)-10).
  { rewrite rrun_app,VM; cbn [rrun rstep]; ring. }
  rewrite h0_big,HW; change (Scan (((repeat Y(k+3)++[V;Y;Y;V;D])++
    repeat V(k+1))++[D]) n a Q).
  apply Scan_snoc_D; split.
  - rewrite VT; nia.
  - apply Scan_append_of.
    apply (scan_Vrun_gap (k+1) (2*n+4)%N 1); [lia|].
    intros b HB; change (2*b<=2*n+4)%N in HB.
    replace (repeat Y(k+3)++[V;Y;Y;V;D]) with
      (((repeat Y(k+3)++[V;Y;Y])++[V])++[D]) by (rewrite <-!app_assoc; reflexivity).
    apply Scan_snoc_D; split.
    + rewrite VM4; assert (pow2 k*(a+1)>=a+1) by nia; nia.
    + apply Scan_snoc_V; right; split; [lia|].
      replace (repeat Y(k+3)++[V;Y;Y]) with
        (((repeat Y(k+3)++[V])++[Y])++[Y]) by (rewrite <-!app_assoc; reflexivity).
      apply Scan_snoc_Y; destruct (parity ((2*b+4)/2)%N) as [H1|H1]; [now left|].
      right; split; [exact H1|].
      apply Scan_snoc_Y; destruct (parity (((2*b+4)/2-1)/2)%N) as [H2|H2]; [now left|].
      right; split; [exact H2|].
      apply Scan_snoc_V; destruct (parity ((((2*b+4)/2-1)/2-1)/2)%N) as [H3|H3]; [|now left].
      right; split; [exact H3|].
      apply (scan_Yrun_gap (k+3) _ 3); [lia|].
      intros m HM; change (8*(m+1)<=((((2*b+4)/2-1)/2-1)/2)/2+1)%N in HM.
      apply HQ; clear - HB H1 H2 H3 HM; lia.
Qed.

Theorem gen_scan_gap w h : Gen w h ->forall (a:BinNums.Z) (n:N) (Q:N->Prop),
  Z.of_N n+4<=4*a-1 ->
  (forall m,(16*(m+1)<=n+4)%N ->Q m) ->
  Scan(w++repeat D h) n a Q.
Proof.
  intro HG; induction HG as [r HR|w h HG IH|w h HG IH]; intros a n Q HN HQ.
  - destruct r as [|[|[|[|k]]]]; try lia.
    + apply scan_w0_two; exact HN.
    + apply scan_w0_three; exact HN.
    + replace (S(S(S(S k)))) with (k+4)%nat by lia.
      apply scan_w0_big; assumption.
  - replace ((Y::w)++repeat D(S h)) with (([Y]++(w++repeat D h))++[D]) by
      (cbn [repeat app]; rewrite <-app_assoc,<-repeat_cons; reflexivity).
    apply Scan_snoc_D; split.
    + pose proof (gen_rrun_buf w h HG (2*a+1) ltac:(lia)) as HB.
      rewrite rrun_app; change (2*Z.of_N n+4<=rrun(w++repeat D h)(2*a+1)); lia.
    + apply Scan_append_of; change (Scan(w++repeat D h)(2*n+4)%N (2*a+1)
        (fun m=>Scan[Y] m a Q)).
      apply IH; [lia|]. intros m HM; apply Scan_single_Y; intro HP; apply HQ; lia.
  - replace ((Y::(w++repeat D h++[V]))++repeat D O) with
      (([Y]++(w++repeat D h))++[V]) by (cbn [repeat]; rewrite app_nil_r; cbn [app]; now rewrite app_assoc).
    apply Scan_snoc_V; destruct (parity n) as [HP|HP]; [|now left].
    right; split; [exact HP|].
    apply Scan_append_of; change (Scan(w++repeat D h)(n/2)%N (2*a+1)
      (fun m=>Scan[Y] m a Q)).
    apply IH; [lia|]. intros m HM; apply Scan_single_Y; intro HP'; apply HQ; lia.
Qed.

End BB25FamilyRBGap.

(* BB25FamilyRBClockDefs.v *)
Close Scope Z_scope. Close Scope N_scope.
From Coq Require Import List NArith.
Import ListNotations BB25FamilyCore BB25FamilyWord
  BB25FamilyStack BB25FamilyExact.
Module BB25FamilyRBClockDefs.
Definition wordCD t w h := pdec t++[Y]++w++
  chi(BB25FamilyCore.pow2(S h)*(cap t+1))%N++[V].
End BB25FamilyRBClockDefs.

(* BB25FamilyRBClock.v *)
Close Scope Z_scope. Close Scope N_scope.
From Coq Require Import List NArith ZArith Lia Arith.Wf_nat.
Import ListNotations BB25FamilyCore BB25FamilyWord
  BB25FamilyStack BB25FamilyReset
  BB25FamilyDrain BB25FamilyReady
  BB25FamilyExact BB25FamilyExactRun
  BB25FamilyLADebt BB25FamilyLAChi
  BB25FamilyLADirect BB25FamilyRBClockDefs
  BB25FamilyRBGen BB25FamilyRBScan
  BB25FamilyRBReady BB25FamilyRBGap.

Module BB25FamilyRBClock.
Open Scope Z_scope.
Notation npow := BB25FamilyCore.pow2.
Lemma rrun_chi_pos M : (1<=M)%N ->forall v, 4*Z.of_N M-3<=v ->
  1<=rrun(chi M)v.
Proof.
  induction M as [M IH] using
    (well_founded_induction (well_founded_ltof _ N.to_nat)).
  intros HM v HV; destruct(N.lt_ge_cases M 2) as [Hlt|Hge].
  - assert (E:M=1%N) by lia; rewrite chi_small by exact Hlt; cbn[rrun]; rewrite E in HV; cbn[Z.of_N] in HV; lia.
  - pose proof(N.div_mod M 2 ltac:(discriminate)) as HD.
    pose proof(N.mod_lt M 2 ltac:(discriminate)) as HR.
    assert (HM':(1<=M/2)%N) by lia.
    assert (HL:(N.to_nat(M/2)<N.to_nat M)%nat) by lia.
    rewrite chi_step by exact Hge; destruct(N.odd M) eqn:HO.
    + change (1<=rrun(chi(M/2))(2*v)); apply(IH (M/2)%N HL HM'); lia.
    + rewrite odd_Nmod in HO; apply N.eqb_neq in HO.
      assert (HE:(M mod 2=0)%N) by lia.
      change (1<=rrun(chi(M/2))(v/2-1)); apply(IH (M/2)%N HL HM').
      pose proof(div2_bounds v); lia.
Qed.
Lemma rrun_chi_pos_entry M v : (2<=M)%N ->4*Z.of_N M-4<=v ->
  1<=rrun(chi M)v.
Proof.
  intros HM HV; pose proof(N.div_mod M 2 ltac:(discriminate)) as HD.
  pose proof(N.mod_lt M 2 ltac:(discriminate)) as HR.
  assert (HM':(1<=M/2)%N) by lia.
  rewrite chi_step by exact HM; destruct(N.odd M) eqn:HO.
  - change (1<=rrun(chi(M/2))(2*v)); apply rrun_chi_pos; [exact HM'|lia].
  - rewrite odd_Nmod in HO; apply N.eqb_neq in HO.
    assert (HE:(M mod 2=0)%N) by lia.
    change (1<=rrun(chi(M/2))(v/2-1)); apply rrun_chi_pos; [exact HM'|].
    pose proof(div2_bounds v); lia.
Qed.

Lemma small_clock_word t : wordCD t [Y;V] O=tail_word t 2.
Proof. reflexivity. Qed.
Theorem lemma_seven t : Good t ->(1<=cap t)%N ->
  1<=rrun(wordCD t [Y;V] O)0 /\ Ready(TW(wordCD t [Y;V] O)).
Proof.
  intros HG HX; split.
  - unfold wordCD; rewrite (chi_two_pow 1 (cap t+1)%N ltac:(lia)).
    rewrite !rrun_app; change (1<=2*rrun(chi(cap t+1)%N)
      ((2*(2*(2*bval t+1)+1))/2-1)).
    assert (E:((2*(2*(2*bval t+1)+1))/2-1)=4*bval t+2) by lia.
    rewrite E; pose proof(good_bound t HG).
    pose proof(rrun_chi_pos (cap t+1)%N ltac:(lia) (4*bval t+2) ltac:(lia)); lia.
  - rewrite small_clock_word; apply ready_drain_word; [exact HG|lia].
Qed.

Lemma pdec_nil_of_counts s : nbit s=O ->nsh s=O ->pdec s=[].
Proof. destruct s as [|b s]; [reflexivity|destruct b; cbn[nbit nsh]; intros; lia]. Qed.

Theorem slack_early s d : Adm s ->Strict s ->0<=bval s ->(d=D \/ d=V) ->
  0<=rstep d (bval s) ->pdec s<>[] ->forall k,
  (cap(TW(pdec s++[d]))+1=npow k)%N ->
  Z.of_N(cap(TW(pdec s++[d])))+1<=bval(TW(pdec s++[d])).
Proof.
  intros HA HS HB HD HC Hne k HK.
  destruct(tfold_empty_props (pdec s) HB) as [HAu [HGu [ECu [EBu _]]]].
  change (Z.of_N(cap(TW(pdec s)))=bval s) in ECu.
  change (bval(TW(pdec s))=trun(pdec s)0 0) in EBu.
  assert (Hcredit:bval s<=trun(pdec s)0 0).
  { pose proof(good_bound _ HGu) as H.
    change (Z.of_N(cap(TW(pdec s)))<=bval(TW(pdec s))) in H.
    rewrite ECu,EBu in H; exact H. }
  assert (Hwhole:0<=rrun(pdec s++[d])0) by (rewrite rrun_app; exact HC).
  destruct(tfold_empty_props (pdec s++[d]) Hwhole) as [HAt [HGt [ECt [EBt _]]]].
  change (Z.of_N(cap(TW(pdec s++[d])))=rrun(pdec s++[d])0) in ECt.
  rewrite rrun_app in ECt; change (Z.of_N(cap(TW(pdec s++[d])))=rstep d(bval s)) in ECt.
  assert (EV:bval(TW(pdec s++[d]))=rstep(qout d(bval s))(trun(pdec s)0 0)).
  { unfold TW at 1; rewrite tfold_app;
    change (bval(tstep (TW(pdec s))d)=rstep(qout d(bval s))(trun(pdec s)0 0)).
    rewrite tstep_bval by (rewrite ECu; exact HC); now rewrite ECu,EBu. }
  rewrite ECt,EV; destruct HD as [-> | ->].
  - cbn[rstep] in HC,ECt |- *; unfold qout.
    destruct(Z.eqb (bval s mod 2) 1) eqn:HO.
    + cbn[rstep]; pose proof(div2_bounds(bval s)); lia.
    + apply Z.eqb_neq in HO.
      assert (Hmod:bval s mod 2=0) by (pose proof(Z.mod_pos_bound (bval s) 2 ltac:(lia)); lia).
      assert (Hcast:Z.of_N(cap(TW(pdec s++[D])))+1=pow2 k).
      { pose proof(f_equal Z.of_N HK); rewrite N2Z.inj_add,pow2_of_N in H; exact H. }
      assert (Hval:bval s=pow2(S k)).
      { rewrite pow2_succ; pose proof(Z.div_mod (bval s) 2 ltac:(lia)); lia. }
      pose proof(adm_bound s HA) as Hbal.
      assert (Hnb:(1<=nbit s)%nat).
      { destruct(nbit s) eqn:E; [exfalso; apply Hne,pdec_nil_of_counts; lia|lia]. }
      pose proof(strict_head s HS Hnb) as Hstr.
      assert (EB:bal(pdec s)=Z.of_nat(nbit s-nsh s)).
      { rewrite bal_pdec; lia. }
      pose proof(trun_gt_of_pow (pdec s) (nbit s-nsh s) (S k)
        (pdec_dyck s HA) EB ltac:(lia) ltac:(lia) Hval) as Hgap.
      change (bval s+2<=trun(pdec s)0 0) in Hgap.
      cbn[rstep]; pose proof(div2_bounds(bval s)); pose proof(div2_bounds(trun(pdec s)0 0)); lia.
  - cbn[qout rstep]; lia.
Qed.

Open Scope N_scope.
Lemma ready_chi_ref m : 1<=m ->forall pre, 4*m<=cap(TW pre)+4 ->
  (forall n, n+4<=4*m ->(n mod 2=1 ->n+9<=2*m) ->
    ((exists k,m=npow k) \/ n+12<=4*m) ->Ready(dpow n(TW pre))) ->
  Ready(TW(pre++chi m)).
Proof.
  induction m as [m IH] using
    (well_founded_induction (well_founded_ltof _ N.to_nat)).
  intros HM pre HC HR; destruct(N.lt_ge_cases m 2) as [Hlt|Hge].
  - assert (HE:m=1) by lia; rewrite chi_small by exact Hlt; rewrite app_nil_r.
    apply(HR 0); [lia|discriminate|left; exists O; exact HE].
  - pose proof(N.div_mod m 2 ltac:(discriminate)) as Hdiv.
    pose proof(N.mod_lt m 2 ltac:(discriminate)) as Hmod.
    assert (HM':1<=m/2) by lia.
    assert (Hlt':(N.to_nat(m/2)<N.to_nat m)%nat) by lia.
    rewrite chi_step by exact Hge; destruct(N.odd m) eqn:HO.
    + rewrite odd_Nmod in HO; apply N.eqb_eq in HO.
      replace (pre++V::chi(m/2)) with ((pre++[V])++chi(m/2))
        by (rewrite <-app_assoc; reflexivity).
      apply(IH (m/2) Hlt' HM').
      * rewrite TW_V_cap; lia.
      * intros n HN _ _.
        pose proof(N.div_mod n 2 ltac:(discriminate)) as Hndiv.
        pose proof(N.mod_lt n 2 ltac:(discriminate)) as Hnmod.
        destruct(N.eq_dec (n mod 2) 1) as [HP|HP].
        -- apply ready_V_odd; [rewrite TW_V_cap; lia|exact HP].
        -- apply ready_V_even; [rewrite TW_V_cap; lia|lia|].
           apply HR; [lia| |right; lia].
           intro HQ; pose proof(N.div_mod (n/2) 2 ltac:(discriminate)); lia.
    + rewrite odd_Nmod in HO; apply N.eqb_neq in HO.
      assert (HP:m mod 2=0) by lia.
      assert (H2:2<=cap(TW pre)) by lia.
      replace (pre++D::chi(m/2)) with ((pre++[D])++chi(m/2))
        by (rewrite <-app_assoc; reflexivity).
      apply(IH (m/2) Hlt' HM').
      * rewrite TW_D_cap by exact H2; div2.
      * intros n HN _ HD; apply ready_D; [lia|].
        apply HR; [lia|rewrite N.add_mod,N.mul_mod by discriminate; discriminate|].
        destruct HD as [[k HK]|HD].
        -- left; exists(S k); change (m=2*npow k); lia.
        -- right; lia.
Qed.

Open Scope Z_scope.
Definition clock_pre t w h := (pdec t++[Y])++(w++repeat D(S h)).
Lemma wordCD_expanded t w h :
  wordCD t w h=(clock_pre t w h++chi(cap t+1)%N)++[V].
Proof.
  unfold wordCD,clock_pre; rewrite chi_two_pow by lia.
  repeat rewrite <-app_assoc; reflexivity.
Qed.
Lemma clock_pre_value t w h :
  rrun(clock_pre t w h)0=rrun(w++repeat D(S h))(2*bval t+1).
Proof. unfold clock_pre; rewrite rrun_app; f_equal; rewrite rrun_app; reflexivity. Qed.
Lemma clock_pre_bound t w h : Good t ->Gen w h ->
  4*bval t<=rrun(clock_pre t w h)0.
Proof.
  intros HG HW; rewrite clock_pre_value.
  pose proof(good_bval_nonneg t HG) as HB.
  pose proof(gen_rrun_buf' w h HW (2*bval t+1) ltac:(lia)) as H.
  replace (h+1)%nat with (S h) in H by lia; lia.
Qed.

Theorem lemmaC_of_scan t w h : Good t ->
  (forall k,(cap t+1=npow k)%N ->Z.of_N(cap t)+1<=bval t) ->Gen w h ->
  (forall a (n:N) (Q:N->Prop), Z.of_N n+4<=4*a-1 ->
    (forall m,(16*(m+1)<=n+4)%N ->Q m) ->Scan(w++repeat D h)n a Q) ->
  1<=rrun(wordCD t w h)0 /\ Ready(TW(wordCD t w h)).
Proof.
  intros HG Hslack HW Hscan.
  pose proof(good_bound t HG) as HB.
  pose proof(good_bval_nonneg t HG) as HB0.
  pose proof(clock_pre_bound t w h HG HW) as HF.
  rewrite wordCD_expanded; split.
  - rewrite !rrun_app; change (1<=2*rrun(chi(cap t+1)%N)(rrun(clock_pre t w h)0)).
    destruct(N.eq_dec (cap t) 0) as [HC|HC].
    + pose proof(Hslack O ltac:(rewrite HC; reflexivity)) as HS.
      rewrite HC in HS |- *; change (1<=bval t) in HS.
      change (1<=2*rrun(clock_pre t w h)0); lia.
    + pose proof(rrun_chi_pos_entry (cap t+1)%N (rrun(clock_pre t w h)0) ltac:(lia) ltac:(lia)); lia.
  - rewrite TW_V; apply ready_X.
    assert (HCpre:0<=rrun(clock_pre t w h)0) by lia.
    destruct(tfold_empty_props (clock_pre t w h) HCpre) as [_ [_ [ECpre _]]].
    change (Z.of_N(cap(TW(clock_pre t w h)))=rrun(clock_pre t w h)0) in ECpre.
    apply ready_chi_ref; [lia|lia|].
    intros n HN _ HD.
    assert (HN4:Z.of_N n+4<=4*bval t).
    { destruct HD as [[k HK]|HD]; [pose proof(Hslack k HK); lia|lia]. }
    destruct(tfold_empty_props (pdec t) HB0) as [HAt [HGt [ECt _]]].
    change (Adm(TW(pdec t))) in HAt; change (Good(TW(pdec t))) in HGt.
    change (Z.of_N(cap(TW(pdec t)))=bval t) in ECt.
    set (mid:=([Y]++(w++repeat D h))++[D]).
    assert (Eword:clock_pre t w h=pdec t++mid).
    { unfold clock_pre,mid;
      change ((pdec t++[Y])++(w++D::repeat D h)=pdec t++(([Y]++(w++repeat D h))++[D])).
      rewrite (repeat_cons h D); repeat rewrite <-app_assoc; reflexivity. }
    rewrite Eword; unfold TW at 1; rewrite tfold_app; fold(TW(pdec t)).
    pose proof(gen_rrun_buf w h HW (2*bval t+1) ltac:(lia)) as Hbuf.
    assert (Emid:rrun mid (Z.of_N(cap(TW(pdec t))))=
      rrun(w++repeat D h)(2*bval t+1)/2-1).
    { unfold mid; rewrite !rrun_app,ECt; reflexivity. }
    apply(ready_scan mid (TW(pdec t)) n (fun m=>(2*m+2<=cap t)%N));
      [exact HAt|exact HGt| | | |intros m HM; now apply ready_dpow_of_cap].
    + rewrite Emid; pose proof(div2_bounds(rrun(w++repeat D h)(2*bval t+1))); lia.
    + rewrite Emid; pose proof(div2_bounds(rrun(w++repeat D h)(2*bval t+1))); lia.
    + unfold mid; apply Scan_snoc_D; split.
      * rewrite rrun_app,ECt; change (2*Z.of_N n+4<=rrun(w++repeat D h)(2*bval t+1)); lia.
      * apply Scan_app; change (Scan(w++repeat D h)(2*n+4)%N
          (2*Z.of_N(cap(TW(pdec t)))+1)
          (fun m=>Scan[Y]m (Z.of_N(cap(TW(pdec t))))(fun a=>(2*a+2<=cap t)%N))).
        rewrite ECt; apply Hscan.
        -- rewrite N2Z.inj_add,N2Z.inj_mul; cbn[Z.of_N]; lia.
        -- intros m HM; change (Scan([]++[Y])m (bval t)(fun a=>(2*a+2<=cap t)%N)).
           apply Scan_snoc_Y; destruct(N.eq_dec (m mod 2) 0) as [HP|HP]; [now left|].
           assert (Hodd:(m mod 2=1)%N) by (pose proof(N.mod_lt m 2 ltac:(discriminate)); lia).
           right; split; [exact Hodd|change (2*((m-1)/2)+2<=cap t)%N].
           pose proof(N.div_mod (m-1) 2 ltac:(discriminate)) as HDm.
           pose proof(N.mod_lt (m-1) 2 ltac:(discriminate)) as HMm.
           pose proof(N.div_mod m 2 ltac:(discriminate)) as HDm'.
           clear - HM HN Hodd HDm HMm HDm'; lia.
Qed.

Theorem lemmaC t w h : Good t ->
  (forall k,(cap t+1=npow k)%N ->Z.of_N(cap t)+1<=bval t) ->Gen w h ->
  1<=rrun(wordCD t w h)0 /\ Ready(TW(wordCD t w h)).
Proof.
  intros HG HS HW; apply lemmaC_of_scan; try assumption.
  now apply gen_scan_gap.
Qed.
End BB25FamilyRBClock.

(* BB25FamilyRBRun.v *)
Close Scope Z_scope. Close Scope N_scope.
From BusyCoq Require Import Individual25.
Open Scope sym_scope.
From Coq Require Import List NArith ZArith Lia Arith.Wf_nat.
Import ListNotations BB25FamilyRules
  BB25FamilyCore BB25FamilyWord
  BB25FamilyStack BB25FamilyReset
  BB25FamilyMachine BB25FamilyDrain
  BB25FamilyReturn BB25FamilyReady
  BB25FamilyMarker BB25FamilyDrainWord
  BB25FamilyExact BB25FamilyExactRun
  BB25FamilyRBGen BB25FamilyRBClockDefs
  BB25FamilySeed.

Module BB25FamilyRBRun.
Notation npow := BB25FamilyCore.pow2.

(** Heights concern only the colored word, not the arithmetic counter. *)
Inductive DyckRun : nat ->list digit ->nat ->Prop :=
| dr_nil h : DyckRun h [] h
| dr_Y h h' w : DyckRun (S h) w h' ->DyckRun h (Y::w) h'
| dr_V h h' w : DyckRun h w h' ->DyckRun (S h) (V::w) h'
| dr_D h h' w : DyckRun h w h' ->DyckRun (S h) (D::w) h'.

Lemma dyckrun_height w : forall h h',
  (forall p t,w=p++t ->(0<=Z.of_nat h+bal p)%Z) ->
  (Z.of_nat h+bal w=Z.of_nat h')%Z ->DyckRun h w h'.
Proof.
  induction w as [|b w IH]; intros h h' HP HE.
  - cbn [bal] in HE; assert (h=h') by lia; subst; constructor.
  - assert (Hhead:(0<=Z.of_nat h+bal [b])%Z) by (apply (HP [b] w); reflexivity).
    destruct b.
    + apply dr_Y,IH.
      * intros p t Ep; pose proof (HP (Y::p) t ltac:(cbn; now rewrite Ep)); cbn [bal] in *; lia.
      * cbn [bal] in HE; lia.
    + destruct h; [cbn [bal] in Hhead; lia|apply dr_V,IH].
      * intros p t Ep; pose proof (HP (V::p) t ltac:(cbn; now rewrite Ep)); cbn [bal] in *; lia.
      * cbn [bal] in HE; lia.
    + destruct h; [cbn [bal] in Hhead; lia|apply dr_D,IH].
      * intros p t Ep; pose proof (HP (D::p) t ltac:(cbn; now rewrite Ep)); cbn [bal] in *; lia.
      * cbn [bal] in HE; lia.
Qed.
Lemma dyckrun_of_prefix w h : DyckPre w ->bal w=Z.of_nat h ->DyckRun O w h.
Proof. intros HP HE; apply dyckrun_height; [intros p t E; apply (HP p t E)|exact HE]. Qed.
Lemma gen_dyckrun w h : Gen w h ->DyckRun O w h.
Proof. intro H; destruct (gen_dyck w h H); now apply dyckrun_of_prefix. Qed.

Lemma gen_start_Y w h : Gen w h ->exists v,w=Y::v.
Proof.
  intro HG; destruct HG as [r Hr|w h HG|w h HG]; try (eexists; reflexivity).
  destruct r as [|[|[|[|k]]]]; try lia; eexists; reflexivity.
Qed.
Lemma gen_end_V w h : Gen w h ->exists u,w=u++[V].
Proof.
  intro HG; induction HG as [r Hr|w h HG [u ->]|w h HG IH].
  - destruct r as [|[|[|[|k]]]]; try lia.
    + exists [Y;D;Y;Y]; reflexivity.
    + exists [Y;Y;V;Y;Y]; reflexivity.
    + exists (Y::(repeat Y(S(S k))++[V;Y;Y;V;D]++repeat V k)).
      change (Y::(repeat Y(S(S k))++[V;Y;Y;V;D]++repeat V(S k))=
        (Y::(repeat Y(S(S k))++[V;Y;Y;V;D]++repeat V k))++[V]).
      assert (ER:repeat V(S k)=repeat V k++[V]) by apply repeat_cons.
      rewrite ER; cbn [app]; repeat rewrite <-app_assoc; reflexivity.
  - exists (Y::u); reflexivity.
  - exists (Y::(w++repeat D h)); cbn [app]; rewrite <-!app_assoc; reflexivity.
Qed.

Definition cstep s b := match b with Y=>Z::s | V=>W::s | D=>W::cdec s end.
Fixpoint cfold s w := match w with []=>s |b::w=>cfold(cstep s b)w end.

Section Runs.
Variable b4 : control.
Notation tm := (family b4).
Notation "c -->* c'" := (c -[tm]->* c') (at level 40).
Notation "c -->+ c'" := (c -[tm]->+ c') (at level 40).
Open Scope N_scope.

(** No goodness premise is needed: this is the normal counter phase,
    rather than the pending-2 reset phase. Both tape tails stay arbitrary. *)
Theorem cfold_props_gen h w h' : DyckRun h w h' ->forall a s,
  cap s+1=npow h*(a+1) ->
  cap(cfold s w)+1=npow h'*(a+1) /\ pdec(cfold s w)=pdec s++w /\
  forall l r,left s l {{A}}>cells w *>r -->* left(cfold s w) l {{A}}>r.
Proof.
  intro HD; induction HD as [h|h h' w HD IH|h h' w HD IH|h h' w HD IH];
    intros a s HC.
  - split; [exact HC|split; [now rewrite app_nil_r|intros; apply evstep_refl]].
  - assert (HC':cap(Z::s)+1=npow(S h)*(a+1)) by (cbn [cap npow]; nia).
    destruct (IH a (Z::s) HC') as [EC [EP HR]].
    split; [exact EC|split].
    + cbn [cfold cstep]; rewrite EP; cbn [pdec]; now rewrite <-app_assoc.
    + intros l r; cbn [cfold cstep cells flat_map dc]; rewrite Str_app_assoc.
      eapply evstep_trans; [apply progress_evstep; apply right_Y|apply HR].
  - assert (HO:N.odd(cap s)=true).
    { apply (odd_of_succ_double (cap s) (npow h*(a+1))); cbn [npow] in HC; nia. }
    assert (HC':cap(W::s)+1=npow h*(a+1)) by (cbn [cap]; cbn [npow] in HC; nia).
    destruct (IH a (W::s) HC') as [EC [EP HR]].
    split; [exact EC|split].
    + cbn [cfold cstep]; rewrite EP; cbn [pdec]; rewrite HO,<-app_assoc; reflexivity.
    + intros l r; cbn [cfold cstep cells flat_map dc]; rewrite Str_app_assoc.
      eapply evstep_trans; [apply progress_evstep; apply right_V|apply HR].
  - pose proof (BB25FamilyCore.pow2_pos h) as Hpow.
    assert (HP:0<cap s) by (cbn [npow] in HC; nia).
    assert (HE:cap(cdec s)=cap s-1) by now apply cdec_capacity.
    assert (HO:N.odd(cap(cdec s))=false).
    { assert (HO':N.odd(cap s)=true).
      { apply (odd_of_succ_double (cap s) (npow h*(a+1))); cbn [npow] in HC; nia. }
      rewrite HE,odd_before_even,HO' by exact HP; reflexivity. }
    assert (HC':cap(W::cdec s)+1=npow h*(a+1))
      by (cbn [cap]; rewrite HE; cbn [npow] in HC; nia).
    destruct (IH a (W::cdec s) HC') as [EC [EP HR]].
    split; [exact EC|split].
    + cbn [cfold cstep]; rewrite EP; cbn [pdec]; rewrite HO,cdec_pdec,<-app_assoc; reflexivity.
    + intros l r; cbn [cfold cstep cells flat_map dc]; rewrite Str_app_assoc.
      apply progress_evstep; eapply progress_trans; [apply right_one|].
      eapply progress_trans; [apply cdec_run; exact HP|].
      eapply progress_evstep_trans; [apply right_V|apply HR].
Qed.

(** Exact drain over an arbitrary bottom. The old strong-return theorem
    additionally resets the word; this local form needs no goodness. *)
Theorem drain_plain s : forall l,
  left s l {{A}}>0inf -->+ l <{{A}} cells(drain_word s) *>0inf.
Proof.
  induction s as [s IH] using
    (well_founded_induction (well_founded_ltof _ (fun s=>N.to_nat(cap s)))); intro l.
  destruct (N.eq_dec (cap s) 0) as [HC|HC].
  - rewrite drain_word_zero by exact HC; rewrite cells_app,Str_app_assoc; cbn [cells flat_map dc].
    rewrite <-out_pdec.
    eapply progress_evstep_trans; [apply right_blank|apply overflow_run; exact HC].
  - assert (HP:0<cap s) by lia.
    assert (HL:(N.to_nat(cap(W::cdec s))<N.to_nat(cap s))%nat).
    { cbn [cap]; rewrite cdec_capacity by exact HP; lia. }
    pose proof (IH (W::cdec s) HL l) as HR.
    rewrite drain_word_round in HR by exact HP.
    eapply progress_trans; [apply right_blank|].
    eapply progress_trans; [apply cdec_run; exact HP|].
    eapply progress_trans; [apply right_V|exact HR].
Qed.

Theorem marker_return_word w h : DyckRun O w h ->forall l,
  l {{A}}>cells w *>0inf -->+ l <{{A}} cells(w++repeat D h++[V]) *>0inf.
Proof.
  intros HD l.
  destruct (cfold_props_gen O w h HD 0 [] eq_refl) as [HC [HP HR]].
  cbn in HP; change (cap(cfold [] w)+1=npow h*1) in HC; rewrite N.mul_1_r in HC.
  pose proof (drain_plain (cfold [] w) l) as HT.
  unfold drain_word in HT; rewrite HP,HC in HT.
  replace (npow h) with (npow h*1) in HT by lia.
  rewrite chi_two_pow in HT by lia; cbn [chi pchi] in HT; rewrite app_nil_r in HT.
  eapply evstep_progress_trans; [exact (HR l 0inf)|exact HT].
Qed.

Lemma rreturns_reset_end s w u : Adm s ->Good s ->Strict s ->w=u++[V] ->
  (1<=rrun w (Z.of_N(cap s)))%Z ->Ready(tfold s w) ->
  RReturns b4 (left s root {{A}}>S2>>cells w *>0inf).
Proof.
  intros HA HG HS Ew HP HR.
  destruct(tfold_props w s HA HG ltac:(lia)) as [HA' [HG' [HC Hrest]]].
  eapply rreturns_trans; [apply reset_run; lia|].
  eapply rreturns_trans; [apply progress_evstep; apply right_two_blank|].
  apply rreturns_cp; constructor.
  - split; [exact HA'|split; [exact HG'|split; [lia|]]].
    exists(tfold s u); rewrite Ew,tfold_app; reflexivity.
  - exact HR.
  - apply strict_tfold; auto; lia.
Qed.

Lemma counter_drain_word t w h : DyckRun O w h ->
  left(Z::t) root {{A}}>cells w *>0inf -->+
  root {{A}}>S2>>cells(wordCD t w h) *>0inf.
Proof.
  intro HD.
  destruct(cfold_props_gen O w h HD (cap(Z::t)) (Z::t) ltac:(cbn[npow];lia))
    as [HC [HP HR]].
  assert (EC:cap(cfold(Z::t)w)+1=npow(S h)*(cap t+1)).
  { cbn [cap npow] in HC |- *; nia. }
  pose proof (drain_plain (cfold(Z::t)w) root) as HT.
  unfold drain_word in HT; rewrite EC,HP in HT; cbn [pdec] in HT.
  eapply evstep_progress_trans; [exact(HR root 0inf)|].
  eapply progress_trans; [exact HT|].
  unfold wordCD; rewrite <-!app_assoc; apply leftend_A.
Qed.

Lemma rreturns_counter_drain t w h : DyckRun O w h ->
  (1<=rrun(wordCD t w h)0)%Z ->Ready(tfold [](wordCD t w h)) ->
  RReturns b4 (left(Z::t) root {{A}}>cells w *>0inf).
Proof.
  intros HD HP HR.
  eapply rreturns_trans; [apply progress_evstep; apply counter_drain_word; exact HD|].
  eapply (rreturns_reset_end [] (wordCD t w h)
    (pdec t++[Y]++w++chi(npow(S h)*(cap t+1)))); try exact I; try assumption.
  unfold wordCD; rewrite <-!app_assoc; reflexivity.
Qed.

End Runs.

Theorem rb_pop_episode s w h : (2<=cap s)%N ->DyckRun O w h ->forall l,
  left(W::s) l <{{B}} S1 >>cells w *>0inf -[family(Some(S0,R,B))]->+
  left(cdec(cdec s)) l <{{B}} S1 >>cells(Y::(w++repeat D h++[V])) *>0inf.
Proof.
  intros HC HD l.
  assert (H1:(0<cap s)%N) by lia.
  assert (H2:(0<cap(cdec s))%N) by (rewrite cdec_capacity by exact H1; lia).
  rewrite left_cons; cbn [tc].
  eapply progress_trans; [apply B1_W|].
  eapply progress_trans; [apply cdec_run; exact H1|].
  eapply progress_trans; [apply right_one|].
  eapply progress_trans; [apply cdec_run; exact H2|].
  eapply progress_trans; [apply G_B_right|].
  eapply progress_trans; [apply marker_return_word; exact HD|].
  cbn [cells flat_map dc]; rewrite Str_app_assoc; apply left_J0.
Qed.

Theorem first_episode s r : (2<=cap s)%N ->(2<=r)%nat ->forall l,
  left(W::s) l <{{B}} S1>>cells(repeat Y r)*>S1>>0inf -[family(Some(S0,R,B))]->+
  left(cdec(cdec s)) l <{{B}} S1>>cells(w0 r)*>0inf.
Proof.
  intros HC Hr l; destruct r as [|[|r]]; [lia|lia|].
  assert (H1:(0<cap s)%N) by lia.
  assert (H2:(0<cap(cdec s))%N) by (rewrite cdec_capacity by exact H1; lia).
  rewrite left_cons; cbn [tc].
  eapply progress_trans; [apply B1_W|].
  eapply progress_trans; [apply cdec_run; exact H1|].
  eapply progress_trans; [apply right_one|].
  eapply progress_trans; [apply cdec_run; exact H2|].
  eapply progress_trans; [apply G_B_right|].
  change (left [] ([S3;S0;S0]*>left(cdec(cdec s))l) {{A}}>
    cells(repeat Y(S(S r)))*>S1>>0inf -[family(Some(S0,R,B))]->+
    left(cdec(cdec s)) l <{{B}} S1>>cells(w0(S(S r)))*>0inf).
  eapply evstep_progress_trans; [apply Yrun|].
  eapply progress_trans; [apply marker_tail_run|].
  destruct r as [|[|k]].
  - unfold marker_tail; cbn [pushZ Nat.iter left flat_map cells dc repeat w0]; execute.
  - unfold marker_tail; cbn [pushZ Nat.iter left flat_map tc cells dc repeat w0]; execute.
  - eapply progress_trans; [apply marker_drain|].
    replace (w0(S(S(S(S k))))) with (Y::kword(S(S k))).
    + cbn [cells flat_map dc]; rewrite Str_app_assoc; apply left_J0.
    + replace (S(S(S(S k)))) with (k+4)%nat by lia.
      rewrite w0_big; f_equal; f_equal; lia.
Qed.

Definition ZEven b4 := forall s w h, Adm s ->Good s ->Strict s ->Gen w h ->
  RReturns b4 (left s root <{{A}} dc D*>S2>>cells w*>0inf).

Section Closure.
Variable b4 : control.
Hypothesis pop_word : forall s w h, (2<=cap s)%N ->DyckRun O w h ->forall l,
  left(W::s) l <{{B}} S1>>cells w*>0inf -[family b4]->+
  left(cdec(cdec s)) l <{{B}} S1>>cells(Y::(w++repeat D h++[V]))*>0inf.
Hypothesis pop_first : forall s r, (2<=cap s)%N ->(2<=r)%nat ->forall l,
  left(W::s) l <{{B}} S1>>cells(repeat Y r)*>S1>>0inf -[family b4]->+
  left(cdec(cdec s)) l <{{B}} S1>>cells(w0 r)*>0inf.
Hypothesis zeven : ZEven b4.
Notation tm := (family b4).

Theorem sweep_even s : Ready s ->forall w h, Gen w h ->Adm s ->Good s ->Strict s ->
  RReturns b4 (left s root <{{B}} S1>>cells w*>0inf).
Proof.
  intro HR; induction HR as [|s|s HR IH|s HC HR IH]; intros w h HW HA HG HS.
  - right; apply leftend_B1_nonhalt.
  - rewrite left_cons; cbn [tc].
    eapply rreturns_trans; [apply progress_evstep; apply B1_Z|].
    eapply zeven; [exact(proj1 HA)|exact(proj1 HG)|exact(proj1 HS)|exact HW].
  - rewrite left_cons; cbn [tc].
    eapply rreturns_trans; [apply progress_evstep; apply B1_X|].
    change (RReturns b4 (left s root <{{B}} S1>>cells(Y::w)*>0inf)).
    eapply IH; [apply gen_pre; exact HW|exact(proj1 HA)|exact(proj1 HG)|exact(proj1 HS)].
  - eapply rreturns_trans; [apply progress_evstep; apply pop_word; [exact HC|exact(gen_dyckrun w h HW)]|].
    eapply IH; [apply gen_mark; exact HW| | |].
    + apply cdec_adm,cdec_adm; exact(proj1 HA).
    + apply cdec_good,cdec_good; exact(proj1 HG).
    + apply strict_cdec,strict_cdec; exact(proj1 HS).
Qed.

Theorem sweep_odd s : Ready s ->forall r, (2<=r)%nat ->Adm s ->Good s ->Strict s ->
  RReturns b4 (left s root <{{B}} S1>>cells(repeat Y r)*>S1>>0inf).
Proof.
  intro HR; induction HR as [|s|s HR IH|s HC HR IH]; intros r Hr HA HG HS.
  - right; apply leftend_B1_nonhalt.
  - rewrite left_cons; cbn [tc].
    eapply rreturns_trans; [apply progress_evstep; apply B1_Z|].
    apply BB25FamilyLAFinal.zready;
      [exact(proj1 HA)|exact(proj1 HG)|exact Hr].
  - rewrite left_cons; cbn [tc].
    eapply rreturns_trans; [apply progress_evstep; apply B1_X|].
    change (RReturns b4 (left s root <{{B}} S1>>cells(repeat Y(S r))*>S1>>0inf)).
    apply IH; [lia|exact(proj1 HA)|exact(proj1 HG)|exact(proj1 HS)].
  - eapply rreturns_trans; [apply progress_evstep; apply pop_first; [exact HC|exact Hr]|].
    eapply sweep_even; [exact HR|apply gen_base; exact Hr| | |].
    + apply cdec_adm,cdec_adm; exact(proj1 HA).
    + apply cdec_good,cdec_good; exact(proj1 HG).
    + apply strict_cdec,strict_cdec; exact(proj1 HS).
Qed.

Lemma rb_cp_progress s : ReadyCP s ->
  (exists t,cp s -[tm]->+cp t /\ ReadyCP t) \/ ~halts tm(cp s).
Proof.
  intros [HS HR HSt]; destruct HS as [HA [HG [HC [t ->]]]].
  assert (Hrun:cp(X::t) -[tm]->+left t root <{{B}} S1>>cells(repeat Y 2)*>S1>>0inf).
  { unfold cp; rewrite left_cons; cbn [tc cells flat_map repeat dc]; apply B1_X. }
  assert (HT:RReturns b4 (left t root <{{B}} S1>>cells(repeat Y 2)*>S1>>0inf)).
  { apply sweep_odd; [now apply ready_of_X|lia|exact(proj1 HA)|exact(proj1 HG)|exact(proj1 HSt)]. }
  destruct HT as [[u [HU HT]]|HN].
  - left; exists u; split; [eapply progress_evstep_trans; eassumption|exact HU].
  - right; eapply multistep_nonhalt; [apply progress_evstep; exact Hrun|exact HN].
Qed.

Theorem nonhalt_of_zeven : ~halts tm c0.
Proof.
  eapply multistep_nonhalt; [apply seed_run|].
  apply(progress_nonhalt_or tm (fun c=>exists s,ReadyCP s /\ c=cp s)).
  - intros c [s [HS ->]]; destruct(rb_cp_progress s HS) as [[t [HR HT]]|HN].
    + left; exists(cp t); split; [exact HR|exists t; split; [exact HT|reflexivity]].
    + right; exact HN.
  - exists seed; split; [exact ready_seedCP|reflexivity].
Qed.
End Closure.

End BB25FamilyRBRun.

(* BB25FamilyRBFinal.v *)
Close Scope Z_scope. Close Scope N_scope.
From BusyCoq Require Import Individual25.
Open Scope sym_scope.
From Coq Require Import List NArith ZArith Lia String.
Import ListNotations BB25FamilyRules
  BB25FamilyCore BB25FamilyWord
  BB25FamilyStack BB25FamilyReset
  BB25FamilyMachine BB25FamilyDrain
  BB25FamilyBounds BB25FamilyReturn
  BB25FamilyReady BB25FamilyRBGen
  BB25FamilyRBReady BB25FamilyRBFamilies
  BB25FamilyRBClockDefs BB25FamilyRBClock
  BB25FamilyRBRun.

Module BB25FamilyRBFinal.
Open Scope Z_scope.
Definition rb_digit_eq_dec (a b:digit) : {a=b}+{a<>b}.
Proof. decide equality. Defined.
Section Branch.
Variable b4 : control.

Lemma gen_reset s w h : Adm s ->Good s ->Strict s ->Gen w h ->
  (w<>w0 2 \/ (1<=cap s)%N) ->
  RReturns b4 (left s root {{A}}>S2>>cells w*>0inf).
Proof.
  intros HA HG HS HW Hex.
  assert (HP:1<=rrun w (Z.of_N(cap s))).
  { apply (gen_rrun_pos w h); [exact HW|lia|destruct Hex; [now left|right;lia]]. }
  destruct (gen_end_V w h HW) as [u Eu].
  apply (rreturns_reset_end b4 s w u); try assumption.
  apply ready_tfold_of_stops; [exact HA|exact HG|lia|].
  apply (gen_scan_stops w h); [exact HW|lia].
Qed.

(** The unique unextended base word over an exhausted counter is the
    small clock; the two pending 2 cells are an ordinary Y step. *)
Lemma exceptional_reset s : Good s ->cap s=0%N ->
  RReturns b4 (left s root {{A}}>S2>>cells(w0 2)*>0inf).
Proof.
  intros HG HC; set (q:=W::Z::s).
  assert (HQ:cap q=0%N) by (unfold q; cbn [cap]; rewrite HC; reflexivity).
  assert (HB:bval q=4*bval s+2).
  { unfold q; rewrite bval_W,bval_Z; cbn [cap]; rewrite HC.
    change (2*(2*bval s+1)=4*bval s+2); ring. }
  assert (HB0:0<=bval q) by (pose proof(good_bval_nonneg s HG); rewrite HB; lia).
  set (u:=pdec q++[Y]).
  assert (HU:rrun u 0=2*bval q+1) by (unfold u; rewrite rrun_app; reflexivity).
  assert (HU0:0<=rrun u 0) by (rewrite HU; lia).
  destruct(tfold_empty_props u HU0) as [HAt [HGt [HCt _]]].
  assert (Ht:(1<=cap(tfold [] u))%N) by (rewrite HU in HCt; lia).
  destruct(lemma_seven (tfold [] u) HGt Ht) as [HP HR].
  eapply rreturns_trans; [apply progress_evstep; apply right_Y|].
  eapply rreturns_trans; [apply progress_evstep; apply right_V|].
  change (RReturns b4 (left q root {{A}}>S1>>cells [Y;Y;V]*>0inf)).
  eapply rreturns_trans; [apply progress_evstep; apply right_one|].
  eapply rreturns_trans; [apply progress_evstep; apply overflow_root_run; exact HQ|].
  rewrite out_pdec.
  change (RReturns b4 (root {{A}}>S2>>cells(pdec q)*>dc Y*>S2>>cells[Y;V]*>0inf)).
  rewrite <-cells_snoc.
  eapply rreturns_trans; [apply reset_zero_run; exact HU0|].
  eapply rreturns_trans; [apply progress_evstep; apply right_Y|].
  apply (rreturns_counter_drain b4 (tfold [] u) [Y;V] O); [repeat constructor|exact HP|exact HR].
Qed.

Lemma overflow_gen s d w h : Adm s ->Good s ->Strict s ->cap s=0%N ->
  (d=D \/ d=V) ->(d=V ->pdec s<>[]) ->Gen w h ->
  RReturns b4 (left s root <{{A}} dc d*>S2>>cells w*>0inf).
Proof.
  intros HA HG HS HC Hd HneV HW.
  pose proof(good_bval_nonneg s HG) as HB.
  destruct(Z_le_dec 0 (rstep d (bval s))) as [Hclean|Hdirty].
  - assert (Hne:pdec s<>[]).
    { destruct Hd as [-> | ->]; [|now apply HneV].
      intro E; unfold bval in Hclean; rewrite E in Hclean; cbn [rrun rstep] in Hclean; lia. }
    set (u:=pdec s++[d]).
    assert (HU:0<=rrun u 0) by (unfold u; rewrite rrun_app; exact Hclean).
    destruct(tfold_empty_props u HU) as [HAt [HGt _]].
    destruct(lemmaC (tfold [] u) w h HGt (slack_early s d HA HS HB Hd Hclean Hne) HW)
      as [HP HR].
    eapply rreturns_trans; [apply progress_evstep; apply overflow_root_run; exact HC|].
    rewrite out_pdec,<-cells_snoc.
    eapply rreturns_trans; [apply reset_zero_run; exact HU|].
    eapply rreturns_trans; [apply progress_evstep; apply right_Y|].
    apply (rreturns_counter_drain b4 (tfold [] u) w h); [now apply gen_dyckrun|exact HP|exact HR].
  - assert (Ed:d=D) by (destruct Hd as [-> | ->]; [reflexivity|cbn [rstep] in Hdirty; lia]).
    subst d; assert (HB1:bval s<=1) by (cbn [rstep] in Hdirty; lia).
    destruct(pdec s) as [|x xs] eqn:Ep.
    + destruct(gen_start_Y w h HW) as [v ->].
      eapply rreturns_trans; [apply overflow_run; exact HC|].
      rewrite out_pdec,Ep; right; unfold root; apply xy_spinout_nonhalt.
    + assert (Hne:pdec s<>[]) by (rewrite Ep; discriminate).
      destruct(overflow_retry s HA HC ltac:(lia) Hne) as [HAq [HGq [HCq HBq]]].
      set (q:=W::tfold [] (pdec s)) in *.
      set (u:=pdec q++[Y]).
      assert (HU:rrun u 0=2*bval q+1) by (unfold u; rewrite rrun_app; reflexivity).
      assert (HU0:0<=rrun u 0) by (rewrite HU; lia).
      destruct(tfold_empty_props u HU0) as [HAt [HGt [HCt _]]].
      assert (Ht:(1<=cap(tfold [] u))%N) by (rewrite HU in HCt; lia).
      eapply rreturns_trans; [apply progress_evstep; apply overflow_root_run; exact HC|].
      rewrite out_pdec.
      eapply rreturns_trans; [apply reset_zero_run; exact HB|].
      eapply rreturns_trans; [apply progress_evstep; apply right_V|].
      eapply rreturns_trans; [apply progress_evstep; apply right_one|].
      eapply rreturns_trans; [apply progress_evstep; apply(overflow_root_run b4 q); exact HCq|].
      rewrite out_pdec.
      change (RReturns b4 (root {{A}}>S2>>cells(pdec q)*>dc Y*>cells w*>0inf)).
      rewrite <-cells_snoc.
      eapply rreturns_trans; [apply reset_zero_run; exact HU0|].
      apply (gen_reset (tfold [] u) w h); [exact HAt|exact HGt|now apply strict_reset_empty|exact HW|now right].
Qed.

Theorem zeven : ZEven b4.
Proof.
  intros s w h HA HG HS HW.
  destruct(N.eq_dec (cap s) 0) as [HC|HC].
  - apply (overflow_gen s D w h); auto; discriminate.
  - assert (H1:(0<cap s)%N) by lia.
    eapply rreturns_trans; [apply progress_evstep; apply cdec_run; exact H1|].
    eapply rreturns_trans; [apply progress_evstep; apply right_one|].
    destruct(N.eq_dec (cap(cdec s)) 0) as [HC1|HC1].
    + apply (overflow_gen (cdec s) V w h); auto using cdec_adm,cdec_good,strict_cdec.
      intros _ Hnil; rewrite cdec_pdec in Hnil.
      pose proof(capacity_one_bit s HA H1) as HB.
      pose proof(bal_pdec s); rewrite Hnil in H; cbn [bal] in H; lia.
    + assert (H2:(2<=cap s)%N) by (rewrite cdec_capacity in HC1 by exact H1; lia).
      assert (HP:(0<cap(cdec s))%N) by lia.
      eapply rreturns_trans; [apply progress_evstep; apply cdec_run; exact HP|].
      eapply rreturns_trans; [apply progress_evstep; apply right_V|].
      set (q:=W::cdec(cdec s)).
      assert (HAq:Adm q).
      { unfold q; rewrite <-cdec_W by exact H2; apply cdec_adm,adm_W;
        [exact HA|pose proof(capacity_two_bits s HA H2); lia]. }
      assert (HGq:Good q) by (unfold q; rewrite <-cdec_W by exact H2; now apply good_paid_W).
      assert (HSq:Strict q).
      { unfold q; apply strict_W; [now apply strict_cdec,strict_cdec|].
        destruct(cdec_counts s) as [EB ES]; destruct(cdec_counts(cdec s)) as [EB' ES'];
          rewrite EB',ES',EB,ES; pose proof(capacity_two_bits s HA H2); lia. }
      destruct(N.eq_dec (cap q) 0) as [HQ|HQ].
      * destruct(list_eq_dec rb_digit_eq_dec w (w0 2)) as [-> | Hne].
        -- apply (exceptional_reset q); assumption.
        -- apply (gen_reset q w h); auto; now left.
      * apply (gen_reset q w h); auto; right; lia.
Qed.
End Branch.
End BB25FamilyRBFinal.

Module TM_0RB.
Definition tm := Eval compute in (TM_from_str "1RB2LA0RB1LB---_1LA3RA1RA4LB0RB").
Theorem nonhalt : ~halts tm c0.
Proof.
  apply (nonhalt_of_zeven (regular(Some(S0,R,B))));
    [exact rb_pop_episode|exact first_episode|apply BB25FamilyRBFinal.zeven].
Qed.
End TM_0RB.

(* BB25FamilyTwo.v *)
Close Scope Z_scope. Close Scope N_scope.
From BusyCoq Require Import Individual25.
Open Scope sym_scope.
From Coq Require Import String List NArith ZArith Lia ZifyNat.
Import ListNotations BB25FamilyRules
  BB25FamilyCore BB25FamilyWord
  BB25FamilyStack BB25FamilyReset
  BB25FamilyMachine BB25FamilyDrain
  BB25FamilyBounds BB25FamilyReturn
  BB25FamilyCases BB25FamilyClosure
  BB25FamilyExcept.

(** Prefix/Two.lean, on the original machine configurations.  The residual
    12 block consumes the fourth decrement before the final pending 1. *)
Module BB25FamilyTwo.
Open Scope Z_scope.
Definition b4 := Some(S2,L,B).
Notation tm := (family b4).
Notation "c -->* c'" := (c -[tm]->* c') (at level 40).
Notation "c -->+ c'" := (c -[tm]->+ c') (at level 40).

Lemma two_turn s l r : (0<cap s)%N ->
  left s l <{{A}} [S1;S2;S1] *> r -->+
  left(cdec s) l <{{A}} [S2;S2;S1] *> r.
Proof.
  intro H; eapply progress_trans; [apply cdec_run; exact H|apply right_one].
Qed.

Theorem wcase_2LB_ord_weak s n : Adm s -> (0<=bval s)%Z ->
  (3*Z.of_N(cap s)<=4*bval s+14)%Z -> (4<=cap s)%N ->(1<=n)%nat ->
  Returns b4 (left s root <{{A}} [S1;S4;S1] *>
    cells(repeat Y n) *> S1 >> 0inf).
Proof.
  intros HA HB HC H4 Hn.
  assert (H2:(2<=cap(cdec(cdec s)))%N).
  { rewrite cap_cdec_twice by lia; lia. }
  assert (H3:(0<cap(cdec(cdec(cdec s))))%N).
  { rewrite cdec_capacity by lia; lia. }
  assert (HC4:cap(cdec(cdec(cdec(cdec s))))=(cap s-4)%N).
  { rewrite cap_cdec_twice by exact H2. rewrite cap_cdec_twice by lia; lia. }
  eapply returns_trans; [apply progress_evstep; apply case_two_decrements; lia|].
  eapply returns_trans; [apply progress_evstep; apply G_B_left|].
  eapply returns_trans; [apply progress_evstep; apply two_turn; lia|].
  eapply returns_trans; [apply progress_evstep; apply cdec_run; exact H3|].
  eapply returns_trans; [apply progress_evstep; apply right_Y|].
  eapply returns_trans; [apply progress_evstep; apply right_one|].
  eapply returns_trans; [apply progress_evstep; apply left_Z|].
  change (Returns b4 (left(X::cdec(cdec(cdec(cdec s)))) root {{A}}>
    S2 >> cells(repeat Y n) *> S1 >> 0inf)).
  apply returns_tail.
  - apply adm_X; repeat apply cdec_adm; exact HA.
  - rewrite bval_X,!cdec_bval. change
      (3*(Z.of_N(2*cap(cdec(cdec(cdec(cdec s)))))+1)<=4*(2*bval s+1+1))%Z.
    rewrite HC4; lia.
  - left; exact Hn.
Qed.

Theorem wcase_2LB_ord s n : Adm s ->Good s ->(4<=cap s)%N ->(1<=n)%nat ->
  Returns b4 (left s root <{{A}} [S1;S4;S1] *>
    cells(repeat Y n) *> S1 >> 0inf).
Proof.
  intros HA HG HC Hn. apply wcase_2LB_ord_weak; try assumption.
  - apply good_bval_nonneg; exact HG.
  - pose proof (good_bound s HG); lia.
Qed.

(** Numerical content of the double-pop checkpoint.  All divisions are
    binary N or Z; no trajectory or unary counter is used. *)
Lemma exc_2LB_arith (f:N) (bv bw bk:BinNums.Z) :
  (4<=f)%N -> Z.of_N f<=bv ->
  bw=(if N.odd f then 2*bv else bv/2-1) ->
  bk=(if N.odd(f/2) then 2*bw else bw/2-1) ->
  (N.odd f=true \/ 11<=bv) -> ((f mod 4=0)%N ->43<=bv) ->
  ~(Z.of_N(f/2)<=bw /\ Z.of_N(f/2/2)<=bk) ->
  (4<=f/2)%N /\ 0<=bw /\ 3*Z.of_N(f/2)<=4*bw+14 /\
  (2<=f/2/2)%N /\ Z.of_N(f/2/2)-2<=bk /\
  ((f/2/2 mod 2=0)%N ->3*(Z.of_N(f/2/2)/2)<=4*(bk/2)).
Proof.
  intros Hf HB HW HK HD HM Hbad.
  rewrite !odd_of_N in *.
  repeat rewrite N2Z.inj_div in *.
  change (Z.of_N 2) with 2 in *.
  destruct (Z.eqb_spec (Z.of_N f mod 2) 1) as [Ho|He];
    destruct (Z.eqb_spec (Z.of_N f/2 mod 2) 1) as [Ho2|He2];
    lazy beta iota in HW,HK,HD.
  all: lia.
Qed.

Theorem wcase_2LB_a3 s n : Adm s ->Good s ->cap s=3%N ->(1<=n)%nat ->
  Returns b4 (left s root <{{A}} [S1;S4;S1] *>
    cells(repeat Y n) *> S1 >> 0inf).
Proof.
  intros HA HG HC Hn.
  assert (HC2:cap(cdec(cdec s))=1%N) by (rewrite cap_cdec_twice by lia; rewrite HC; reflexivity).
  assert (HC3:cap(cdec(cdec(cdec s)))=0%N) by (rewrite cdec_capacity by lia; rewrite HC2; reflexivity).
  assert (HB:(3<=bval s)%Z) by (pose proof (good_bound s HG); rewrite HC in H; exact H).
  set (t:=tfold [] (pdec s)).
  destruct (tfold_empty_props (pdec s) ltac:(change (0<=bval s); lia))
    as [HAt [HGt [HCt [HBt Hbits]]]].
  change (Adm t) in HAt; change (Good t) in HGt.
  change (Z.of_N(cap t)=bval s) in HCt.
  assert (HAZ:Adm(Z::t)) by (apply adm_Z; exact HAt).
  assert (HO:N.odd(cap(Z::t))=true).
  { change (N.odd(2*cap t+1)=true); rewrite N.odd_add,N.odd_mul; reflexivity. }
  assert (HAW:Adm(W::Z::t)).
  { apply adm_W; [exact HAZ|]. pose proof (capacity_one_bit (Z::t) HAZ ltac:(cbn [cap]; lia)); lia. }
  assert (HGW:Good(W::Z::t)) by (apply good_W_odd; [apply good_Z; exact HGt|exact HO]).
  eapply returns_trans; [apply progress_evstep; apply case_two_decrements; lia|].
  eapply returns_trans; [apply progress_evstep; apply G_B_left|].
  eapply returns_trans; [apply progress_evstep; apply two_turn; lia|].
  eapply returns_trans; [apply progress_evstep; apply overflow_root_run; exact HC3|].
  rewrite out_pdec,!cdec_pdec.
  change (Returns b4 (root {{A}}> S2 >> cells(pdec s) *>
    dc Y *> S1 >> cells(repeat Y n) *> S1 >> 0inf)).
  rewrite <-cells_snoc.
  eapply returns_trans; [apply reset_zero_run|].
  - rewrite rrun_app. change (0<=2*bval s+1); lia.
  - rewrite tfold_app.
    change (Returns b4 (left(Z::t) root {{A}}> S2 >> S1 >>
      cells(repeat Y n) *> S1 >> 0inf)).
    eapply returns_trans; [apply progress_evstep; apply right_V|].
    change (Returns b4 (left(W::Z::t) root {{A}}> cells(repeat Y n) *> S1 >> 0inf)).
    apply returns_Yrun; try assumption; right.
    change (0<(2*cap t+1)/2)%N; lia.
Qed.

Lemma pushed_tail_bound s i : (2<=cap s)%N -> Z.of_N(cap s)-2<=bval s ->
  ((cap s mod 2=0)%N ->3*(Z.of_N(cap s)/2)<=4*(bval s/2)) ->
  (2<=cap(pushZ i s))%N /\
  3*(Z.of_N(cap(W::cdec(cdec(pushZ i s))))+1)<=
    4*(bval(W::cdec(cdec(pushZ i s)))+1).
Proof.
  intros HC HB HE.
  pose proof (pushZ_zcapacity i s) as EC.
  pose proof (pushZ_bval i s) as EB.
  pose proof (BB25FamilyWord.pow2_pos i) as HP.
  assert (HC' : (2<=cap(pushZ i s))%N) by nia.
  split; [exact HC'|].
  destruct (values_W_cdec2 (pushZ i s) HC') as [EW EV].
  rewrite EW,EV,N2Z.inj_div.
  assert (ES : Z.of_N(cap(pushZ i s)-2)=Z.of_N(cap(pushZ i s))-2) by lia.
  rewrite ES. change (Z.of_N 2) with 2.
  destruct (N.odd(cap(pushZ i s)-2)) eqn:HO.
  - rewrite odd_of_N in HO; apply Z.eqb_eq in HO; rewrite ES in HO.
    assert (Hbase:3*(Z.of_N(cap s)+1)+2<=16*(bval s+1)) by lia.
    assert (Hscaled:3*(BB25FamilyWord.pow2 i*(Z.of_N(cap s)+1))+
      2*BB25FamilyWord.pow2 i<=
      16*(BB25FamilyWord.pow2 i*(bval s+1))) by nia.
    lia.
  - assert (Hi:i=O).
    { destruct i as [|i]; [reflexivity|].
      pose proof (pushZ_odd (S i) s ltac:(left; lia)) as HS.
      rewrite odd_of_N in HS,HO. apply Z.eqb_eq in HS; apply Z.eqb_neq in HO.
      rewrite ES in HO; lia. }
    subst i; rewrite pushZ_zero in *.
    rewrite odd_of_N in HO; apply Z.eqb_neq in HO.
    assert (ES0 : Z.of_N(cap s-2)=Z.of_N(cap s)-2) by lia.
    rewrite ES0 in HO.
    assert (Hmod:(cap s mod 2=0)%N).
    { apply N2Z.inj. rewrite N2Z.inj_mod; change (Z.of_N(cap s) mod 2=0); lia. }
    specialize (HE Hmod); lia.
Qed.

Lemma returns_WWt t n : Adm t ->Good t ->(4<=cap t)%N ->
  (N.odd(cap t)=true \/ 11<=bval t) ->
  ((cap t mod 4=0)%N ->43<=bval t) ->(1<=n)%nat ->
  Returns b4 (left(W::W::t) root {{A}}> cells(repeat Y n) *> S1 >> 0inf).
Proof.
  intros HA HG HC HD HM Hn.
  pose proof (capacity_two_bits t HA ltac:(lia)) as Hbits.
  assert (HAW:Adm(W::t)) by (apply adm_W; [exact HA|lia]).
  assert (HAK:Adm(W::W::t)) by (apply adm_W; [exact HAW|cbn [nsh nbit]; lia]).
  assert (HGdec:
    {Z.of_N(cap t/2)<=bval(W::t) /\ Z.of_N(cap t/2/2)<=bval(W::W::t)}+
    {~(Z.of_N(cap t/2)<=bval(W::t) /\ Z.of_N(cap t/2/2)<=bval(W::W::t))}).
  { destruct (Z_le_dec (Z.of_N(cap t/2)) (bval(W::t)));
      destruct (Z_le_dec (Z.of_N(cap t/2/2)) (bval(W::W::t)));
      [left|right|right|right]; tauto. }
  destruct HGdec as [[HGW HGK]|Hbad].
  - apply returns_Yrun; try assumption.
    + split; [split; [exact HG|exact HGW]|exact HGK].
    + right; change (0<cap t/2/2)%N; lia.
  - pose proof (good_bound t HG) as HB.
    destruct (exc_2LB_arith (cap t) (bval t) (bval(W::t)) (bval(W::W::t))
      HC HB (bval_W t) (bval_W (W::t)) HD HM Hbad)
      as [HCW [HBW [Hweak [HCK [HBK HKE]]]]].
    destruct n as [|n]; [lia|].
    eapply returns_trans; [apply progress_evstep; apply Yrun_cp|].
    rewrite left_cons; cbn [tc].
    eapply returns_trans; [apply progress_evstep; apply B1_X|].
    destruct n as [|i].
    + rewrite pushZ_zero,left_cons; cbn [tc].
      eapply returns_trans; [apply progress_evstep; apply B1_W|].
      apply (wcase_2LB_ord_weak (W::t) 2); try assumption; lia.
    + rewrite pushZ_succ,left_cons; cbn [tc].
      eapply returns_trans; [apply progress_evstep; apply B1_Z|].
      destruct (pushed_tail_bound (W::W::t) i HCK HBK HKE) as [HCH HBH].
      apply (returns_dX_weak b4 (pushZ i (W::W::t)) 2).
      * apply pushZ_adm; exact HAK.
      * exact HCH.
      * exact HBH.
      * lia.
Qed.

Theorem wcase_2LB_exc s n : Adm s ->Good s ->cap s=2%N ->4<=bval s ->(1<=n)%nat ->
  Returns b4 (left s root <{{A}} [S1;S4;S1] *>
    cells(repeat Y n) *> S1 >> 0inf).
Proof.
  intros HA HG HC HB Hn.
  assert (HC2:cap(cdec(cdec s))=0%N) by (rewrite cap_cdec_twice by lia; rewrite HC; reflexivity).
  pose proof (capacity_two_bits s HA ltac:(lia)) as Hbits.
  destruct (paid_stack_facts s HA HG Hbits) as [HAt [HGt [HCt [HBt HDt]]]].
  set (t:=tfold [] (pdec s)) in *.
  assert (HD:N.odd(cap t)=true \/ 11<=bval t).
  { destruct HDt as [HDt|HDt]; [left; rewrite odd_of_N; apply Z.eqb_eq|right]; exact HDt. }
  assert (HM:(cap t mod 4=0)%N ->43<=bval t).
  { intro HE; unfold t; apply (paid_stack_mod_four s HA HG Hbits).
    rewrite <-HCt. change (Z.of_N(cap t) mod Z.of_N 4=0).
    rewrite <-N2Z.inj_mod,HE; reflexivity. }
  eapply returns_trans; [apply progress_evstep; apply case_two_decrements; lia|].
  eapply returns_trans; [apply progress_evstep; apply G_B_left|].
  eapply returns_trans; [apply progress_evstep; apply overflow_root_run; exact HC2|].
  rewrite out_pdec,!cdec_pdec.
  eapply returns_trans; [apply reset_zero_run; change (0<=bval s); lia|].
  eapply returns_trans; [apply progress_evstep; apply right_V|].
  eapply returns_trans; [apply progress_evstep; apply right_V|].
  change (Returns b4 (left(W::W::t) root {{A}}> cells(repeat Y n) *> S1 >> 0inf)).
  apply returns_WWt; try assumption; lia.
Qed.

Theorem wcase_2LB : WCase b4.
Proof.
  intros s n HA HG HC Hcrit Heven Hn.
  destruct (N.eq_dec (cap s) 2) as [H2|H2].
  - apply wcase_2LB_exc; try assumption; [apply Hcrit; exact H2|lia].
  - destruct (N.eq_dec (cap s) 3) as [H3|H3].
    + apply wcase_2LB_a3; try assumption; lia.
    + apply wcase_2LB_ord; try assumption; lia.
Qed.

End BB25FamilyTwo.

Module TM_2LB.
Definition tm := Eval compute in (TM_from_str "1RB2LA0RB1LB---_1LA3RA1RA4LB2LB").
Theorem nonhalt : ~halts tm c0.
Proof.
  change (~halts (family BB25FamilyTwo.b4) c0).
  apply family_nonhalt,BB25FamilyTwo.wcase_2LB.
Qed.
End TM_2LB.

(* BB25FamilySibling.v *)
Close Scope Z_scope. Close Scope N_scope.
From BusyCoq Require Import Individual25.
Open Scope sym_scope.
From Coq Require Import List NArith ZArith Lia String.
Import ListNotations BB25FamilyRules BB25FamilyCore BB25FamilyWord
  BB25FamilyStack BB25FamilyReset BB25FamilyMachine BB25FamilyDrain
  BB25FamilyBounds BB25FamilyReturn BB25FamilySeed BB25FamilyReady
  BB25FamilyMarker BB25FamilyDrainWord BB25FamilyRBGen BB25FamilyRBRun.

Module BB25FamilySibling.
Definition sibling := Control (Some(S4,R,B)) (Some(S0,L,B)).
Notation tm := (family sibling).
Notation "c -->* c'" := (c -[tm]->* c') (at level 40).
Notation "c -->+ c'" := (c -[tm]->+ c') (at level 40).

(** The sibling postpones both decrements until its protected right-hand
    excursion has returned. No change of the word/counter algebra is needed. *)
Lemma pop_start l r :
  l <* [S3;S0] <{{B}} S1>>r -->+ l <* [S3;S4;S0] {{A}}>r.
Proof. execute. Qed.
Lemma pop_end l r :
  l <* [S3;S4;S0] <{{A}} r -->+ l <{{A}} [S1;S0;S1]*>r.
Proof. execute. Qed.

Lemma pop_run s r t : (2<=cap s)%N ->
  (forall l,l {{A}}>r -->+ l <{{A}} t) ->forall l,
  left(W::s) l <{{B}} S1>>r -->+
  left(cdec(cdec s)) l <{{B}} S1>>dc Y*>t.
Proof.
  intros HC HR l.
  assert (H1:(0<cap s)%N) by lia.
  assert (H2:(0<cap(cdec s))%N) by (rewrite cdec_capacity by exact H1; lia).
  rewrite left_cons; cbn [tc].
  eapply progress_trans; [apply pop_start|].
  eapply progress_trans; [apply HR|].
  eapply progress_trans; [apply pop_end|].
  eapply progress_trans; [apply cdec_run; exact H1|].
  eapply progress_trans; [apply right_one|].
  eapply progress_trans; [apply cdec_run; exact H2|].
  apply right_N2.
Qed.

Lemma pop_word s w h : (2<=cap s)%N ->DyckRun O w h ->forall l,
  left(W::s) l <{{B}} S1>>cells w*>0inf -->+
  left(cdec(cdec s)) l <{{B}} S1>>cells(Y::(w++repeat D h++[V]))*>0inf.
Proof.
  intros HC HD l; cbn [cells flat_map]; rewrite Str_app_assoc.
  apply pop_run; [exact HC|intro; now apply marker_return_word].
Qed.

Lemma first_marker r : (2<=r)%nat ->forall l,
  l {{A}}>cells(repeat Y r)*>S1>>0inf -->+
  l <{{A}} cells(tl(w0 r))*>0inf.
Proof.
  intros Hr l; destruct r as [|[|r]]; [lia|lia|].
  change (left [] l {{A}}>cells(repeat Y(S(S r)))*>S1>>0inf -->+
    l <{{A}} cells(tl(w0(S(S r))))*>0inf).
  eapply evstep_progress_trans; [apply Yrun|].
  eapply progress_evstep_trans; [apply marker_tail_run|].
  destruct r as [|[|k]].
  - apply evstep_refl.
  - unfold marker_tail; cbn [pushZ Nat.iter left flat_map tc cells dc repeat w0 tl]; execute.
  - replace (S(S(S(S k)))) with (k+4)%nat by lia.
    rewrite w0_big; cbn [tl].
    replace (k+2)%nat with (S(S k)) by lia.
    apply progress_evstep,marker_drain.
Qed.

Lemma first_pop s r : (2<=cap s)%N ->(2<=r)%nat ->forall l,
  left(W::s) l <{{B}} S1>>cells(repeat Y r)*>S1>>0inf -->+
  left(cdec(cdec s)) l <{{B}} S1>>cells(w0 r)*>0inf.
Proof.
  intros HC Hr l.
  assert (E:w0 r=Y::tl(w0 r)).
  { destruct r as [|[|[|[|k]]]]; try lia; reflexivity. }
  rewrite E; cbn [cells flat_map]; rewrite Str_app_assoc.
  apply pop_run; [exact HC|intro; now apply first_marker].
Qed.

End BB25FamilySibling.

Module TM_Sibling.
Definition tm := Eval compute in (TM_from_str "1RB2LA0RB1LB---_1LA3RA1RA4RB0LB").
Theorem nonhalt : ~halts tm c0.
Proof.
  apply (nonhalt_of_zeven BB25FamilySibling.sibling).
  - exact BB25FamilySibling.pop_word.
  - exact BB25FamilySibling.first_pop.
  - apply BB25FamilyRBFinal.zeven.
Qed.
End TM_Sibling.

Print Assumptions TM_3RA.nonhalt.
Print Assumptions TM_2LA.nonhalt.
Print Assumptions TM_1RA.nonhalt.
Print Assumptions TM_0RA.nonhalt.
Print Assumptions TM_2RB.nonhalt.
Print Assumptions TM_0LA.nonhalt.
Print Assumptions TM_1LB.nonhalt.
Print Assumptions TM_2RA.nonhalt.
Print Assumptions TM_1RB.nonhalt.
Print Assumptions TM_2LB.nonhalt.
Print Assumptions TM_1LA.nonhalt.
Print Assumptions TM_0LB.nonhalt.
Print Assumptions TM_0RB.nonhalt.
Print Assumptions TM_Sibling.nonhalt.
