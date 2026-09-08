(* Self-contained column-flow proofs for test_48/TM1--TM8 and Skelet17/v2--v8.
   Only BusyCoq and the Coq standard library are required. *)

(* Column signals, finite lifetimes and infinite execution. *)

From Coq Require Import List Arith Bool Lia.
Import ListNotations.
Set Implicit Arguments.

Fixpoint Alt (p:bool) (n:nat) : list bool :=
  match n with 0 => [] | S n => p::Alt (negb p) n end.

Lemma Alt_length n : forall p, length (Alt p n)=n.
Proof. induction n; intros p; cbn; [reflexivity|rewrite IHn; reflexivity]. Qed.

Lemma odd_0 a : Nat.odd (a*2)=false.
Proof. rewrite Nat.odd_mul; cbn; apply andb_false_r. Qed.

Lemma odd_1 a : Nat.odd (1+a*2)=true.
Proof. rewrite Nat.odd_add, odd_0; reflexivity. Qed.

Lemma odd_S a : Nat.odd (S a)=negb (Nat.odd a).
Proof. rewrite Nat.odd_succ, Nat.negb_odd; reflexivity. Qed.

Lemma Alt_snoc n : forall p, Alt p (n+1)=Alt p n++[xorb (Nat.odd n) p].
Proof.
  induction n; intro p; cbn[Nat.add Alt app]; [destruct p; reflexivity|].
  rewrite IHn, odd_S; destruct p, (Nat.odd n); reflexivity.
Qed.

Lemma Alt_app_even p n m : Alt p (n*2+m)=Alt p (n*2)++Alt p m.
Proof.
  induction n; [reflexivity|].
  replace (S n*2) with (2+n*2) by lia.
  cbn[Nat.add Alt List.app]; rewrite negb_involutive, IHn; reflexivity.
Qed.

(* Successive I/P pairs of geometric alternating blocks. *)
Fixpoint Doubles b n := match n with
  | 0 => [] | S n => Alt false b ++ Alt true (b*2) ++ Doubles (b*4) n end.

Fixpoint Ladder p b n := match n with
  | 0 => [] | S n => Alt p (1+b) ++ Ladder p (b*2) n end.

Lemma Doubles_snoc n : forall b,
  Doubles b (n+1)=Doubles b n++Alt false (b*4^n)++Alt true (b*4^n*2).
Proof.
  induction n; intro b; cbn[Nat.add Doubles Nat.pow]; [rewrite Nat.mul_1_r, app_nil_r; reflexivity|].
  rewrite IHn; replace (b*4*4^n) with (b*(4*4^n)) by lia.
  rewrite !app_assoc; reflexivity.
Qed.

Section Flow.
Variable Edge : nat -> nat -> list nat -> Prop.
Variable retire : nat -> list bool.

Inductive LInc : bool -> list nat -> list nat -> Prop :=
| LInc_P a xs : LInc true (a::xs) (1+a::xs)
| LInc_I a xs ys : a<>0 -> LInc (Nat.odd a) xs ys ->
    LInc false (a::xs) (a::ys)
| LInc_edge a b kids : Edge a b kids -> LInc false [a] (b::kids).

Inductive Run : list bool -> list nat -> list nat -> Prop :=
| Run_nil xs : Run [] xs xs
| Run_cons p w xs ys zs : LInc p xs ys -> Run w ys zs -> Run (p::w) xs zs.

Lemma Run_app u v xs zs :
  Run (u++v) xs zs <-> exists ys, Run u xs ys /\ Run v ys zs.
Proof.
  split.
  - revert xs; induction u; cbn; intros xs H.
    + eauto using Run_nil.
    + inversion H; subst. destruct (IHu _ H5) as [cut [Hu Hv]].
      eauto using Run_cons.
  - intros [ys [H H']]. induction H; cbn; eauto using Run_cons.
Qed.

Lemma Run_P k a xs : Run (repeat true k) (a::xs) (a+k::xs).
Proof.
  revert a; induction k; intros; cbn.
  - rewrite Nat.add_0_r; constructor.
  - replace (a+S k) with (S a+k) by lia. econstructor; [constructor|apply IHk].
Qed.

Inductive Pass : list bool -> nat -> nat -> list bool -> Prop :=
| Pass_nil a : Pass [] a a []
| Pass_P w a b o : Pass w (1+a) b o -> Pass (true::w) a b o
| Pass_I w a b o : a<>0 -> Pass w a b o -> Pass (false::w) a b (Nat.odd a::o).

Lemma Pass_length w a b o : Pass w a b o -> length o <= length w.
Proof. intro H; induction H; cbn; lia. Qed.

Lemma Pass_sound w a b o : Pass w a b o ->
  forall xs ys, Run o xs ys -> Run w (a::xs) (b::ys).
Proof.
  intro H; induction H; intros xs ys Hr.
  - inversion Hr; subst; constructor.
  - econstructor; [constructor|eauto].
  - inversion Hr; subst. econstructor; [eapply LInc_I; eauto|eauto].
Qed.

Lemma Pass_app u v a b o : Pass (u++v) a b o ->
  exists c p q, Pass u a c p /\ Pass v c b q /\ o=p++q.
Proof.
  revert a o; induction u as [|s u IH]; cbn; intros a o H.
  - exists a, [], o; auto using Pass_nil.
  - inversion H; subst; match goal with
    | H : Pass (u++v) _ _ _ |- _ => destruct (IH _ _ H) as [c [p [q [Hp [Hq ->]]]]]
    end; eexists; eexists; eexists; repeat split; eauto using Pass_P, Pass_I.
Qed.

Lemma Pass_cat u v a b c p q : Pass u a b p -> Pass v b c q ->
  Pass (u++v) a c (p++q).
Proof. intro H; induction H; cbn; eauto using Pass_P, Pass_I. Qed.

Lemma Pass_two p a w b o : a<>0 \/ p=true -> Pass w (1+a) b o ->
  Pass (p::negb p::w) a b (xorb (Nat.odd a) p::o).
Proof.
  destruct p; cbn[negb]; intros H HP.
  - rewrite xorb_true_r, <- odd_S. apply Pass_P, Pass_I; [lia|assumption].
  - rewrite xorb_false_r.
    destruct H; [apply Pass_I; [assumption|apply Pass_P; assumption]|discriminate].
Qed.

Lemma Pass_alt_even p k a : a<>0 \/ p=true ->
  Pass (Alt p (k*2)) a (a+k) (Alt (xorb (Nat.odd a) p) k).
Proof.
  revert a; induction k; intros a H.
  - cbn; rewrite Nat.add_0_r; constructor.
  - replace (S k*2) with (2+k*2) by lia. cbn[Nat.add Alt].
    rewrite negb_involutive, Nat.add_succ_r.
    replace (negb (xorb (Nat.odd a) p)) with (xorb (Nat.odd (S a)) p)
      by (rewrite odd_S; destruct (Nat.odd a),p; reflexivity).
    apply Pass_two; [assumption|apply IHk; left; lia].
Qed.

Lemma Pass_Doubles n : forall b a, b<>0 -> a<>0 -> Nat.odd b=false -> Nat.odd a=false ->
  Pass (Doubles (b*2) n) a (a+b*(4^n-1)) (Doubles b n).
Proof.
  induction n; intros b a Hb Ha Eb Ea.
  - cbn[Doubles Nat.pow Nat.sub]; rewrite Nat.mul_0_r, Nat.add_0_r; constructor.
  - pose proof (@Pass_alt_even false b a (or_introl Ha)) as H1.
    rewrite Ea in H1; cbn[xorb] in H1.
    pose proof (@Pass_alt_even true (b*2) (a+b) (or_intror eq_refl)) as H2.
    rewrite Nat.odd_add, Ea, Eb in H2; cbn[xorb] in H2.
    assert (HP : 4^n<>0) by (apply Nat.pow_nonzero; lia).
    assert (E : Nat.odd (a+b+b*2)=false) by (rewrite !Nat.odd_add, Ea, Eb, odd_0; reflexivity).
    pose proof (IHn (b*4) (a+b+b*2) ltac:(lia) ltac:(lia)
      ltac:(rewrite Nat.odd_mul, Eb; reflexivity) E) as H3.
    cbn[Doubles Nat.pow].
    replace (a+b*(4*4^n-1)) with (a+b+b*2+b*4*(4^n-1))
      by (destruct (4^n); [contradiction|cbn; nia]).
    replace (b*2*4) with (b*4*2) by lia.
    eapply Pass_cat; [exact H1|eapply Pass_cat; [exact H2|exact H3]].
Qed.

Lemma Pass_alt_odd_P k a :
  Pass (Alt true (1+k*2)) a (1+a+k) (Alt (negb (Nat.odd a)) k).
Proof.
  cbn[Nat.add Alt]; apply Pass_P.
  replace (negb (Nat.odd a)) with (xorb (Nat.odd (S a)) false)
    by (rewrite odd_S; destruct (Nat.odd a); reflexivity).
  apply Pass_alt_even; left; lia.
Qed.

Lemma Pass_alt_odd_I k a : a<>0 ->
  Pass (Alt false (1+k*2)) a (a+k) (Alt (Nat.odd a) (1+k)).
Proof.
  intro H; cbn[Nat.add Alt]; apply Pass_I; [assumption|].
  replace (negb (Nat.odd a)) with (xorb (Nat.odd a) true)
    by (destruct (Nat.odd a); reflexivity).
  apply Pass_alt_even; auto.
Qed.

Lemma Pass_ladder_return n : forall t, t<>0 -> exists A o,
  Pass (Ladder false (t*2) n) t A o /\
  o++Alt (Nat.odd A) (1+A)=Alt (Nat.odd t) (1+t)++Ladder false (t*2) n.
Proof.
  induction n; intros t Ht.
  - exists t,[]; split; [constructor|cbn[Ladder app]; rewrite app_nil_r; reflexivity].
  - destruct (IHn (t*2) ltac:(lia)) as [A [o [HP HE]]].
    pose proof (@Pass_alt_odd_I t t Ht) as H; replace (t+t) with (t*2) in H by lia.
    exists A,(Alt (Nat.odd t) (1+t)++o); split.
    + cbn[Ladder]; eapply Pass_cat; eassumption.
    + rewrite <- app_assoc, HE, odd_0; reflexivity.
Qed.

Inductive Life : list bool -> list nat -> list bool -> list nat -> Prop :=
| Life_internal w a xs b o : xs<>[] -> Pass w a b o ->
    Life w (a::xs) (o++retire b) xs
| Life_terminal k u a b c o kids : Edge (a+k) b kids -> Pass u b c o ->
    Life (repeat true k++false::u) [a] (o++retire c) kids.

Inductive Lives : nat -> list bool -> list nat -> list bool -> list nat -> Prop :=
| Lives_nil w xs : Lives 0 w xs w xs
| Lives_cons n w xs v ys z zs : Life w xs v ys -> Lives n v ys z zs ->
    Lives (1+n) w xs z zs.

Lemma Lives_app n w xs v ys : Lives n w xs v ys -> forall m z zs,
  Lives m v ys z zs -> Lives (n+m) w xs z zs.
Proof. intro H; induction H; intros; cbn; eauto using Lives_nil, Lives_cons. Qed.

CoInductive InfiniteLife : list bool -> list nat -> Prop :=
| Life_more w xs v ys : Life w xs v ys -> InfiniteLife v ys -> InfiniteLife w xs.

Lemma Lives_infinite n w xs v ys : Lives n w xs v ys -> InfiniteLife v ys -> InfiniteLife w xs.
Proof. intro H; induction H; eauto using Life_more. Qed.

Lemma terminal_prefix k u p q : repeat true k++false::u=p++q ->
  (exists j, p=repeat true j) \/
  (exists v z, u=v++z /\ p=repeat true k++false::v).
Proof.
  revert p; induction k; intros [|s p] H; cbn in H.
  - left; exists 0; reflexivity.
  - inversion H; subst. right; exists p,q; auto.
  - left; exists 0; reflexivity.
  - inversion H; subst. destruct (IHk p H2) as [[j ->]|[v [z [Hu Hp]]]].
    + left; exists (S j); reflexivity.
    + right; exists v,z; cbn; subst; auto.
Qed.

Hypothesis Edge_size : forall a b kids, Edge a b kids -> length kids<=2.

Lemma InfiniteLife_nonempty w xs : InfiniteLife w xs -> xs<>[].
Proof. intros H E; destruct H as [w xs v ys H _]; inversion H; subst; discriminate. Qed.

Lemma Infinite_prefix_bound_size K
  (Edge_bound : forall a b kids, Edge a b kids -> length kids<=K) n : forall p q xs,
  length xs+length p*K<=n -> InfiniteLife (p++q) xs -> exists ys, Run p xs ys.
Proof.
  induction n as [|n IH]; intros p q xs Hn.
  - intro H. apply InfiniteLife_nonempty in H. destruct xs; cbn in Hn; congruence || lia.
  - remember (p++q) as w eqn:Ew. intros H.
    destruct H as [w xs v ys HL HI].
    destruct HL as [w a xs b o Hne HP | k u a b c o kids HE HP].
    + rewrite Ew in HP. destruct (Pass_app p q HP) as [d [o1 [o2 [H1 [H2 Eo]]]]].
      subst o. rewrite <- app_assoc in HI.
      destruct (IH o1 (o2++retire b) xs) as [ys Hr]; eauto.
      * apply Pass_length in H1. cbn in Hn; nia.
      * exists (d::ys); eapply Pass_sound; eauto.
    + destruct (terminal_prefix k u p q Ew) as [[j ->]|[u1 [u2 [Eu Ep]]]].
      * eauto using Run_P.
      * subst u p. destruct (Pass_app u1 u2 HP) as [d [o1 [o2 [H1 [H2 Eo]]]]].
        subst o. rewrite <- app_assoc in HI.
        destruct (IH o1 (o2++retire c) kids) as [ys Hr]; eauto.
        -- apply Edge_bound in HE. apply Pass_length in H1.
           rewrite length_app, repeat_length in Hn; cbn in Hn; nia.
        -- exists (d::ys). apply Run_app. eexists; split; [apply Run_P|].
           econstructor; [apply LInc_edge; exact HE|]. eapply Pass_sound; eauto.
Qed.

Hypothesis Edge_functional : forall a b kids c kids',
  Edge a b kids -> Edge a c kids' -> b=c /\ kids=kids'.

Lemma LInc_functional p xs ys : LInc p xs ys ->
  forall zs, LInc p xs zs -> ys=zs.
Proof.
  intro H; induction H; intros zs Hz; inversion Hz; subst; auto.
  - f_equal; eauto.
  - match goal with H : LInc _ [] _ |- _ => inversion H end.
  - match goal with H : LInc _ [] _ |- _ => inversion H end.
  - match goal with H1 : Edge ?a ?b ?u, H2 : Edge ?a ?c ?v |- _ =>
      destruct (Edge_functional H1 H2); congruence end.
Qed.

Lemma Run_functional w xs ys : Run w xs ys ->
  forall zs, Run w xs zs -> ys=zs.
Proof.
  intro H; induction H; intros last Hz; inversion Hz; subst; auto.
  match goal with H1 : LInc ?p ?xs ?ys, H2 : LInc ?p ?xs ?zs |- _ =>
    assert (ys=zs) by (eapply LInc_functional; eauto); subst end; eauto.
Qed.

Lemma Life_sound w xs v ys : Life w xs v ys -> forall zs, Run v ys zs ->
  exists a tail, Run w xs (a::tail) /\ Run (retire a) tail zs.
Proof.
  intro H; destruct H; intros zs HR; apply Run_app in HR; destruct HR as [cut [Ho Hr]].
  - eauto using Pass_sound.
  - exists c,cut; split; [|assumption]. apply Run_app.
    eexists; split; [apply Run_P|]. econstructor; [apply LInc_edge; eassumption|].
    eapply Pass_sound; eauto.
Qed.

Inductive Macro : list nat -> list nat -> Prop :=
| Macro_retire a xs ys : Run (retire a) xs ys -> Macro (a::xs) ys.

CoInductive InfiniteMacro : list nat -> Prop :=
| Macro_more xs ys : Macro xs ys -> InfiniteMacro ys -> InfiniteMacro xs.

Theorem InfiniteLife_sound_bounded K
  (Edge_bound : forall a b kids, Edge a b kids -> length kids<=K) w xs : InfiniteLife w xs ->
  forall ys, Run w xs ys -> InfiniteMacro ys.
Proof.
  revert w xs; cofix CIH; intros w xs HI ys HR.
  destruct HI as [w xs v pending HL HI].
  assert (HR' : InfiniteLife (v++[]) pending) by (rewrite app_nil_r; exact HI).
  destruct (@Infinite_prefix_bound_size K Edge_bound
    (length pending+length v*K) v [] pending ltac:(lia) HR') as [zs HZ].
  destruct (Life_sound HL HZ) as [a [tail [Hrun Hmacro]]].
  assert (ys=a::tail) by (eapply Run_functional; eauto); subst ys.
  econstructor; [constructor; eassumption|eapply (CIH v pending HI); exact HZ].
Qed.

Theorem InfiniteLife_sound w xs : InfiniteLife w xs ->
  forall ys, Run w xs ys -> InfiniteMacro ys.
Proof. apply (InfiniteLife_sound_bounded Edge_size). Qed.

End Flow.

Lemma Alt_flip n : forall p, map negb (Alt p n)=Alt (negb p) n.
Proof. induction n; intro p; cbn; [reflexivity|rewrite IHn; reflexivity]. Qed.

Lemma Pass_Doubles_odd n : forall b a, b<>0 -> a<>0 -> Nat.odd b=false -> Nat.odd a=true ->
  Pass (Doubles (b*2) n) a (a+b*(4^n-1)) (map negb (Doubles b n)).
Proof.
  induction n; intros b a Hb Ha Eb Ea.
  - cbn[Doubles Nat.pow Nat.sub map]; rewrite Nat.mul_0_r, Nat.add_0_r; constructor.
  - pose proof (@Pass_alt_even false b a (or_introl Ha)) as H1.
    rewrite Ea in H1; cbn[xorb] in H1.
    pose proof (@Pass_alt_even true (b*2) (a+b) (or_intror eq_refl)) as H2.
    rewrite Nat.odd_add, Ea, Eb in H2; cbn[xorb] in H2.
    assert (HP : 4^n<>0) by (apply Nat.pow_nonzero; lia).
    assert (E : Nat.odd (a+b+b*2)=true) by (rewrite !Nat.odd_add, Ea, Eb, odd_0; reflexivity).
    pose proof (IHn (b*4) (a+b+b*2) ltac:(lia) ltac:(lia)
      ltac:(rewrite Nat.odd_mul, Eb; reflexivity) E) as H3.
    cbn[Doubles Nat.pow]; rewrite !map_app, !Alt_flip; cbn[negb].
    replace (a+b*(4*4^n-1)) with (a+b+b*2+b*4*(4^n-1))
      by (destruct (4^n); [contradiction|cbn; nia]).
    replace (b*2*4) with (b*4*2) by lia.
    eapply Pass_cat; [exact H1|eapply Pass_cat; [exact H2|exact H3]].
Qed.

(* Unambiguous names for use beneath machine-local notations. *)
Notation Flow_LInc := LInc.
Notation Flow_Run := Run.
Notation Flow_Life := Life.
Notation Flow_Lives := Lives.
Notation Flow_Macro := Macro.
Notation Flow_InfiniteLife := InfiniteLife.
Notation Flow_InfiniteMacro := InfiniteMacro.

(* Finite right boundaries with a flag and multiple calls. *)

Section Frontier.
Variable F : Type.
Variable Edge : nat -> list nat -> F -> nat -> list nat -> F -> Prop.
Variable retire : nat -> list bool.

Inductive Frontier_LInc : bool -> list nat -> F -> list nat -> F -> Prop :=
| Frontier_LInc_P a xs f : Frontier_LInc true (a::xs) f (1+a::xs) f
| Frontier_LInc_I a xs f ys g : a<>0 -> Frontier_LInc (Nat.odd a) xs f ys g ->
    Frontier_LInc false (a::xs) f (a::ys) g
| Frontier_LInc_edge a xs f b kids g : Edge a xs f b kids g -> Frontier_LInc false (a::xs) f (b::kids) g.

Inductive Frontier_Run : list bool -> list nat -> F -> list nat -> F -> Prop :=
| Frontier_Run_nil xs f : Frontier_Run [] xs f xs f
| Frontier_Run_cons p w xs f ys g zs h : Frontier_LInc p xs f ys g -> Frontier_Run w ys g zs h -> Frontier_Run (p::w) xs f zs h.

Lemma Frontier_Run_app u v xs f zs h : Frontier_Run (u++v) xs f zs h <->
  exists ys g, Frontier_Run u xs f ys g /\ Frontier_Run v ys g zs h.
Proof.
  split.
  - revert xs f; induction u; cbn; intros xs f H.
    + eauto using Frontier_Run_nil.
    + inversion H as [|p w source f0 cut g0 target h0 HL HR]; subst.
      destruct (IHu _ _ HR) as [ys [g [HU HV]]]; eauto using Frontier_Run_cons.
  - intros [ys [g [H H']]]; induction H; cbn; eauto using Frontier_Run_cons.
Qed.

Lemma Frontier_Run_P k a xs f : Frontier_Run (repeat true k) (a::xs) f (a+k::xs) f.
Proof.
  revert a; induction k; intro a; cbn.
  - rewrite Nat.add_0_r; constructor.
  - replace (a+S k) with (S a+k) by lia; econstructor; [constructor|apply IHk].
Qed.

Lemma Frontier_Pass_sound w a b o : Pass w a b o -> forall xs f ys g,
  Frontier_Run o xs f ys g -> Frontier_Run w (a::xs) f (b::ys) g.
Proof.
  intro H; induction H; intros xs f ys g HR.
  - inversion HR; subst; constructor.
  - econstructor; [constructor|eauto].
  - inversion HR; subst; econstructor; [eapply Frontier_LInc_I; eauto|eauto].
Qed.

Lemma Frontier_Run_enter k w a xs f b kids g ys h : Edge (a+k) xs f b kids g ->
  Frontier_Run w (b::kids) g ys h -> Frontier_Run (repeat true k++false::w) (a::xs) f ys h.
Proof.
  intros HE HR; apply Frontier_Run_app; eexists; eexists; split; [apply Frontier_Run_P|].
  econstructor; [apply Frontier_LInc_edge; exact HE|exact HR].
Qed.

Inductive Frontier_Life : list bool -> list nat -> F -> list bool -> list nat -> F -> Prop :=
| Frontier_Life_internal w a xs f b o : xs<>[] -> Pass w a b o ->
    Frontier_Life w (a::xs) f (o++retire b) xs f
| Frontier_Life_border k u a xs f b c o kids g : Edge (a+k) xs f b kids g -> Pass u b c o ->
    Frontier_Life (repeat true k++false::u) (a::xs) f (o++retire c) kids g
| Frontier_Life_double k j u a xs f b mid g c kids h d o :
    Edge (a+k) xs f b mid g -> Edge (b+j) mid g c kids h -> Pass u c d o ->
    Frontier_Life (repeat true k++false::(repeat true j++false::u)) (a::xs) f (o++retire d) kids h.

Inductive Frontier_Lives : nat -> list bool -> list nat -> F -> list bool -> list nat -> F -> Prop :=
| Frontier_Lives_nil w xs f : Frontier_Lives 0 w xs f w xs f
| Frontier_Lives_cons n w xs f v ys g z zs h : Frontier_Life w xs f v ys g -> Frontier_Lives n v ys g z zs h ->
    Frontier_Lives (1+n) w xs f z zs h.

Lemma Frontier_Lives_app n w xs f v ys g : Frontier_Lives n w xs f v ys g -> forall m z zs h,
  Frontier_Lives m v ys g z zs h -> Frontier_Lives (n+m) w xs f z zs h.
Proof. intro H; induction H; intros; cbn; eauto using Frontier_Lives_nil, Frontier_Lives_cons. Qed.

CoInductive Frontier_InfiniteLife : list bool -> list nat -> F -> Prop :=
| Frontier_Life_more w xs f v ys g : Frontier_Life w xs f v ys g -> Frontier_InfiniteLife v ys g -> Frontier_InfiniteLife w xs f.

Variable K : nat.
Hypothesis Edge_size : forall a xs f b kids g, Edge a xs f b kids g -> length kids<=K.

Lemma Frontier_InfiniteLife_nonempty w xs f : Frontier_InfiniteLife w xs f -> xs<>[].
Proof. intros H E; destruct H as [w xs f v ys g H _]; inversion H; subst; discriminate. Qed.

Lemma Frontier_Infinite_prefix_bound n : forall p q xs f,
  length xs+length p*K<=n -> Frontier_InfiniteLife (p++q) xs f -> exists ys g, Frontier_Run p xs f ys g.
Proof.
  induction n as [|n IH]; intros p q xs f Hn.
  - intro H; apply Frontier_InfiniteLife_nonempty in H; destruct xs; cbn in Hn; congruence || lia.
  - remember (p++q) as w eqn:Ew; intros H; destruct H as [w xs f v ys g HL HI].
    destruct HL as [w a xs f b o Hne HP|k u a xs f b c o kids g HE HP|
      k j u a xs f b mid g c kids h d o HE HE' HP].
    + rewrite Ew in HP; destruct (Pass_app p q HP) as [d [o1 [o2 [H1 [H2 Eo]]]]].
      subst o; rewrite <- app_assoc in HI.
      destruct (IH o1 (o2++retire b) xs f) as [ys [g HR]]; eauto.
      * apply Pass_length in H1; cbn in Hn; nia.
      * exists (d::ys),g; eapply Frontier_Pass_sound; eauto.
    + destruct (terminal_prefix k u p q Ew) as [[j ->]|[u1 [u2 [Eu Ep]]]].
      * eauto using Frontier_Run_P.
      * subst u p; destruct (Pass_app u1 u2 HP) as [d [o1 [o2 [H1 [H2 Eo]]]]].
        subst o; rewrite <- app_assoc in HI.
        destruct (IH o1 (o2++retire c) kids g) as [ys [h HR]]; eauto.
        -- apply Edge_size in HE; apply Pass_length in H1.
           rewrite length_app, repeat_length in Hn; cbn in Hn; nia.
        -- exists (d::ys),h; apply Frontier_Run_app; eexists; eexists; split; [apply Frontier_Run_P|].
           econstructor; [apply Frontier_LInc_edge; exact HE|eapply Frontier_Pass_sound; eauto].
    + destruct (terminal_prefix k (repeat true j++false::u) p q Ew)
        as [[v ->]|[u1 [u2 [Eu Ep]]]].
      * eauto using Frontier_Run_P.
      * subst p; destruct (terminal_prefix j u u1 u2 Eu) as [[v ->]|[v1 [v2 [Ev Ef]]]].
        -- exists (b+v::mid),g; eapply Frontier_Run_enter; [exact HE|apply Frontier_Run_P].
        -- subst u u1; destruct (Pass_app v1 v2 HP) as [z [o1 [o2 [H1 [H2 Eo]]]]].
           subst o; rewrite <- app_assoc in HI.
           destruct (IH o1 (o2++retire d) kids h) as [ys [s HR]]; eauto.
           ++ apply Edge_size in HE'; apply Pass_length in H1.
              rewrite !length_app, !repeat_length in Hn; cbn in Hn.
              rewrite length_app, repeat_length in Hn; cbn in Hn; nia.
           ++ exists (z::ys),s; eapply Frontier_Run_enter; [exact HE|].
              eapply Frontier_Run_enter; [exact HE'|eapply Frontier_Pass_sound; eauto].
Qed.

Hypothesis LInc_functional : forall p xs f ys g zs h,
  Frontier_LInc p xs f ys g -> Frontier_LInc p xs f zs h -> ys=zs /\ g=h.

Lemma Frontier_Run_functional w xs f ys g : Frontier_Run w xs f ys g -> forall zs h,
  Frontier_Run w xs f zs h -> ys=zs /\ g=h.
Proof.
  intro H; induction H; intros last flag HZ; inversion HZ; subst; auto.
  match goal with H1 : Frontier_LInc ?p ?xs ?f ?ys ?g, H2 : Frontier_LInc ?p ?xs ?f ?zs ?h |- _ =>
    destruct (LInc_functional H1 H2); subst end; eauto.
Qed.

Lemma Frontier_Life_sound w xs f v ys g : Frontier_Life w xs f v ys g -> forall zs h, Frontier_Run v ys g zs h ->
  exists a tail s, Frontier_Run w xs f (a::tail) s /\ Frontier_Run (retire a) tail s zs h.
Proof.
  intro H; destruct H; intros zs flag HR; apply Frontier_Run_app in HR;
    destruct HR as [cut [s [Ho Hr]]].
  - exists b,cut,s; split; [eapply Frontier_Pass_sound; eassumption|assumption].
  - exists c,cut,s; split; [|assumption]; apply Frontier_Run_app.
    eexists; eexists; split; [apply Frontier_Run_P|].
    econstructor; [apply Frontier_LInc_edge; eassumption|eapply Frontier_Pass_sound; eauto].
  - exists d,cut,s; split; [|assumption].
    eapply Frontier_Run_enter; [eassumption|eapply Frontier_Run_enter; [eassumption|eapply Frontier_Pass_sound; eauto]].
Qed.

Inductive Frontier_Macro : list nat -> F -> list nat -> F -> Prop :=
| Frontier_Macro_retire a xs f ys g : Frontier_Run (retire a) xs f ys g -> Frontier_Macro (a::xs) f ys g.

CoInductive Frontier_InfiniteMacro : list nat -> F -> Prop :=
| Frontier_Macro_more xs f ys g : Frontier_Macro xs f ys g -> Frontier_InfiniteMacro ys g -> Frontier_InfiniteMacro xs f.

Theorem Frontier_InfiniteLife_sound w xs f : Frontier_InfiniteLife w xs f -> forall ys g,
  Frontier_Run w xs f ys g -> Frontier_InfiniteMacro ys g.
Proof.
  revert w xs f; cofix CIH; intros w xs f HI ys g HR.
  destruct HI as [w xs f v pending s HL HI].
  assert (HR' : Frontier_InfiniteLife (v++[]) pending s) by (rewrite app_nil_r; exact HI).
  destruct (@Frontier_Infinite_prefix_bound (length pending+length v*K) v [] pending s ltac:(lia) HR')
    as [zs [h HZ]].
  destruct (Frontier_Life_sound HL HZ) as [a [tail [u [Hrun Hmacro]]]].
  destruct (Frontier_Run_functional HR Hrun); subst.
  econstructor; [constructor; eassumption|eapply (CIH v pending s HI); exact HZ].
Qed.
End Frontier.

(* Balanced rotor stacks and last-exit certificates. *)

(* A finite rotor-stack certificate.  Rows are indexed by vertices; each row
   lists successive destinations.  These lists are logical certificates, not
   objects which the final proof has to evaluate or simulate explicitly. *)
Definition mark (i j:nat) := if Nat.eq_dec i j then 1 else 0.
Definition incoming (rows:list (list nat)) v := count_occ Nat.eq_dec (concat rows) v.
Definition outgoing (rows:list (list nat)) v := length (nth v rows []).
Definition Balance rows start sink := forall v,
  incoming rows v + mark start v = outgoing rows v + mark sink v.
Definition LastForest (rank:nat->nat) (rows:list (list nat)) := forall i,
  nth i rows [] <> [] -> rank (last (nth i rows []) 0) < rank i.

Inductive Pop : nat -> nat -> list (list nat) -> list (list nat) -> Prop :=
| Pop_here j xs rows : Pop 0 j ((j::xs)::rows) (xs::rows)
| Pop_later i j xs rows rows' : Pop i j rows rows' ->
  Pop (1+i) j (xs::rows) (xs::rows').

Lemma mark_self i : mark i i=1.
Proof. unfold mark; destruct (Nat.eq_dec i i); congruence. Qed.

Lemma mark_other i j : i<>j -> mark i j=0.
Proof. unfold mark; destruct (Nat.eq_dec i j); congruence. Qed.

Lemma Pop_get i j rows rows' : Pop i j rows rows' ->
  nth i rows []=j::nth i rows' [].
Proof. intro H; induction H; cbn; congruence. Qed.

Lemma Pop_other i j rows rows' : Pop i j rows rows' -> forall v, v<>i ->
  nth v rows []=nth v rows' [].
Proof. intro H; induction H; intros [|v] Hne; cbn; try reflexivity; try lia; apply IHPop; lia. Qed.

Lemma Pop_exists rows : forall i j xs, nth i rows []=j::xs -> exists rows', Pop i j rows rows'.
Proof.
  induction rows as [|ys rows IH]; intros [|i] j xs H; cbn in H; try discriminate.
  - subst ys; eauto using Pop_here.
  - destruct (IH _ _ _ H) as [rows' HP]; eauto using Pop_later.
Qed.

Lemma Pop_outgoing i j rows rows' : Pop i j rows rows' -> forall v,
  outgoing rows v=outgoing rows' v+mark i v.
Proof.
  intros H v; unfold outgoing; destruct (Nat.eq_dec i v) as [->|Hne].
  - rewrite (Pop_get H), mark_self; cbn; lia.
  - rewrite (Pop_other (v:=v) H ltac:(lia)), mark_other by assumption; lia.
Qed.

Lemma Pop_incoming i j rows rows' : Pop i j rows rows' -> forall v,
  incoming rows v=incoming rows' v+mark j v.
Proof.
  intro H; induction H; intro v; unfold incoming in *; cbn.
  - unfold mark; destruct (Nat.eq_dec j v); cbn; lia.
  - rewrite !count_occ_app, IHPop; lia.
Qed.

Lemma Pop_budget i j rows rows' : Pop i j rows rows' ->
  length (concat rows)=1+length (concat rows').
Proof. intro H; induction H; cbn; rewrite ?length_app in *; lia. Qed.

Lemma Pop_length i j rows rows' : Pop i j rows rows' -> length rows=length rows'.
Proof. intro H; induction H; cbn; congruence. Qed.

Lemma Pop_balance i j rows rows' sink : Pop i j rows rows' ->
  Balance rows i sink -> Balance rows' j sink.
Proof.
  intros HP HB v; specialize (HB v).
  rewrite (Pop_incoming HP), (Pop_outgoing HP) in HB; lia.
Qed.

Lemma Balance_stuck rows i sink : Balance rows i sink -> outgoing rows i=0 -> i=sink.
Proof.
  intros HB HE; specialize (HB i); rewrite mark_self, HE in HB.
  destruct (Nat.eq_dec sink i); [congruence|rewrite mark_other in HB by assumption; lia].
Qed.

Lemma last_in xs : xs<>[] -> In (last xs 0) xs.
Proof.
  induction xs as [|a xs IH]; intro H; [contradiction|].
  destruct xs as [|b xs]; [cbn; auto|cbn; right; apply IH; discriminate].
Qed.

Lemma incoming_positive rows i j : In j (nth i rows []) -> 0<incoming rows j.
Proof.
  intro H; unfold incoming; apply (proj1 (count_occ_In Nat.eq_dec _ _)).
  apply in_concat; exists (nth i rows []); split; [|exact H].
  apply nth_In; destruct (lt_dec i (length rows)); [assumption|].
  rewrite nth_overflow in H by lia; contradiction.
Qed.
Arguments incoming_positive rows i {j} _.

(* Finite execution consumes one destination per step.  The theorem below
   forces both the endpoint and every row to be exhausted. *)
Inductive StackWalk : nat -> list (list nat) -> nat -> list (list nat) -> nat -> Prop :=
| StackWalk_nil i rows : StackWalk i rows i rows 0
| StackWalk_cons i j k rows rows' rows'' n : Pop i j rows rows' ->
  StackWalk j rows' k rows'' n -> StackWalk i rows k rows'' (1+n).

Lemma StackWalk_stuck i rows j rows' n : StackWalk i rows j rows' n ->
  nth i rows []=[] -> i=j /\ n=0 /\ rows=rows'.
Proof.
  intros H HE; inversion H; subst; [auto|].
  match goal with HP : Pop _ _ _ _ |- _ => rewrite (Pop_get HP) in HE end; discriminate.
Qed.

(* A finite prefix may finish at an internal vertex which it visited earlier.
   Only cycles avoiding that designated endpoint must be excluded. *)
Definition LastForestExcept (rank:nat->nat) rows sink := forall i,
  i<>sink -> nth i rows []<>[] -> rank (last (nth i rows []) 0)<rank i.

Lemma Pop_forest_except i j rows rows' rank sink : Pop i j rows rows' ->
  LastForestExcept rank rows sink -> LastForestExcept rank rows' sink.
Proof.
  intros HP HF v HV Hne; destruct (Nat.eq_dec v i) as [->|Hvi].
  - specialize (HF i HV); rewrite (Pop_get HP) in HF.
    destruct (nth i rows' []) as [|a xs]; [contradiction|apply HF; discriminate].
  - rewrite <- (Pop_other HP Hvi) in *; auto.
Qed.

Lemma Balance_closed_except rows sink rank : Balance rows sink sink ->
  LastForestExcept rank rows sink -> outgoing rows sink=0 ->
  forall i, nth i rows []=[].
Proof.
  intros HB HF HE.
  assert (H : forall n i, rank i<n -> nth i rows []=[]).
  { induction n as [|n IH]; intros i HI; [lia|].
    destruct (nth i rows []) as [|a xs] eqn:E; [reflexivity|].
    assert (HN : nth i rows []<>[]) by congruence.
    assert (HS : i<>sink) by (intro ES; subst i; unfold outgoing in HE; rewrite E in HE; discriminate).
    pose proof (HF i HS HN) as HR.
    pose proof (incoming_positive rows i (last_in HN)) as HP.
    specialize (HB (last (nth i rows []) 0)).
    unfold outgoing in HB; rewrite (IH (last (nth i rows []) 0) ltac:(lia)) in HB; cbn in HB; lia. }
  intro i; apply (H (1+rank i)); lia.
Qed.

Theorem stack_certificate_except rows start sink rank :
  Balance rows start sink -> LastForestExcept rank rows sink ->
  exists rows', StackWalk start rows sink rows' (length (concat rows)) /\
    forall i, nth i rows' []=[].
Proof.
  remember (length (concat rows)) as n eqn:E; revert rows start E.
  induction n as [|n IH]; intros rows start E HB HF.
  - assert (HE : outgoing rows start=0).
    { unfold outgoing; destruct (nth start rows []) as [|a xs] eqn:HR; [reflexivity|].
      pose proof (incoming_positive rows start (j:=a) ltac:(rewrite HR; left; reflexivity)).
      unfold incoming in H; destruct (concat rows); cbn in *; lia. }
    pose proof (Balance_stuck HB HE) as ->.
    exists rows; split; [constructor|eapply Balance_closed_except; eassumption].
  - destruct (nth start rows []) as [|j xs] eqn:HR.
    + assert (HE : outgoing rows start=0) by (unfold outgoing; rewrite HR; reflexivity).
      pose proof (Balance_stuck HB HE) as ->.
      pose proof (Balance_closed_except HB HF HE) as HZ.
      assert (HL : concat rows=[]).
      { clear -HZ; induction rows as [|xs rows IH]; [reflexivity|].
        specialize (HZ 0) as H0; cbn in H0; subst xs; cbn.
        apply IH; intro i; exact (HZ (1+i)). }
      rewrite HL in E; discriminate.
    + destruct (Pop_exists rows start HR) as [rows' HP].
      destruct (IH rows' j ltac:(pose proof (Pop_budget HP); lia)
        (Pop_balance HP HB) (Pop_forest_except HP HF)) as [rows'' [HW HZ]].
      exists rows''; split; [eapply StackWalk_cons; eassumption|exact HZ].
Qed.

Theorem stack_certificate rows start sink rank :
  Balance rows start sink -> LastForest rank rows ->
  exists rows', StackWalk start rows sink rows' (length (concat rows)) /\
    forall i, nth i rows' []=[].
Proof.
  intros HB HF; eapply stack_certificate_except; [exact HB|].
  intros i _; apply HF.
Qed.

(* Algebraic verification of certificates uses row lengths and counts only. *)
Fixpoint weighted (rows:list (list nat)) base v :=
  match rows with [] => 0 | xs::rows => length xs*mark base v + weighted rows (1+base) v end.

Lemma mark_succ i j : mark (1+i) (1+j)=mark i j.
Proof. unfold mark; destruct (Nat.eq_dec (1+i) (1+j)), (Nat.eq_dec i j); lia. Qed.

Lemma weighted_shift rows : forall k v, weighted rows (1+k) (1+v)=weighted rows k v.
Proof. induction rows; intros; cbn[weighted]; rewrite ?mark_succ, ?IHrows; reflexivity. Qed.

Lemma weighted_outgoing rows : forall v, weighted rows 0 v=outgoing rows v.
Proof.
  induction rows as [|xs rows IH]; intros [|v]; cbn[weighted outgoing nth]; try reflexivity.
  - rewrite mark_self.
    assert (H : forall rows k, weighted rows (1+k) 0=0).
    { induction rows0 as [|ys rows0 IH0]; intros; cbn[weighted]; rewrite ?mark_other, ?IH0 by lia; lia. }
    rewrite H; unfold outgoing; cbn; lia.
  - rewrite mark_other by lia; rewrite weighted_shift, IH; unfold outgoing; cbn; lia.
Qed.

Lemma weighted_app rows : forall tail base v,
  weighted (rows++tail) base v=weighted rows base v+weighted tail (length rows+base) v.
Proof.
  induction rows; intros; cbn[weighted length app]; [reflexivity|].
  rewrite IHrows; replace (length rows+(1+base)) with (1+length rows+base) by lia.
  cbn[Nat.add]; lia.
Qed.

Definition Cycles (xs:list nat) n := concat (repeat xs n).

Lemma Cycles_length xs n : length (Cycles xs n)=n*length xs.
Proof.
  induction n; [reflexivity|change (length (xs++Cycles xs n)=(1+n)*length xs)].
  rewrite length_app, IHn; lia.
Qed.

Lemma Cycles_count xs n v : count_occ Nat.eq_dec (Cycles xs n) v=n*count_occ Nat.eq_dec xs v.
Proof.
  induction n; [reflexivity|change (count_occ Nat.eq_dec (xs++Cycles xs n) v=(1+n)*count_occ Nat.eq_dec xs v)].
  rewrite count_occ_app, IHn; lia.
Qed.

Lemma count_cons x xs v : count_occ Nat.eq_dec (x::xs) v=mark x v+count_occ Nat.eq_dec xs v.
Proof. unfold mark; cbn; destruct (Nat.eq_dec x v); lia. Qed.

Lemma last_suffix xs ys : ys<>[] -> last (xs++ys) 0=last ys 0.
Proof.
  induction xs as [|x xs IH]; intro H; [reflexivity|].
  destruct xs as [|a xs]; [destruct ys; cbn in *; congruence|cbn; apply IH; assumption].
Qed.

(* The position in a row is the number of previous visits, not just its
   residue.  Keeping it in the predicate will also locate the unique exit. *)
Fixpoint Indexed (R:nat->nat->Prop) a xs : Prop :=
  match xs with [] => True | j::xs => R a j /\ Indexed R (1+a) xs end.

Lemma Indexed_app R xs : forall ys a,
  Indexed R a (xs++ys) <-> Indexed R a xs /\ Indexed R (length xs+a) ys.
Proof.
  induction xs; intros; cbn[Indexed app length]; [tauto|].
  rewrite IHxs; replace (length xs+(1+a0)) with (1+(length xs+a0)) by lia; tauto.
Qed.

Lemma Indexed_cycles R word tail :
  (forall a, Indexed R (a*length word) word) ->
  (forall a, Indexed R (a*length word) tail) ->
  forall n a, Indexed R (a*length word) (Cycles word n++tail).
Proof.
  intros HW HT; induction n; intro a; [apply HT|].
  change (Indexed R (a*length word) ((word++Cycles word n)++tail)).
  rewrite <- app_assoc, Indexed_app; split; [apply HW|].
  replace (length word+a*length word) with ((1+a)*length word) by lia; apply IHn.
Qed.

Lemma Indexed_in R xs : forall a j, Indexed R a xs -> In j xs ->
  exists b, a<=b /\ R b j.
Proof.
  induction xs as [|x xs IH]; intros a j HR HJ; [contradiction|].
  destruct HR as [HX HT]; destruct HJ as [<-|HJ]; [exists a; auto|].
  destruct (IH _ _ HT HJ) as [b [HB H]]; exists b; split; [lia|assumption].
Qed.
Arguments Indexed_in {R xs a j} _ _.

Lemma Indexed_mono R S xs : (forall a j, R a j -> S a j) ->
  forall a, Indexed R a xs -> Indexed S a xs.
Proof.
  intro H; induction xs; intros a0 HR; cbn in *; [exact I|].
  destruct HR; split; [eapply H; eassumption|eapply IHxs; eassumption].
Qed.

Lemma incoming_witness rows j : 0<incoming rows j ->
  exists i, i<length rows /\ In j (nth i rows []).
Proof.
  intro H; unfold incoming in H; apply (proj2 (count_occ_In Nat.eq_dec _ _)) in H.
  apply in_concat in H; destruct H as [xs [HX HJ]].
  apply In_nth with (d:=[]) in HX; destruct HX as [i [HI HE]].
  exists i; split; [assumption|rewrite HE; assumption].
Qed.

Lemma Cycles_snoc xs n : Cycles xs (1+n)=Cycles xs n++xs.
Proof.
  induction n; [change (xs++[]=xs); apply app_nil_r|].
  change (xs++Cycles xs (1+n)=(xs++Cycles xs n)++xs).
  rewrite IHn, app_assoc; reflexivity.
Qed.

Lemma Cycles_last xs n : xs<>[] -> n<>0 -> last (Cycles xs n) 0=last xs 0.
Proof. intros HX HN; destruct n; [contradiction|rewrite Cycles_snoc; apply last_suffix; assumption]. Qed.

(* Nonnegative counters and finite evaluation. *)

Inductive Split : bool -> nat -> nat -> nat -> Prop :=
| Split_even e a : Split e (a*2) a a
| Split_odd0 a : Split false (1+a*2) a (1+a)
| Split_odd1 a : Split true (1+a*2) (1+a) a.

Lemma Split_mass e n q r : Split e n q r -> n=q+r.
Proof. intro H; destruct H; lia. Qed.

Lemma Split_functional e n q r q' r' :
  Split e n q r -> Split e n q' r' -> q=q' /\ r=r'.
Proof. intros H H'; destruct H; inversion H'; subst; lia. Qed.

Lemma Split_mono e a q r b q' r' :
  Split e a q r -> Split e b q' r' -> a<=b -> q<=q' /\ r<=r'.
Proof. intros H H'; destruct H; inversion H'; subst; lia. Qed.

Lemma Split_succ e a q r : Split e a q r -> exists q' r', Split e (1+a) q' r'.
Proof.
  intro H; destruct H.
  - destruct e; eauto using Split_odd0, Split_odd1.
  - replace (1+(1+a*2)) with ((1+a)*2) by lia; eauto using Split_even.
  - replace (1+(1+a*2)) with ((1+a)*2) by lia; eauto using Split_even.
Qed.

Lemma Split_total e n : exists q r, Split e n q r.
Proof.
  induction n.
  - exists 0,0; apply (Split_even e 0).
  - destruct IHn as [q [r H]]; eapply Split_succ; exact H.
Qed.

Fixpoint total (xs:list nat) := match xs with [] => 0 | a::xs => a+total xs end.

Lemma total_app xs ys : total (xs++ys)=total xs+total ys.
Proof. induction xs; cbn; lia. Qed.

Inductive Scatter : list bool -> list nat -> list nat -> nat -> Prop :=
| Scatter_nil : Scatter [] [] [] 0
| Scatter_cons e a q r es xs qs s : Split e a q r -> Scatter es xs qs s ->
    Scatter (e::es) (a::xs) (q::qs) (r+s).

Lemma Scatter_length es xs qs r : Scatter es xs qs r ->
  length xs=length es /\ length qs=length es.
Proof. intro H; induction H; cbn; lia. Qed.

Lemma Scatter_zeros es : Scatter es (repeat 0 (length es)) (repeat 0 (length es)) 0.
Proof.
  induction es; cbn; [constructor|exact (Scatter_cons (Split_even a 0) IHes)].
Qed.

Lemma Scatter_mass es xs qs r : Scatter es xs qs r -> total xs=total qs+r.
Proof. intro H; induction H; cbn; [reflexivity|apply Split_mass in H; lia]. Qed.

Lemma Scatter_app es xs qs r : Scatter es xs qs r ->
  forall es' xs' qs' r', Scatter es' xs' qs' r' ->
  Scatter (es++es') (xs++xs') (qs++qs') (r+r').
Proof.
  intro H; induction H; cbn; intros es' xs' qs' r' H'; [assumption|].
  replace (r+s+r') with (r+(s+r')) by lia; econstructor; eauto.
Qed.

Lemma Scatter_single e a q r : Split e a q r -> Scatter [e] [a] [q] r.
Proof. intro H; replace r with (r+0) by lia; econstructor; [exact H|constructor]. Qed.

Lemma Scatter_total es xs : length es=length xs -> exists qs r, Scatter es xs qs r.
Proof.
  revert xs; induction es as [|e es IH]; intros [|a xs] E; cbn in E; try discriminate.
  - exists [],0; constructor.
  - destruct (Split_total e a) as [q [r Hq]].
    destruct (IH xs) as [qs [s Hs]]; [lia|]. eauto using Scatter_cons.
Qed.

Lemma Scatter_functional es xs qs r : Scatter es xs qs r ->
  forall ps s, Scatter es xs ps s -> qs=ps /\ r=s.
Proof.
  intro H; induction H; intros ps t HT; inversion HT; subst.
  - auto.
  - match goal with H' : Split e a _ _ |- _ =>
      destruct (Split_functional H H'); subst end.
    match goal with H' : Scatter es xs _ _ |- _ =>
      destruct (IHScatter _ _ H'); subst end; auto.
Qed.

Lemma Scatter_mono es xs qs r : Scatter es xs qs r ->
  forall ys ps s, Scatter es ys ps s -> Forall2 le xs ys -> Forall2 le qs ps /\ r<=s.
Proof.
  intro H; induction H; intros ys ps t HT HL.
  - inversion HT; subst; split; constructor.
  - inversion HT as [|e' b p u es' ys' ps' v HB HS]; subst.
    inversion HL as [|a' b' xs' ys'' Hab Hxy]; subst.
    destruct (Split_mono H HB Hab) as [Hq Hr].
    destruct (IHScatter _ _ _ HS Hxy) as [Hqs Hs].
    split; [constructor; assumption|lia].
Qed.

(* The final parameter records the discarded first forward count. It is zero
   precisely on the ordinary (no-front-overflow) branch used by real columns. *)
Inductive Half (es:list bool) (inj:nat) : list nat -> nat -> list nat -> nat -> nat -> Prop :=
| Half_make xs u q qs r : Scatter es xs (q::qs) r ->
    Half es inj xs u (qs++[u]) (inj+r) q.

Lemma Half_length es inj xs u ys v leak : Half es inj xs u ys v leak ->
  length xs=length es /\ length ys=length xs.
Proof.
  intro H; destruct H; apply Scatter_length in H.
  rewrite length_app; cbn in *; lia.
Qed.

Lemma Half_nonempty es inj xs u ys v leak : Half es inj xs u ys v leak -> xs<>[].
Proof. intros H E; destruct H; subst xs; inversion H. Qed.

Lemma Half_mass es inj xs u ys v leak : Half es inj xs u ys v leak ->
  total xs+u+inj=total ys+v+leak.
Proof.
  intro H; destruct H; apply Scatter_mass in H.
  rewrite total_app; cbn in *; lia.
Qed.

Lemma Half_total es inj xs u : length es=length xs -> xs<>[] ->
  exists ys v leak, Half es inj xs u ys v leak.
Proof.
  intros E Hne. destruct (Scatter_total es xs E) as [qs [r H]].
  destruct qs; [apply Scatter_length in H; destruct xs; cbn in *; intuition congruence|].
  eauto using Half_make.
Qed.

Lemma Split_false_small a : a<=1 -> Split false a 0 a.
Proof. destruct a as [|[|a]]; intro H; [apply (Split_even false 0)|apply (Split_odd0 0)|lia]. Qed.

Lemma Half_front_total e es a xs u inj : length es=length xs -> Split e a 0 a ->
  exists ys v, Half (e::es) inj (a::xs) u ys v 0.
Proof.
  intros EL HA; destruct (Scatter_total es xs EL) as [qs [r HR]].
  exists (qs++[u]),(inj+(a+r)); apply Half_make; apply Scatter_cons; assumption.
Qed.

Lemma Half_functional es inj xs u ys v leak : Half es inj xs u ys v leak ->
  forall ys' v' leak', Half es inj xs u ys' v' leak' -> ys=ys' /\ v=v' /\ leak=leak'.
Proof.
  intro H; destruct H; intros ys' v' leak' H'; inversion H'; subst.
  match goal with H' : Scatter es xs _ _ |- _ =>
    destruct (Scatter_functional H H') as [E ->]; inversion E; subst end; auto.
Qed.

Lemma Half_mono es inj xs u ys v leak : Half es inj xs u ys v leak ->
  forall xs' u' ys' v' leak', Half es inj xs' u' ys' v' leak' ->
  Forall2 le xs xs' -> u<=u' -> Forall2 le ys ys' /\ v<=v' /\ leak<=leak'.
Proof.
  intro H; destruct H; intros xs' u' ys' v' leak' HT Hxs Hu.
  inversion HT; subst.
  match goal with H' : Scatter es xs' _ _ |- _ =>
    destruct (Scatter_mono H H' Hxs) as [Hqs Hr] end.
  inversion Hqs; subst; repeat split; try lia.
  apply Forall2_app; [assumption|constructor; [assumption|constructor]].
Qed.

Lemma Half_box_base e a : Split e a 0 a -> Half [e] 0 [a] a [a] a 0.
Proof. intro H; apply (Half_make 0 a (qs:=[]) (r:=a)); apply Scatter_single; assumption. Qed.

Lemma Half_box_extend es xs h e y r :
  Half es 0 xs h xs h 0 -> Split e y h r ->
  Half (es++[e]) 0 (xs++[y]) y (xs++[y]) y 0.
Proof.
  intros H HS. inversion H as [source root first qs h0 HC]; subst.
  pose proof (Split_mass HS) as E; subst y.
  apply (Half_make 0 (h0+r) (qs:=qs++[h0]) (r:=h0+r)).
  change (Scatter (es++[e]) ((qs++[h0])++[h0+r]) ((0::qs)++[h0]) (h0+r)).
  eapply Scatter_app; [eassumption|apply Scatter_single; exact HS].
Qed.

Lemma Half_box_injection es bounds h inj : Half es 0 bounds h bounds h 0 ->
  Half es inj bounds h bounds (inj+h) 0.
Proof. intro H; inversion H; subst; econstructor; eassumption. Qed.

Lemma Half_box_step es bounds h inj xs u ys v leak :
  Half es 0 bounds h bounds h 0 -> Half es inj xs u ys v leak ->
  Forall2 le xs bounds -> u<=h -> Forall2 le ys bounds /\ leak=0.
Proof.
  intros HB H HX HU. apply (Half_box_injection inj) in HB.
  destruct (Half_mono H HB HX HU) as [HY [_ HL]]; split; [assumption|lia].
Qed.

Inductive One : list nat -> list nat -> Prop :=
| One_here a xs : One (a::xs) (1+a::xs)
| One_later a xs ys : One xs ys -> One (a::xs) (a::ys).

Lemma le_refl_list xs : Forall2 le xs xs.
Proof. induction xs; constructor; auto. Qed.

Lemma zeros_le xs : Forall2 le (repeat 0 (length xs)) xs.
Proof. induction xs; cbn; constructor; auto; lia. Qed.

Lemma total_zeros n : total (repeat 0 n)=0.
Proof. induction n; cbn; assumption || reflexivity. Qed.

Lemma One_le xs ys : One xs ys -> Forall2 le xs ys.
Proof. intro H; induction H; constructor; auto using le_refl_list. Qed.

Lemma One_mass xs ys : One xs ys -> total ys=1+total xs.
Proof. intro H; induction H; cbn; lia. Qed.

Lemma total_le xs ys : Forall2 le xs ys -> total xs<=total ys.
Proof. intro H; induction H; cbn; lia. Qed.

Lemma total_eq xs ys : Forall2 le xs ys -> total xs=total ys -> xs=ys.
Proof.
  intro H; induction H; cbn; intros E; [reflexivity|].
  assert (total l<=total l') by (apply total_le; assumption).
  f_equal; [lia|apply IHForall2; lia].
Qed.

Lemma total_one xs ys : Forall2 le xs ys -> total ys=1+total xs -> One xs ys.
Proof.
  intro H; induction H; cbn; intros E; [lia|].
  assert (total l<=total l') by (apply total_le; assumption).
  destruct (Nat.eq_dec x y) as [->|Hne].
  - apply One_later, IHForall2; lia.
  - assert (l=l') by (apply total_eq; [assumption|lia]); subst l'.
    replace y with (1+x) by lia; constructor.
Qed.

Lemma Half_unit es inj xs u ys v xs' u' ys' v' :
  Half es inj xs u ys v 0 -> Half es inj xs' u' ys' v' 0 ->
  One (u::xs) (u'::xs') -> One (v::ys) (v'::ys').
Proof.
  intros H H' HU. pose proof (One_le HU) as HL.
  inversion HL as [|u1 u2 l l' Hu Hxs]; subst.
  destruct (Half_mono H H' Hxs Hu) as [Hy [Hv _]].
  apply total_one; [constructor; assumption|].
  apply Half_mass in H; apply Half_mass in H'; apply One_mass in HU; cbn in *; lia.
Qed.

Inductive Tick (es:list bool) (early:bool) : list nat -> nat -> list nat -> nat -> nat -> Prop :=
| Tick_make xs u middle root ys v a b :
    Half es (if early then 1 else 0) xs u middle root a ->
    Half es (if early then 0 else 1) middle root ys v b ->
    Tick es early xs u ys v (a+b).

Lemma Tick_mass es early xs u ys v leak : Tick es early xs u ys v leak ->
  total xs+u+1=total ys+v+leak.
Proof. intro H; destruct H; apply Half_mass in H, H0; destruct early; cbn in *; lia. Qed.

Lemma Tick_length es early xs u ys v leak : Tick es early xs u ys v leak ->
  length xs=length es /\ length ys=length xs.
Proof. intro H; destruct H; apply Half_length in H, H0; lia. Qed.

Lemma Tick_functional es early xs u ys v leak : Tick es early xs u ys v leak ->
  forall ys' v' leak', Tick es early xs u ys' v' leak' ->
    ys=ys' /\ v=v' /\ leak=leak'.
Proof.
  intro H; destruct H; intros ys' v' leak' HT.
  inversion HT as [xs0 u0 middle' root' ys0 v0 a' b' H1 H2]; subst.
  destruct (Half_functional H H1) as [-> [-> ->]].
  destruct (Half_functional H0 H2) as [-> [-> ->]]; auto.
Qed.

Lemma Tick_front_total es a b xs u : length es=length xs -> a<=1 -> b<=2 ->
  exists ys v, Tick (false::true::es) true (a::b::xs) u ys v 0.
Proof.
  intros EL HA HB; destruct (Split_total true b) as [q [r HQ]].
  assert (Hq : q<=1) by (inversion HQ; subst; lia).
  destruct (Scatter_total es xs EL) as [qs [s HS]].
  assert (H1 : Half (false::true::es) 1 (a::b::xs) u ((q::qs)++[u]) (1+(a+(r+s))) 0).
  { apply Half_make; apply Scatter_cons; [apply Split_false_small; assumption|].
    apply Scatter_cons; assumption. }
  destruct (@Half_front_total false (true::es) q (qs++[u]) (1+(a+(r+s))) 0)
    as [ys [v H2]]; [pose proof (Scatter_length HS); rewrite length_app; cbn; lia|apply Split_false_small; assumption|].
  exists ys,v; exact (Tick_make true H1 H2).
Qed.

Lemma zeros_snoc n : repeat 0 n++[0]=repeat 0 (1+n).
Proof.
  change (repeat 0 n++repeat 0 1=repeat 0 (1+n)).
  rewrite <- repeat_app; f_equal; lia.
Qed.

Lemma Tick_zeros e es : Tick (e::es) true (repeat 0 (1+length es)) 0
  (repeat 0 (length es)++[1]) 0 0.
Proof.
  assert (H : Half (e::es) 1 (repeat 0 (1+length es)) 0
    (repeat 0 (1+length es)) 1 0).
  { rewrite <- (zeros_snoc (length es)) at 2.
    apply (Half_make 1 0 (qs:=repeat 0 (length es)) (r:=0)); apply Scatter_zeros. }
  assert (H' : Half (e::es) 0 (repeat 0 (1+length es)) 1
    (repeat 0 (length es)++[1]) 0 0).
  { apply (Half_make 0 1 (qs:=repeat 0 (length es)) (r:=0)); apply Scatter_zeros. }
  exact (Tick_make true H H').
Qed.

Lemma Tick_late_zeros e es : Tick (e::es) false (repeat 0 (1+length es)) 0
  (repeat 0 (1+length es)) 1 0.
Proof.
  assert (H : forall inj, Half (e::es) inj (repeat 0 (1+length es)) 0
    (repeat 0 (1+length es)) inj 0).
  { intro inj; rewrite <- (zeros_snoc (length es)) at 2.
    replace inj with (inj+0) at 2 by lia.
    apply (Half_make inj 0 (qs:=repeat 0 (length es)) (r:=0)); apply Scatter_zeros. }
  exact (Tick_make false (H 0) (H 1)).
Qed.

Lemma Tick_mono es early xs u ys v leak : Tick es early xs u ys v leak ->
  forall xs' u' ys' v' leak', Tick es early xs' u' ys' v' leak' ->
  Forall2 le xs xs' -> u<=u' -> Forall2 le ys ys' /\ v<=v' /\ leak<=leak'.
Proof.
  intro H; destruct H; intros xs' u' ys' v' leak' HT Hxs Hu.
  inversion HT as [xs0 u0 middle' root' ys0 v0 a' b' H1 H2]; subst.
  destruct (Half_mono H H1 Hxs Hu) as [Hm [Hr Ha]].
  destruct (Half_mono H0 H2 Hm Hr) as [Hy [Hv Hb]]; repeat split; auto; lia.
Qed.

Lemma Tick_unit es early xs u ys v xs' u' ys' v' :
  Tick es early xs u ys v 0 -> Tick es early xs' u' ys' v' 0 ->
  One (u::xs) (u'::xs') -> One (v::ys) (v'::ys').
Proof.
  intros H H' HU. pose proof (One_le HU) as HL.
  inversion HL as [|u1 u2 l l' Hu Hxs]; subst.
  destruct (Tick_mono H H' Hxs Hu) as [Hy [Hv _]].
  apply total_one; [constructor; assumption|].
  apply Tick_mass in H; apply Tick_mass in H'; apply One_mass in HU; cbn in *; lia.
Qed.

Lemma Half_box_total es bounds h inj xs u :
  Half es 0 bounds h bounds h 0 -> Forall2 le xs bounds -> u<=h ->
  exists ys v, Half es inj xs u ys v 0 /\ Forall2 le ys bounds.
Proof.
  intros HB HX HU.
  destruct (Half_length HB) as [EL _].
  assert (EN : xs<>[]).
  { intro E; subst xs; inversion HX; subst bounds; exact (Half_nonempty HB eq_refl). }
  destruct (Half_total es inj (xs:=xs) u) as [ys [v [leak H]]];
    [apply Forall2_length in HX; lia|exact EN|].
  destruct (Half_box_step HB H HX HU) as [HY ->]; eauto.
Qed.

Lemma Tick_box_total es bounds h early xs u :
  Half es 0 bounds h bounds h 0 -> Forall2 le xs bounds -> total xs+u+1<=h ->
  exists ys v, Tick es early xs u ys v 0 /\ Forall2 le ys bounds.
Proof.
  intros HB HX Hmass.
  destruct (Half_box_total (u:=u) (if early then 1 else 0) HB HX ltac:(lia))
    as [middle [root [H1 HM]]].
  pose proof (Half_mass H1) as E.
  assert (HR : root<=h) by (destruct early; cbn in E; lia).
  destruct (Half_box_total (if early then 0 else 1) HB HM HR) as [ys [v [H2 HY]]].
  exists ys,v; split; [exact (Tick_make early H1 H2)|exact HY].
Qed.

Inductive Ticks (es:list bool) (early:bool) : nat -> list nat -> nat -> list nat -> nat -> Prop :=
| Ticks_nil xs u : Ticks es early 0 xs u xs u
| Ticks_cons n xs u ys v zs w : Tick es early xs u ys v 0 ->
    Ticks es early n ys v zs w -> Ticks es early (1+n) xs u zs w.

Lemma Ticks_mass es early n xs u ys v : Ticks es early n xs u ys v ->
  total ys+v=total xs+u+n.
Proof. intro H; induction H; [lia|apply Tick_mass in H; lia]. Qed.

Lemma Ticks_app es early n xs u ys v : Ticks es early n xs u ys v ->
  forall m zs w, Ticks es early m ys v zs w -> Ticks es early (n+m) xs u zs w.
Proof. intro H; induction H; intros; cbn; eauto using Ticks_nil, Ticks_cons. Qed.

Lemma Ticks_snoc es early n xs u ys v zs w :
  Ticks es early n xs u ys v -> Tick es early ys v zs w 0 ->
  Ticks es early (1+n) xs u zs w.
Proof.
  intros H HT; replace (1+n) with (n+1) by lia.
  eapply Ticks_app; [exact H|eapply Ticks_cons; [exact HT|constructor]].
Qed.

Lemma Ticks_unsnoc es early n : forall xs u ys v, Ticks es early (1+n) xs u ys v ->
  exists zs w, Ticks es early n xs u zs w /\ Tick es early zs w ys v 0.
Proof.
  induction n; intros xs u ys v H; inversion H as [|n0 xs0 u0 mid root ys0 v0 HT HR]; subst.
  - inversion HR; subst; eauto using Ticks_nil.
  - destruct (IHn _ _ _ _ HR) as [zs [w [HC HD]]]; eauto using Ticks_cons.
Qed.

Lemma Ticks_functional es early n xs u ys v : Ticks es early n xs u ys v ->
  forall ys' v', Ticks es early n xs u ys' v' -> ys=ys' /\ v=v'.
Proof.
  intro H; induction H; intros ys' v' HT;
    inversion HT as [|n0 xs0 u0 middle root ys0 v0 H1 H2]; subst; [auto|].
  destruct (Tick_functional H H1) as [-> [-> _]]; eapply IHTicks; exact H2.
Qed.

Lemma Ticks_suffix es early n xs u ys v : Ticks es early n xs u ys v ->
  forall k zs w, k<=n -> Ticks es early k xs u zs w -> Ticks es early (n-k) zs w ys v.
Proof.
  intro H; induction H; intros [|k] ps r HK HP.
  - inversion HP; subst; constructor.
  - lia.
  - rewrite Nat.sub_0_r; inversion HP; subst; eapply Ticks_cons; eassumption.
  - inversion HP as [|k0 xs0 u0 mid root zs0 w0 H1 H2]; subst.
    destruct (Tick_functional H H1) as [-> [-> _]].
    cbn[Nat.sub]; eapply IHTicks; [lia|exact H2].
Qed.

Lemma Ticks_unit es early n xs u ys v : Ticks es early n xs u ys v ->
  forall xs' u' ys' v', Ticks es early n xs' u' ys' v' ->
  One (u::xs) (u'::xs') -> One (v::ys) (v'::ys').
Proof.
  intro H; induction H; intros xs' u' ys' v' HT HU; inversion HT; subst; [assumption|].
  eapply IHTicks; [eassumption|eapply Tick_unit; eauto].
Qed.

Lemma Tick_zeros_unit es early xs u : Tick es early (repeat 0 (length es)) 0 xs u 0 ->
  One (0::repeat 0 (length es)) (u::xs).
Proof.
  intro H. destruct (Tick_length H) as [_ EL]. rewrite repeat_length in EL.
  apply total_one.
  - constructor; [lia|rewrite <- EL; apply zeros_le].
  - apply Tick_mass in H; rewrite total_zeros in H.
    cbn[total]; rewrite total_zeros; lia.
Qed.

Lemma Ticks_zero_unit es early n xs u ys v :
  Ticks es early n (repeat 0 (length es)) 0 xs u ->
  Ticks es early (1+n) (repeat 0 (length es)) 0 ys v -> One (u::xs) (v::ys).
Proof.
  intros H HT; inversion HT; subst.
  eapply Ticks_unit; [exact H|eassumption|eapply Tick_zeros_unit; eassumption].
Qed.

Lemma Ticks_box_total es bounds h early n : Half es 0 bounds h bounds h 0 ->
  forall xs u, Forall2 le xs bounds -> total xs+u+n<=h ->
  exists ys v, Ticks es early n xs u ys v /\ Forall2 le ys bounds.
Proof.
  intro HB; induction n; intros xs u HX Hmass.
  - exists xs,u; auto using Ticks_nil.
  - destruct (Tick_box_total early u HB HX ltac:(lia)) as [middle [root [HT HM]]].
    pose proof (Tick_mass HT) as E.
    destruct (IHn middle root HM ltac:(lia)) as [ys [v [HR HY]]].
    exists ys,v; eauto using Ticks_cons.
Qed.

Lemma Ticks_box_preserves es bounds h early n xs u ys v :
  Half es 0 bounds h bounds h 0 -> Ticks es early n xs u ys v ->
  Forall2 le xs bounds -> total xs+u+n<=h -> Forall2 le ys bounds.
Proof.
  intros HB HR HX HM.
  destruct (@Ticks_box_total es bounds h early n HB xs u HX HM) as [zs [w [HT HL]]].
  destruct (Ticks_functional HR HT) as [-> ->]; exact HL.
Qed.

(* Absorb a finite root seed one unit at a time.  The coupling hypothesis
   compares real, already available futures; the box supplies both of them. *)
Lemma Ticks_seed_absorbs es early bounds h C : Half es 0 bounds h bounds h 0 ->
  (forall j xs u noise z endc w endn q,
    Ticks es early j (repeat 0 (length es)) 0 xs u ->
    Ticks es early (1+C) xs u endc w -> Ticks es early C noise z endn q ->
    One (u::xs) (z::noise) -> exists s ys root,
    s<=C /\ Ticks es early s noise z ys root /\ Ticks es early (1+s) xs u ys root) ->
  forall k, k*(C+1)+1<=h -> exists t xs u, t<=k*C /\
    Ticks es early t (repeat 0 (length es)) k xs u /\
    Ticks es early (t+k) (repeat 0 (length es)) 0 xs u /\ Forall2 le xs bounds.
Proof.
  intros HB Couple; destruct (Half_length HB) as [EL _].
  pose proof (zeros_le bounds) as HZ; rewrite EL in HZ.
  induction k; intro HK.
  - exists 0,(repeat 0 (length es)),0; split; [lia|split; [constructor|split; [constructor|exact HZ]]].
  - destruct (IHk ltac:(nia)) as [t [xs [u [Ht [HR [HP HX]]]]]].
    destruct (@Ticks_box_total es bounds h early t HB (repeat 0 (length es)) (1+k) HZ)
      as [noise [z [HN HNX]]]; [rewrite total_zeros; nia|].
    pose proof (Ticks_unit HR HN (One_here k (repeat 0 (length es)))) as HU.
    pose proof (Ticks_mass HP) as EP; pose proof (Ticks_mass HN) as EN.
    rewrite total_zeros in EP, EN.
    destruct (@Ticks_box_total es bounds h early (1+C) HB xs u HX)
      as [endc [w [HC _]]]; [nia|].
    destruct (@Ticks_box_total es bounds h early C HB noise z HNX)
      as [endn [q [HF _]]]; [nia|].
    destruct (Couple _ _ _ _ _ _ _ _ _ HP HC HF HU) as [s [ys [v [HS [HD HE]]]]].
    assert (HA : Ticks es early (t+s) (repeat 0 (length es)) (1+k) ys v)
      by (eapply Ticks_app; eassumption).
    exists (t+s),ys,v; split; [nia|split; [exact HA|split]].
    + replace (t+s+S k) with ((t+k)+(1+s)) by lia; eapply Ticks_app; eassumption.
    + eapply Ticks_box_preserves; [exact HB|exact HA|exact HZ|rewrite total_zeros; nia].
Qed.

Lemma Split_even_eq e n q r : n=q+r -> q=r -> Split e n q r.
Proof. intros -> ->; replace (r+r) with (r*2) by lia; constructor. Qed.
Lemma Split_odd0_eq n q r : n=q+r -> r=1+q -> Split false n q r.
Proof. intros -> ->; replace (q+(1+q)) with (1+q*2) by lia; constructor. Qed.
Lemma Split_odd1_eq n q r : n=q+r -> q=1+r -> Split true n q r.
Proof. intros -> ->; replace (1+r+r) with (1+r*2) by lia; constructor. Qed.

Lemma Pass_alt_split p n q r a : Split p n q r -> a<>0 \/ p=true ->
  Pass (Alt p n) a (a+q) (Alt (xorb (Nat.odd a) p) r).
Proof.
  intros H Ha; destruct H.
  - apply Pass_alt_even; assumption.
  - rewrite xorb_false_r. apply Pass_alt_odd_I; destruct Ha; congruence.
  - rewrite xorb_true_r. replace (a+(1+a0)) with (1+a+a0) by lia.
    apply Pass_alt_odd_P.
Qed.

Lemma Split_adjacent e x q r y q' r' b : Split e x q r -> Split (negb e) y q' r' ->
  Split (xorb e (Nat.odd x)) (b*2+x+y) (b+r+r') (b+q+q').
Proof.
  destruct e; intros H H'; inversion H; subst; inversion H'; subst;
    rewrite ?odd_0, ?odd_1; cbn[xorb];
    first [apply Split_even_eq; lia | apply Split_odd0_eq; lia | apply Split_odd1_eq; lia].
Qed.

Lemma odd_shift a r b s : a+1=b*2+r+s*2 -> Nat.odd a=negb (Nat.odd r).
Proof.
  intro H; apply (f_equal Nat.odd) in H.
  rewrite !Nat.odd_add, !odd_0 in H.
  change (xorb (Nat.odd a) true=xorb (xorb false (Nat.odd r)) false) in H.
  rewrite xorb_true_r, xorb_false_l, xorb_false_r in H.
  rewrite <- H, negb_involutive; reflexivity.
Qed.
Arguments odd_shift {a r b s} _.

Lemma Pass_counter_block e x q r y q' r' b s a :
  Split e x q r -> Split (negb e) y q' r' -> a<>0 -> a+1=b*2+r+s*2 ->
  Pass (Alt (xorb e (Nat.odd x)) (b*4+x+y)) a (a+(b*2+r+r'))
    (Alt (xorb (negb e) (Nat.odd q)) (b*2+q+q')).
Proof.
  intros H H' Ha HE.
  assert (E : xorb (Nat.odd a) (xorb e (Nat.odd x)) =
              xorb (negb e) (Nat.odd q)).
  { rewrite (odd_shift HE), (Split_mass H), Nat.odd_add.
    destruct e, (Nat.odd r), (Nat.odd q); reflexivity. }
  rewrite <- E. replace (b*4+x+y) with ((b*2)*2+x+y) by lia.
  apply Pass_alt_split; [eapply Split_adjacent; eauto|auto].
Qed.
Arguments Pass_counter_block {e x q r y q' r'} b s a _ _ _ _.

(* Alternating masks whose next, unused mask is false. No separate length or
   parity field is needed: the constructors carry that information. *)
Inductive TailSplit : bool -> list nat -> list nat -> nat -> Prop :=
| TailSplit_nil : TailSplit false [] [] 0
| TailSplit_cons e x q r xs qs s : Split e x q r -> TailSplit (negb e) xs qs s ->
    TailSplit e (x::xs) (q::qs) (r+s).

Lemma TailSplit_complete xs : forall e qs r,
  Scatter (Alt e (length xs)) xs qs r -> xorb e (Nat.odd (length xs))=false ->
  TailSplit e xs qs r.
Proof.
  induction xs as [|x xs IH]; intros e qs r H E; cbn[Alt length] in H, E.
  - inversion H; subst. destruct e; [discriminate|constructor].
  - inversion H; subst. econstructor; [eassumption|].
    eapply IH; [eassumption|]. rewrite odd_S in E.
    destruct e, (Nat.odd (length xs)); cbn in *; congruence.
Qed.

Lemma Half_tail n inj xs u ys v : Half (Alt false (n*2)) inj xs u ys v 0 ->
  exists qs r, TailSplit false xs (0::qs) r /\ ys=qs++[u] /\ v=inj+r.
Proof.
  intro H. destruct (Half_length H) as [EL _].
  rewrite Alt_length in EL.
  inversion H; subst. eexists; eexists; repeat split.
  eapply TailSplit_complete; [rewrite EL; eassumption|rewrite EL, odd_0; reflexivity].
Qed.

Fixpoint CWord (e:bool) (base x:nat) (xs:list nat) (u:nat) : list bool :=
  match xs with
  | [] => Alt (xorb e (Nat.odd x)) (base+x+u*2)
  | y::ys => Alt (xorb e (Nat.odd x)) (base+x+y) ++ CWord (negb e) (base*2) y ys u
  end.

Lemma CWord_pass e xs qs R : TailSplit e xs qs R -> forall b x q r s u a,
  b<>0 -> Split (negb e) x q r -> a+1=b*2+r+s*2 -> exists A o,
    Pass (CWord (negb e) (b*4) x xs u) a A o /\
    o++Alt (Nat.odd A) (1+A) = CWord e (b*2) q (qs++[u]) (s+r+R).
Proof.
  intro H; induction H; intros b x0 q0 r0 k u a Hb HX Ha.
  - exists (a+(b*2+r0+u)), (Alt (Nat.odd q0) (b*2+q0+u)); split.
    + cbn[CWord]. change (Nat.odd q0) with (xorb false (Nat.odd q0)).
      apply (Pass_counter_block b k a HX (Split_even false u)); lia.
    + cbn[CWord List.app]. f_equal.
      f_equal; [|lia]. change (Nat.odd (a+(b*2+r0+u))=negb (Nat.odd u)).
      apply (odd_shift (b:=b*2) (s:=k+r0)); lia.
  - assert (HX' : Split (negb (negb e)) x q r) by (rewrite negb_involutive; assumption).
    destruct (IHTailSplit (b*2) x q r (k+r0) u (a+(b*2+r0+r))) as [A [o [HP EO]]];
      [lia|exact HX'|lia|].
    exists A, (Alt (xorb e (Nat.odd q0)) (b*2+q0+q)++o); split.
    + cbn[CWord]. rewrite negb_involutive.
      assert (Ha' : a<>0) by lia.
      pose proof (Pass_counter_block b k a HX HX' Ha' Ha) as HB.
      rewrite negb_involutive in HB, HP.
      replace (b*2*4) with (b*4*2) in HP by lia.
      eapply Pass_cat; eauto.
    + rewrite <- app_assoc, EO. cbn[CWord List.app]. f_equal.
      f_equal; lia.
Qed.
Arguments CWord_pass {e xs qs R} _ b {x q r} s u a _ _ _.

(* Finite initialization checker. Both half-steps reject nonzero discarded
   counts; it computes only the counter vector, never a long signal word. *)
Module CounterEval.

Definition split_c (e:bool) n := let q:=Nat.div2 n in
  if Nat.odd n then if e then (1+q,q) else (q,1+q) else (q,q).

Lemma split_c_spec e n : Split e n (fst (split_c e n)) (snd (split_c e n)).
Proof.
  destruct (Split_total e n) as [q [r H]]; destruct H; unfold split_c.
  - rewrite odd_0; replace (a*2) with (2*a) by lia.
    rewrite Nat.div2_double, Nat.mul_comm; constructor.
  - rewrite odd_1; replace (1+a*2) with (S (2*a)) by lia.
    rewrite Nat.div2_succ_double, Nat.mul_comm; constructor.
  - rewrite odd_1; replace (1+a*2) with (S (2*a)) by lia.
    rewrite Nat.div2_succ_double, Nat.mul_comm; constructor.
Qed.

Fixpoint scatter_c es xs : option (list nat*nat) := match es,xs with
  | [],[] => Some ([],0)
  | e::es,x::xs => let '(q,r):=split_c e x in
      match scatter_c es xs with Some (qs,s) => Some (q::qs,r+s) | None => None end
  | _,_ => None end.

Lemma scatter_c_spec es : forall xs qs r, scatter_c es xs=Some (qs,r) -> Scatter es xs qs r.
Proof.
  induction es as [|e es IH]; intros [|x xs] qs r H; cbn[scatter_c] in H; try discriminate.
  - inversion H; constructor.
  - pose proof (split_c_spec e x) as HS.
    destruct (split_c e x) as [q s]; cbn in HS.
    destruct (scatter_c es xs) as [[ps t]|] eqn:HT; [|discriminate].
    inversion H; subst; econstructor; [exact HS|eapply IH; exact HT].
Qed.

Definition half_c es inj (c:list nat*nat) := let '(xs,u):=c in
  match scatter_c es xs with
  | Some (0::qs,r) => Some (qs++[u],inj+r) | _ => None end.

Lemma half_c_spec es inj xs u ys v : half_c es inj (xs,u)=Some (ys,v) ->
  Half es inj xs u ys v 0.
Proof.
  unfold half_c; destruct (scatter_c es xs) as [[[|[|q] qs] r]|] eqn:H; try discriminate.
  intro E; inversion E; subst; constructor; eapply scatter_c_spec; exact H.
Qed.
Arguments half_c_spec {es inj xs u ys v} _.

Definition tick_c es (early:bool) c := match half_c es (if early then 1 else 0) c with
  | Some d => half_c es (if early then 0 else 1) d | None => None end.

Lemma tick_c_spec es early xs u ys v : tick_c es early (xs,u)=Some (ys,v) ->
  Tick es early xs u ys v 0.
Proof.
  unfold tick_c; destruct (half_c es (if early then 1 else 0) (xs,u)) as [[zs w]|] eqn:H;
    [|discriminate].
  intro E; exact (Tick_make early (half_c_spec H) (half_c_spec E)).
Qed.

Fixpoint ticks_c es early n c := match n with
  | 0 => Some c
  | S n => match tick_c es early c with Some d => ticks_c es early n d | None => None end end.

Lemma ticks_c_spec es early n : forall xs u ys v, ticks_c es early n (xs,u)=Some (ys,v) ->
  Ticks es early n xs u ys v.
Proof.
  induction n; intros xs u ys v H; cbn[ticks_c] in H.
  - inversion H; constructor.
  - destruct (tick_c es early (xs,u)) as [[zs w]|] eqn:HT; [|discriminate].
    econstructor; [eapply tick_c_spec; exact HT|eapply IHn; exact H].
Qed.

Fixpoint counts_eqb (xs ys:list nat) := match xs,ys with
  | [],[] => true
  | x::xs,y::ys => if Nat.eqb x y then counts_eqb xs ys else false
  | _,_ => false end.

Lemma counts_eqb_spec xs : forall ys, counts_eqb xs ys=true -> xs=ys.
Proof.
  induction xs; intros [|y ys] H; cbn[counts_eqb] in H; try discriminate; [reflexivity|].
  destruct (Nat.eqb a y) eqn:E; [apply Nat.eqb_eq in E; subst|discriminate].
  f_equal; apply IHxs; exact H.
Qed.

Definition check es early n xs u ys v := match ticks_c es early n (xs,u) with
  | Some (zs,w) => if Nat.eqb w v then counts_eqb zs ys else false | None => false end.

Theorem check_spec es early n xs u ys v : check es early n xs u ys v=true ->
  Ticks es early n xs u ys v.
Proof.
  unfold check; destruct (ticks_c es early n (xs,u)) as [[zs w]|] eqn:H; [|discriminate].
  destruct (Nat.eqb w v) eqn:E; [apply Nat.eqb_eq in E; subst|discriminate].
  intro HE; apply counts_eqb_spec in HE; subst; eapply ticks_c_spec; exact H.
Qed.

End CounterEval.

(* Constant-base words used by the single-column binary counter. *)
Fixpoint FlatWord (x:nat) (xs:list nat) (u:nat) : list bool := match xs with
  | [] => Alt (Nat.odd x) (2+x+u*2)
  | y::ys => Alt (Nat.odd x) (1+x+y) ++ FlatWord y ys u end.

Lemma Split_flat_adjacent x q r y q' r' : Split false x q r -> Split false y q' r' ->
  Split (Nat.odd x) (1+x+y) (r+r') (1+q+q').
Proof.
  intros H H'; inversion H; subst; inversion H'; subst; rewrite ?odd_0, ?odd_1;
    first [apply Split_even_eq; lia | apply Split_odd0_eq; lia | apply Split_odd1_eq; lia].
Qed.

Lemma Pass_flat_block x q r y q' r' s a : Split false x q r -> Split false y q' r' ->
  a<>0 -> a=r+s*2 ->
  Pass (Alt (Nat.odd x) (1+x+y)) a (a+(r+r')) (Alt (Nat.odd q) (1+q+q')).
Proof.
  intros HX HY Ha HE.
  assert (E : xorb (Nat.odd a) (Nat.odd x)=Nat.odd q).
  { rewrite HE, (Split_mass HX), !Nat.odd_add, odd_0, xorb_false_r.
    destruct (Nat.odd q), (Nat.odd r); reflexivity. }
  rewrite <- E; apply Pass_alt_split; [eapply Split_flat_adjacent; eassumption|auto].
Qed.

Lemma FlatWord_pass xs : forall qs R, Scatter (repeat false (length xs)) xs qs R ->
  forall x q r s u a, Split false x q r -> a<>0 -> a=r+s*2 -> exists A o,
    Pass (FlatWord x xs u) a A o /\
    o++Alt (negb (Nat.odd A)) (1+A)=FlatWord q (qs++[u]) (s+r+R).
Proof.
  induction xs as [|y xs IH]; intros qs R HS x q r s u a HX Ha HE.
  - inversion HS; subst qs R.
    exists (a+(r+(1+u))), (Alt (Nat.odd q) (1+q+u)); split.
    + cbn[FlatWord]; replace (2+x+u*2) with (1+x+(1+u*2)) by lia.
      eapply Pass_flat_block; [exact HX|exact (Split_odd0 u)|exact Ha|exact HE].
    + assert (E : negb (Nat.odd (a+(r+(1+u))))=Nat.odd u).
      { replace (a+(r+(1+u))) with (1+(s+r)*2+u) by lia.
        rewrite Nat.odd_add, odd_1; destruct (Nat.odd u); reflexivity. }
      cbn[FlatWord app]; rewrite E; f_equal; f_equal; lia.
  - cbn[length repeat] in HS.
    inversion HS as [|e y0 q0 r0 es tail out R0 HY HT]; subst e y0 es tail qs R.
    destruct (IH _ _ HT y q0 r0 (s+r) u (a+(r+r0)) HY ltac:(lia) ltac:(lia))
      as [A [o [HP HO]]].
    exists A,(Alt (Nat.odd q) (1+q+q0)++o); split.
    + cbn[FlatWord]; eapply Pass_cat; [eapply Pass_flat_block; eassumption|exact HP].
    + rewrite <- app_assoc, HO; cbn[FlatWord app]; f_equal; f_equal; lia.
Qed.

Lemma FlatWord_I xs u : exists w, FlatWord 0 xs u=false::w.
Proof. destruct xs; cbn[FlatWord Nat.add Alt app]; eauto. Qed.

(* Fixed capacities 1,3,7,... for the all-false zero-injection half-step. *)
Inductive FlatBox : nat -> list nat -> nat -> Prop :=
| FlatBox_base : FlatBox 1 [1] 1
| FlatBox_next N xs h : FlatBox N xs h -> FlatBox (1+N) (xs++[1+h*2]) (1+h*2).

Lemma FlatBox_spec N xs h : FlatBox N xs h ->
  length xs=N /\ Half (repeat false N) 0 xs h xs h 0 /\ h+1=2^N.
Proof.
  intro H; induction H as [|N xs h H [EL [HB EH]]].
  - split; [reflexivity|split; [apply Half_box_base, (Split_odd0 0)|reflexivity]].
  - split; [rewrite length_app; cbn; lia|split].
    + replace (repeat false (1+N)) with (repeat false N++[false])
        by (pose proof (repeat_app false N 1) as E; replace (N+1) with (1+N) in E by lia;
            cbn[repeat Nat.add] in E |- *; congruence).
      eapply Half_box_extend; [exact HB|constructor].
    + change (1+h*2+1=2*2^N); rewrite <- EH; lia.
Qed.

Lemma FlatBox_mass N xs h : FlatBox N xs h -> total xs+N=h*2.
Proof. intro H; induction H; [reflexivity|rewrite total_app; cbn; lia]. Qed.

Lemma Half_fixed_scatter es xs h : Half es 0 xs h xs h 0 ->
  exists qs, xs=qs++[h] /\ Scatter es xs (0::qs) h.
Proof. intro H; inversion H; subst; eauto. Qed.

Fixpoint Raise b xs := match xs with
  | [] => [] | x::xs => (b+x)::Raise (b*2) xs end.

Lemma Raise_app xs : forall b ys,
  Raise b (xs++ys)=Raise b xs++Raise (b*2^length xs) ys.
Proof.
  induction xs; intros b ys; cbn[Raise app length Nat.pow].
  - rewrite Nat.mul_1_r; reflexivity.
  - rewrite IHxs, Nat.mul_assoc; reflexivity.
Qed.

Lemma Split_raise e x q r b : Split e x q r ->
  Split e (b*2+x) (b+q) (b+r).
Proof.
  intro H; destruct H;
    first [apply Split_even_eq; lia | apply Split_odd0_eq; lia | apply Split_odd1_eq; lia].
Qed.

Lemma Scatter_raise xs : forall qs r b,
  Scatter (repeat false (length xs)) xs qs r ->
  Scatter (repeat false (length xs)) (Raise (b*2) xs) (Raise b qs)
    (r+b*(2^length xs-1)).
Proof.
  induction xs; intros qs r b H; inversion H; subst; cbn[Raise length repeat Nat.pow].
  - rewrite !Nat.mul_0_r; constructor.
  - pose proof (Nat.pow_nonzero 2 (length xs) ltac:(lia)).
    replace (r0+s+b*(2*2^length xs-1)) with
      ((b+r0)+(s+b*2*(2^length xs-1))) by nia.
    constructor; [apply Split_raise; assumption|apply IHxs; assumption].
Qed.

Lemma Half_raise N xs u ys v : Half (repeat false N) 1 xs u ys v 0 ->
  Half (repeat false N) 2 (Raise 2 xs) (u+2^N) (Raise 2 ys) (v+2^N) 1.
Proof.
  intro H; inversion H as [body root q qs r HS]; subst.
  destruct (Scatter_length HS) as [EL EQ]; rewrite repeat_length in EL, EQ.
  pose proof (@Scatter_raise xs (0::qs) r 1 ltac:(rewrite EL; exact HS)) as HR.
  rewrite EL in HR; cbn[Raise] in HR; rewrite !Nat.mul_1_l in HR.
  rewrite Raise_app; cbn[Raise length] in *.
  assert (EP : 2*2^length qs=2^N) by (rewrite <- EQ; reflexivity).
  rewrite EP; replace (2^N+u) with (u+2^N) by lia.
  replace (1+r+2^N) with (2+(r+(2^N-1))) by
    (pose proof (Nat.pow_nonzero 2 N ltac:(lia)); lia).
  constructor; exact HR.
Qed.

Arguments Half_raise {N xs u ys v} _.

(* General end phase: the terminal return head is determined by the unused
   mask, not fixed to the false-mask convention of TailSplit. *)
Lemma CWord_pass_mask xs : forall e qs R,
  Scatter (Alt e (length xs)) xs qs R -> forall b x q r s u a,
  b<>0 -> Split (negb e) x q r -> a+1=b*2+r+s*2 -> exists A o,
    Pass (CWord (negb e) (b*4) x xs u) a A o /\
    o++Alt (xorb (xorb e (Nat.odd (length xs))) (Nat.odd A)) (1+A)=
      CWord e (b*2) q (qs++[u]) (s+r+R).
Proof.
  induction xs; intros e qs R H b x q r s u a0 Hb HX Ha;
    cbn[length Alt] in H; inversion H as [|e0 y qy ry es0 tail out rest HS HT]; subst.
  - exists (a0+(b*2+r+u)), (Alt (xorb e (Nat.odd q)) (b*2+q+u)); split.
    + assert (HS : Split (negb (negb e)) (u*2) u u)
        by (rewrite negb_involutive; constructor).
      pose proof (Pass_counter_block b s a0 HX HS ltac:(lia) Ha) as HP.
      rewrite negb_involutive in HP; exact HP.
    + cbn[CWord app length]; rewrite xorb_false_r.
      assert (EO : Nat.odd (a0+(b*2+r+u))=negb (Nat.odd u)).
      { apply (odd_shift (b:=b*2) (s:=s+r)); lia. }
      rewrite EO; f_equal.
      f_equal; [destruct e, (Nat.odd u); reflexivity|lia].
  - assert (HX' : Split (negb (negb e)) a qy ry) by (rewrite negb_involutive; assumption).
    destruct (IHxs (negb e) out rest HT (b*2) a qy ry (s+r) u (a0+(b*2+r+ry)))
      as [A [o [HP EO]]]; [lia|exact HX'|lia|].
    exists A,(Alt (xorb e (Nat.odd q)) (b*2+q+qy)++o); split.
    + cbn[CWord]; rewrite negb_involutive.
      pose proof (Pass_counter_block b s a0 HX HX' ltac:(lia) Ha) as HB.
      rewrite negb_involutive in HB, HP.
      replace (b*2*4) with (b*4*2) in HP by lia; eapply Pass_cat; eassumption.
    + cbn[length]; rewrite odd_S.
      replace (xorb e (negb (Nat.odd (length xs)))) with
        (xorb (negb e) (Nat.odd (length xs))) by (destruct e, (Nat.odd (length xs)); reflexivity).
      rewrite <- app_assoc, EO; cbn[CWord app]; f_equal; f_equal; lia.
Qed.

(* Unit-increment routing, safe windows and seed absorption. *)

(* A single increment, with its position and original counter value retained. *)
Inductive Bump : nat -> nat -> list nat -> list nat -> Prop :=
| Bump_here a xs : Bump 0 a (a::xs) (1+a::xs)
| Bump_later i a b xs ys : Bump i a xs ys -> Bump (1+i) a (b::xs) (b::ys).

Lemma Bump_one i a xs ys : Bump i a xs ys -> One xs ys.
Proof. intro H; induction H; constructor; assumption. Qed.

Lemma One_bump xs ys : One xs ys -> exists i a, Bump i a xs ys.
Proof. intro H; induction H; [eauto using Bump_here|destruct IHOne as [i [a' HI]]; eauto using Bump_later]. Qed.

Lemma Bump_length i a xs ys : Bump i a xs ys -> length xs=length ys /\ i<length xs.
Proof. intro H; induction H; cbn; lia. Qed.

Lemma Bump_nth i a xs ys : Bump i a xs ys -> nth i xs 0=a /\ nth i ys 0=1+a.
Proof. intro H; induction H; cbn; auto. Qed.

Lemma Bump_other i a xs ys : Bump i a xs ys -> forall j, j<>i -> nth j ys 0=nth j xs 0.
Proof.
  intro H; induction H; intros [|j] Hne; cbn; try reflexivity; try congruence.
  apply IHBump; lia.
Qed.

Lemma Bump_odd p i a xs ys : Bump i a xs ys ->
  Nat.odd (nth p ys 0)=
    (if i =? p then negb (Nat.odd (nth p xs 0)) else Nat.odd (nth p xs 0)).
Proof.
  intro H; destruct (i =? p) eqn:E.
  - apply Nat.eqb_eq in E; subst p.
    destruct (Bump_nth H) as [-> ->]; apply odd_S.
  - apply Nat.eqb_neq in E; rewrite (Bump_other (j:=p) H ltac:(lia)); reflexivity.
Qed.
Arguments Bump_odd p {i a xs ys} _.

Lemma Bump_functional i a xs ys : Bump i a xs ys -> forall b zs,
  Bump i b xs zs -> ys=zs.
Proof.
  intro H; induction H; intros b' zs H'; inversion H'; subst; [reflexivity|].
  f_equal; eapply IHBump; eassumption.
Qed.

Lemma Bump_position i a xs ys : Bump i a xs ys -> forall j b,
  Bump j b xs ys -> i=j /\ a=b.
Proof.
  intro H; induction H; intros j b' H'; inversion H'; subst; try lia.
  match goal with H' : Bump _ _ xs ys |- _ =>
    destruct (IHBump _ _ H') end; split; congruence.
Qed.

Definition Waiting p xs i := i=p \/ Nat.odd (nth p xs 0)=true.

Lemma Bump_wait p i a xs ys j : Bump i a xs ys ->
  (i=p -> j<>p -> Nat.odd a=false) -> Waiting p xs i -> Waiting p ys j.
Proof.
  intros H HD HW; unfold Waiting in *.
  destruct (Nat.eq_dec j p) as [->|HJ]; [auto|right].
  destruct (Nat.eq_dec i p) as [->|HI].
  - destruct (Bump_nth H) as [_ ->]; rewrite odd_S, (HD eq_refl HJ); reflexivity.
  - rewrite (Bump_other (j:=p) H ltac:(lia)); destruct HW; congruence.
Qed.

Lemma Bump_app i a xs ys : Bump i a xs ys -> forall zs, Bump i a (xs++zs) (ys++zs).
Proof. intro H; induction H; intros; cbn; constructor; auto. Qed.

Lemma Bump_last xs a : Bump (length xs) a (xs++[a]) (xs++[1+a]).
Proof. induction xs; cbn; constructor; auto. Qed.

Lemma Tick_zeros_bump es xs u : Tick es true (repeat 0 (length es)) 0 xs u 0 ->
  Bump (length es) 0 (0::repeat 0 (length es)) (u::xs).
Proof.
  destruct es as [|e es]; intro H.
  - inversion H as [xs0 u0 middle root ys0 v0 d e H1 H2]; subst.
    exact (False_rect _ (Half_nonempty H1 eq_refl)).
  - destruct (Tick_functional (Tick_zeros e es) H) as [E [EU _]]; subst xs u.
    cbn[length]; rewrite <- zeros_snoc.
    pose proof (Bump_last (repeat 0 (length es)) 0) as HB; rewrite repeat_length in HB.
    constructor; exact HB.
Qed.

Definition RowRules (move:nat->nat->nat->Prop) rows xs :=
  length rows=length xs /\ forall i,
    Indexed (move i) (nth i xs 0) (nth i rows []).
Definition VisitBudget (original rows:list (list nat)) (xs:list nat) :=
  length xs=length original /\ forall i,
    nth i xs 0+outgoing rows i=outgoing original i.

Lemma RowRules_initial move rows : (forall i, Indexed (move i) 0 (nth i rows [])) ->
  RowRules move rows (repeat 0 (length rows)).
Proof. intro H; split; [rewrite repeat_length; reflexivity|intro i; rewrite nth_repeat; apply H]. Qed.

Lemma VisitBudget_initial rows : VisitBudget rows rows (repeat 0 (length rows)).
Proof. split; [apply repeat_length|intro i; rewrite nth_repeat; reflexivity]. Qed.

Lemma RowRules_pop move rows xs i j rows' a ys : RowRules move rows xs ->
  Pop i j rows rows' -> Bump i a xs ys -> move i a j /\ RowRules move rows' ys.
Proof.
  intros [EL HR] HP HB; destruct (Bump_nth HB) as [EX EY].
  specialize (HR i) as HI; rewrite (Pop_get HP), EX in HI; destruct HI as [HM HT].
  split; [exact HM|split].
  - pose proof (Pop_length HP); pose proof (Bump_length HB); lia.
  - intro v; destruct (Nat.eq_dec v i) as [->|Hne].
    + rewrite EY; exact HT.
    + rewrite (Bump_other HB Hne), <- (Pop_other HP Hne); apply HR.
Qed.

Lemma VisitBudget_pop original rows xs i j rows' a ys : VisitBudget original rows xs ->
  Pop i j rows rows' -> Bump i a xs ys -> VisitBudget original rows' ys.
Proof.
  intros [EL HV] HP HB; split; [pose proof (Bump_length HB); lia|].
  intro v; specialize (HV v); rewrite (Pop_outgoing HP) in HV.
  destruct (Nat.eq_dec v i) as [->|Hne].
  - destruct (Bump_nth HB) as [EX EY]; rewrite EX in HV; rewrite EY.
    rewrite mark_self in HV; lia.
  - rewrite (Bump_other HB Hne), mark_other in * by lia; lia.
Qed.

Lemma VisitBudget_bound original rows xs i : VisitBudget original rows xs ->
  nth i xs 0<=outgoing original i.
Proof. intros [_ H]; specialize (H i); lia. Qed.

Lemma VisitBudget_done original rows xs : VisitBudget original rows xs ->
  (forall i, nth i rows []=[]) -> xs=map (@length nat) original.
Proof.
  intros [EL H] HE; apply nth_ext with (d:=0) (d':=0).
  - rewrite length_map; assumption.
  - intros i HI; specialize (H i); unfold outgoing in H; rewrite HE in H; cbn[length] in H.
    pose proof (map_nth (@length nat) original [] i) as E; cbn[length] in E; lia.
Qed.

Lemma Split_bump e a q r q' r' : Split e a q r -> Split e (1+a) q' r' ->
  if xorb e (Nat.odd a) then q'=1+q /\ r'=r else q'=q /\ r'=1+r.
Proof.
  destruct e; intros H H'; inversion H; subst; inversion H'; subst;
    rewrite ?odd_0, ?odd_1; cbn; lia.
Qed.

Lemma Split_forward e a q r : Split e a q r -> xorb e (Nat.odd a)=true ->
  a=q*2+(if e then 0 else 1).
Proof.
  destruct e; intro H; inversion H; subst; rewrite ?odd_0, ?odd_1; cbn; lia.
Qed.

Lemma Alt_nth n : forall p i, i<n -> nth i (Alt p n) false=xorb p (Nat.odd i).
Proof.
  induction n; intros p [|i] HI; cbn in *; try lia.
  - destruct p; reflexivity.
  - rewrite IHn by lia; rewrite odd_S; destruct p, (Nat.odd i); reflexivity.
Qed.

Lemma odd_pred i : 0<i -> Nat.odd (i-1)=negb (Nat.odd i).
Proof. destruct i; [lia|intro H; cbn[Nat.sub]; rewrite Nat.sub_0_r, odd_S, negb_involutive; reflexivity]. Qed.

Lemma Scatter_bump i a xs xs' : Bump i a xs xs' -> forall es qs r qs' r',
  Scatter es xs qs r -> Scatter es xs' qs' r' ->
  if xorb (nth i es false) (Nat.odd a)
  then exists q, Bump i q qs qs' /\ r'=r
  else qs'=qs /\ r'=1+r.
Proof.
  intro H; induction H; intros es qs r ps s HC HD;
    inversion HC as [|e x q r0 es0 tail out r1 HS HT]; subst;
    inversion HD as [|e' x' q' s0 es' tail' out' s1 HS' HT']; subst; cbn[Nat.add nth].
  - destruct (Scatter_functional HT HT') as [-> ->].
    pose proof (Split_bump HS HS') as E.
    destruct (xorb e (Nat.odd a)); destruct E as [-> ->]; eauto using Bump_here.
  - destruct (Split_functional HS HS') as [-> ->].
    specialize (IHBump _ _ _ _ _ HT HT').
    destruct (xorb (nth i es0 false) (Nat.odd a)).
    + destruct IHBump as [q0 [HB ->]]; eauto using Bump_later.
    + destruct IHBump as [-> ->]; split; [reflexivity|lia].
Qed.

Lemma odd_four a : Nat.odd (a*4)=false.
Proof. replace (a*4) with ((a*2)*2) by lia; apply odd_0. Qed.

Lemma Scatter_at es xs qs r : Scatter es xs qs r -> forall i, i<length xs ->
  exists s, Split (nth i es false) (nth i xs 0) (nth i qs 0) s.
Proof.
  intro H; induction H; intros i HI; [cbn in HI; lia|].
  destruct i; cbn; [eexists; exact H|apply IHScatter; cbn in HI; lia].
Qed.

(* Positions in the whole state u::xs: 0 is the root, 1..N the body.
   Forward motion out of position 1 is deliberately absent: both compared
   half-steps below must have zero discarded count. *)
Inductive HalfMove (es:list bool) (root:nat) : nat -> nat -> nat -> nat -> Prop :=
| HalfMove_root a : HalfMove es root 0 a (length es) a
| HalfMove_back i a : xorb (nth i es false) (Nat.odd a)=false ->
    HalfMove es root (1+i) a 0 root
| HalfMove_forward i a q r : Split (nth (1+i) es false) a q r ->
    xorb (nth (1+i) es false) (Nat.odd a)=true ->
    HalfMove es root (2+i) a (1+i) q.

Lemma HalfMove_bound es root i a j b : HalfMove es root i a j b ->
  i<=length es -> j<=length es.
Proof. intro H; destruct H; lia. Qed.

Lemma Half_bump es inj xs u ys v xs' u' ys' v' i a :
  Half es inj xs u ys v 0 -> Half es inj xs' u' ys' v' 0 ->
  Bump i a (u::xs) (u'::xs') -> exists j b,
  HalfMove es v i a j b /\ Bump j b (v::ys) (v'::ys').
Proof.
  intros H H' HU.
  inversion H as [xs0 u0 discard qs r HC]; subst.
  inversion H' as [xs1 u1 discard' ps s HD]; subst.
  inversion HU as [a0 tail|i0 a0 head tail tail' HI]; subst.
  - destruct (Scatter_functional HC HD) as [E ->]; inversion E; subst ps.
    exists (length es),u; split; [constructor|].
    destruct (Scatter_length HC) as [_ EL]; cbn in EL; rewrite <- EL.
    constructor; apply Bump_last.
  - pose proof (Scatter_bump HI HC HD) as E.
    destruct (xorb (nth i0 es false) (Nat.odd a)) eqn:EF.
    + destruct E as [q [HQ ES]]; subst s.
      destruct (Bump_length HI) as [_ IL].
      destruct (Scatter_at HC IL) as [r0 HS].
      destruct (Bump_nth HI) as [EA _]; destruct (Bump_nth HQ) as [EQ _].
      rewrite EA, EQ in HS.
      destruct i0 as [|i0]; [inversion HQ; lia|].
      inversion HQ; subst. exists (1+i0); eexists; split.
      * eapply HalfMove_forward; eassumption.
      * constructor; apply Bump_app; assumption.
    + destruct E as [E ES]; inversion E; subst ps s.
      exists 0,(inj+r); split; [constructor; exact EF|].
      replace (inj+(1+r)) with (1+(inj+r)) by lia; constructor.
Qed.

Inductive AltMove (e:bool) (N root:nat) : nat -> nat -> nat -> nat -> Prop :=
| AltMove_root a : AltMove e N root 0 a N a
| AltMove_back i a : 0<i -> xorb (xorb e (Nat.odd i)) (Nat.odd a)=true ->
    AltMove e N root i a 0 root
| AltMove_forward i a q r : 1<i -> Split (xorb e (negb (Nat.odd i))) a q r ->
    xorb (xorb e (negb (Nat.odd i))) (Nat.odd a)=true ->
    AltMove e N root i a (i-1) q.

Lemma HalfMove_alt e N root i a j b : HalfMove (Alt e N) root i a j b ->
  i<=N -> AltMove e N root i a j b.
Proof.
  intro H; destruct H; intro HI.
  - rewrite Alt_length; constructor.
  - rewrite Alt_nth in H by lia. apply AltMove_back; [lia|].
    change (xorb (xorb e (Nat.odd (S i))) (Nat.odd a)=true).
    rewrite odd_S. destruct e, (Nat.odd i), (Nat.odd a); cbn in *; congruence.
  - rewrite Alt_nth in H, H0 by lia.
    replace (1+i) with ((2+i)-1) by lia.
    eapply AltMove_forward with (r:=r); [lia| |].
    + change (Split (xorb e (negb (Nat.odd (S (S i)))) ) a q r).
      rewrite !odd_S, negb_involutive.
      change (Split (xorb e (Nat.odd (S i))) a q r) in H.
      rewrite odd_S in H; exact H.
    + change (xorb (xorb e (negb (Nat.odd (S (S i))))) (Nat.odd a)=true).
      rewrite !odd_S, negb_involutive.
      change (xorb (xorb e (Nat.odd (S i))) (Nat.odd a)=true) in H0.
      rewrite odd_S in H0; exact H0.
Qed.

Lemma Tick_bump es early xs u ys v xs' u' ys' v' i a :
  Tick es early xs u ys v 0 -> Tick es early xs' u' ys' v' 0 ->
  Bump i a (u::xs) (u'::xs') -> exists root j b k c,
  HalfMove es root i a j b /\ HalfMove es v j b k c /\
  Bump k c (v::ys) (v'::ys').
Proof.
  intros H H' HU.
  inversion H as [xs0 u0 middle root ys0 v0 d e H1 H2]; subst.
  inversion H' as [xs1 u1 middle' root' ys1 v1 d' e' H1' H2']; subst.
  assert (d=0 /\ e=0 /\ d'=0 /\ e'=0) as [-> [-> [-> ->]]] by lia.
  destruct (Half_bump H1 H1' HU) as [j [b [HM HB]]].
  destruct (Half_bump H2 H2' HB) as [k [c [HM' HB']]]; eauto 8.
Qed.

(* A main walk and a marked unit that have not met, including the endpoints. *)
Inductive Apart (move:nat->nat->nat->Prop) :
    nat -> list nat -> nat -> nat -> list nat -> nat -> nat -> Prop :=
| Apart_nil xs i k : i<>k -> Apart move 0 xs i k xs i k
| Apart_cons n xs i a ys j k l zs p q : i<>k ->
    Bump i a xs ys -> move i a j -> move k (nth k xs 0) l ->
    Apart move n ys j l zs p q -> Apart move (1+n) xs i k zs p q.

Lemma Ticks_couple_or_apart es early move :
  (forall xs u ys v xs' u' ys' v' i a,
    Tick es early xs u ys v 0 -> Tick es early xs' u' ys' v' 0 ->
    Bump i a (u::xs) (u'::xs') -> exists j b,
    move i a j /\ Bump j b (v::ys) (v'::ys')) ->
  forall t xs u next v endc w noise z endn q i a k b,
  Tick es early xs u next v 0 -> Ticks es early t next v endc w ->
  Ticks es early t noise z endn q ->
  Bump i a (u::xs) (v::next) -> Bump k b (u::xs) (z::noise) ->
  (exists s ys root, s<=t /\ Ticks es early s noise z ys root /\
    Ticks es early (1+s) xs u ys root) \/
  (exists last j l, Apart move t (u::xs) i k last j l).
Proof.
  intro Route; induction t;
    intros xs u next v endc w noise z endn q i a k b HC HCR HNR HB HK;
    destruct (Nat.eq_dec i k) as [<-|Hneq].
  - left; pose proof (Bump_functional HB HK) as E; injection E as EZ EN; subst z noise.
    exists 0,next,v; split; [lia|split; [constructor|econstructor; [exact HC|constructor]]].
  - right; eauto using Apart_nil.
  - left; pose proof (Bump_functional HB HK) as E; injection E as EZ EN; subst z noise.
    exists 0,next,v; split; [lia|split; [constructor|econstructor; [exact HC|constructor]]].
  - inversion HCR as [|n0 xs0 u0 next' v' endc0 w0 HD HDR]; subst.
    inversion HNR as [|n0 xs0 u0 noise' z' endn0 q0 HE HER]; subst.
    destruct (Route _ _ _ _ _ _ _ _ _ _ HC HD HB) as [j [c [HM HB']]].
    destruct (Route _ _ _ _ _ _ _ _ _ _ HC HE HK) as [l [d [HN HK']]].
    destruct (IHt _ _ _ _ _ _ _ _ _ _ _ _ _ _ HD HDR HER HB' HK')
      as [[s [ys [root [HS [HF HG]]]]]|[last [j' [l' HA]]]].
    + left; exists (1+s),ys,root; split; [lia|split; eapply Ticks_cons; eassumption].
    + right; exists last,j',l'; econstructor; [exact Hneq|exact HB|exact HM| |exact HA].
      rewrite (proj1 (Bump_nth HK)); exact HN.
Qed.

(* The all-false half-step: ordinary single-column binary carries. *)
Inductive FlatMove (N:nat) : nat -> nat -> nat -> Prop :=
| FlatMove_root a : FlatMove N 0 a N
| FlatMove_back i a : 0<i -> Nat.odd a=false -> FlatMove N i a 0
| FlatMove_forward i a : 1<i -> Nat.odd a=true -> FlatMove N i a (i-1).

Lemma HalfMove_flat N root i a j b : HalfMove (repeat false N) root i a j b ->
  FlatMove N i a j.
Proof.
  intro H; destruct H; rewrite ?repeat_length in *.
  - constructor.
  - rewrite nth_repeat in H; cbn in H; apply FlatMove_back; auto; lia.
  - rewrite nth_repeat in H0; cbn in H0.
    replace (1+i) with ((2+i)-1) by lia; apply FlatMove_forward; auto; lia.
Qed.

Lemma FlatMove_functional N i a j : FlatMove N i a j ->
  forall k, FlatMove N i a k -> j=k.
Proof. intros H k H'; destruct H; inversion H'; subst; try lia; congruence. Qed.

Lemma FlatMove_distinct N i a j : 0<N -> FlatMove N i a j -> i<>j.
Proof. intros HN H; destruct H; lia. Qed.

Lemma FlatMove_bound N i a j : FlatMove N i a j -> i<=N -> j<=N.
Proof. intro H; destruct H; lia. Qed.

Inductive FlatStep (N:nat) : list nat -> list nat -> Prop :=
| FlatStep_make xs u ys v : Half (repeat false N) 1 xs u ys v 0 ->
    FlatStep N (u::xs) (v::ys).

Lemma FlatStep_length N xs ys : FlatStep N xs ys ->
  length xs=1+N /\ length ys=1+N.
Proof. intros H; destruct H; apply Half_length in H; rewrite repeat_length in H; cbn; lia. Qed.

Lemma FlatStep_mass N xs ys : FlatStep N xs ys -> total ys=1+total xs.
Proof. intro H; destruct H; apply Half_mass in H; cbn; lia. Qed.

Lemma FlatStep_functional N xs ys : FlatStep N xs ys ->
  forall zs, FlatStep N xs zs -> ys=zs.
Proof.
  intros H zs H'; destruct H; inversion H'; subst.
  match goal with H' : Half _ _ xs u _ _ _ |- _ =>
    destruct (Half_functional H H') as [-> [-> _]] end; reflexivity.
Qed.

Lemma FlatStep_mono N xs ys xs' ys' : FlatStep N xs ys -> FlatStep N xs' ys' ->
  Forall2 le xs xs' -> Forall2 le ys ys'.
Proof.
  intros H H' HL; destruct H; destruct H'; inversion HL as [|a b as' bs' Hu Hxs]; subst.
  destruct (Half_mono H H0 Hxs Hu) as [HY [HV _]]; constructor; assumption.
Qed.

Lemma FlatStep_unit N xs ys xs' ys' : FlatStep N xs ys -> FlatStep N xs' ys' ->
  One xs xs' -> One ys ys'.
Proof. intros H H' HU; destruct H; destruct H'; eapply Half_unit; eassumption. Qed.

Lemma FlatStep_route N xs ys xs' ys' i a : FlatStep N xs ys -> FlatStep N xs' ys' ->
  Bump i a xs xs' -> exists j b, FlatMove N i a j /\ Bump j b ys ys'.
Proof.
  intros H H' HB; destruct H; destruct H'.
  destruct (Half_bump H H0 HB) as [j [b [HM HD]]].
  exists j,b; split; [eapply HalfMove_flat; exact HM|exact HD].
Qed.

Lemma FlatStep_zero N : 0<N -> FlatStep N (0::repeat 0 N) (1::repeat 0 N).
Proof.
  destruct N; [lia|intros _; constructor].
  rewrite <- (zeros_snoc N) at 2.
  apply (Half_make 1 0 (qs:=repeat 0 N) (r:=0)).
  pose proof (Scatter_zeros (repeat false (S N))) as H; rewrite repeat_length in H; exact H.
Qed.

(* While the main unit carries towards the front, all positions behind it
   are even. At the root no parity restriction is imposed. *)
Definition CarryEven (xs:list nat) i := i=0 \/
  forall j, i<j -> j<length xs -> Nat.odd (nth j xs 0)=false.

Lemma FlatMove_carry N xs ys i a j : length xs=1+N -> CarryEven xs i ->
  Bump i a xs ys -> FlatMove N i a j -> CarryEven ys j.
Proof.
  intros EL HC HB HM; destruct HM; unfold CarryEven in *.
  - right; intros; pose proof (Bump_length HB); lia.
  - left; reflexivity.
  - right; intros k HK HL; destruct (Nat.eq_dec k i) as [->|Hne].
    + destruct (Bump_nth HB) as [_ ->]; rewrite odd_S, H0; reflexivity.
    + rewrite (Bump_other HB Hne); destruct HC as [HC|HC]; [lia|].
      apply HC; pose proof (Bump_length HB); lia.
Qed.

Inductive FlatSteps (N:nat) : nat -> list nat -> list nat -> Prop :=
| FlatSteps_nil xs : FlatSteps N 0 xs xs
| FlatSteps_next n xs ys zs : FlatSteps N n xs ys -> FlatStep N ys zs ->
    FlatSteps N (1+n) xs zs.

(* Move the next main unit before the current one. The two increments can
   be interchanged only when they affect distinct positions. *)
Lemma Bump_swap i a xs ys : Bump i a xs ys -> forall j b zs,
  Bump j b ys zs -> i<>j -> exists ds, Bump j b xs ds /\ Bump i a ds zs.
Proof.
  intro H; induction H; intros j c zs HJ Hne; inversion HJ; subst; try lia.
  - eexists; split; [constructor; eassumption|constructor].
  - eexists; split; [constructor|constructor; eassumption].
  - match goal with H' : Bump _ _ ys _ |- _ =>
      destruct (IHBump _ _ _ H' ltac:(lia)) as [ds [HD HE]] end.
    eexists; split; constructor; eassumption.
Qed.

Inductive FlatEarly (N:nat) : list nat -> list nat -> list nat -> Prop :=
| FlatEarly_make xs ys zs ds i a j b : FlatStep N xs ys -> FlatStep N ys zs ->
    Bump i a xs ys -> Bump j b ys zs -> Bump j b xs ds -> FlatEarly N xs ys ds.

Lemma FlatEarly_step N xs ys ds zs ws es : 0<N -> FlatEarly N xs ys ds ->
  FlatStep N ys zs -> FlatStep N zs ws -> FlatStep N ds es -> FlatEarly N ys zs es.
Proof.
  intros HN HE HY HZ HD; destruct HE as [xs ys zs' ds i a j b HX HY' HI HJ HDJ].
  pose proof (FlatStep_functional HY HY') as E; subst zs'.
  destruct (FlatStep_route HY HZ HJ) as [k [c [HM HK]]].
  destruct (FlatStep_route HX HD HDJ) as [l [d [HM' HL]]].
  pose proof (FlatMove_functional HM HM') as E; subst l.
  assert (E : c=d).
  { destruct (Bump_nth HK) as [HC _]; destruct (Bump_nth HL) as [HD' _].
    rewrite (Bump_other (j:=k) HJ ltac:(pose proof (FlatMove_distinct HN HM); lia)) in HC.
    congruence. }
  subst d; econstructor; eassumption.
Qed.

(* Before a perturbed unit reaches the root/last pair, its index decreases.
   Once there, the main carry index decreases until one of the two targets
   is met. This rank avoids classifying complete counter bit patterns. *)
Definition FlatRank N i k := if (k =? 0) || (k =? N) then i else N+k.

Lemma FlatRank_hub N i k : k=0 \/ k=N -> FlatRank N i k=i.
Proof. intros [-> | ->]; unfold FlatRank; rewrite ?Nat.eqb_refl, ?orb_true_r; reflexivity. Qed.

Lemma FlatRank_inner N i k : k<>0 -> k<>N -> FlatRank N i k=N+k.
Proof.
  intros H0 HN; unfold FlatRank.
  destruct (k =? 0) eqn:E; [apply Nat.eqb_eq in E; contradiction|].
  destruct (k =? N) eqn:E'; [apply Nat.eqb_eq in E'; contradiction|reflexivity].
Qed.

Lemma FlatRank_bound N i k : i<=N -> k<=N -> FlatRank N i k<=N*2.
Proof. unfold FlatRank; destruct ((k =? 0) || (k =? N)); lia. Qed.

Lemma FlatRank_step N xs i a j k l : length xs=1+N -> i<=N -> k<=N ->
  CarryEven xs i -> i<>k -> j<>k -> FlatMove N i a j ->
  FlatMove N k (nth k xs 0) l -> FlatRank N j l < FlatRank N i k.
Proof.
  intros EL HI HK HC HIK HJK HM HD.
  destruct (Nat.eq_dec k 0) as [->|HK0].
  - inversion HD; subst; try lia.
    rewrite !FlatRank_hub by auto; destruct HM; lia.
  - destruct (Nat.eq_dec k N) as [->|HKN].
    + assert (Hi : 0<i) by (inversion HM; subst; lia).
      assert (EO : Nat.odd (nth N xs 0)=false).
      { destruct HC as [HC|HC]; [lia|apply HC; lia]. }
      assert (Hl : l=0) by (inversion HD; subst; try lia; congruence).
      subst l; rewrite !FlatRank_hub by auto; destruct HM; lia.
    + rewrite (@FlatRank_inner N i k HK0 HKN).
      destruct HD; [contradiction| |].
      * rewrite FlatRank_hub by auto; pose proof (FlatMove_bound HM HI); lia.
      * rewrite FlatRank_inner by lia; lia.
Qed.

Lemma Bump_value p i a xs ys : Bump i a xs ys ->
  nth p ys 0=if p =? i then 1+nth p xs 0 else nth p xs 0.
Proof.
  intro H; destruct (p =? i) eqn:E.
  - apply Nat.eqb_eq in E; subst p; destruct (Bump_nth H) as [-> ->]; reflexivity.
  - apply Nat.eqb_neq in E; eapply Bump_other; eassumption.
Qed.
Arguments Bump_value p {i a xs ys} _.

Definition EarlyMove N next k a l := FlatMove N k (if k =? next then 1+a else a) l.

Lemma EarlyMove_away N next k a l : k<>next -> EarlyMove N next k a l -> FlatMove N k a l.
Proof.
  intros H; unfold EarlyMove; destruct (k =? next) eqn:E; [apply Nat.eqb_eq in E; contradiction|auto].
Qed.

Lemma EarlyMove_bound N next k a l : EarlyMove N next k a l -> k<=N -> l<=N.
Proof. apply FlatMove_bound. Qed.

Lemma FlatMove_root_value N a j : FlatMove N 0 a j -> j=N.
Proof. intro H; inversion H; subst; lia. Qed.

Lemma FlatMove_positive N i a j : FlatMove N i a j -> 0<i ->
  j=if Nat.odd a then i-1 else 0.
Proof. intros H HI; destruct H; try lia; rewrite H0; reflexivity. Qed.

Lemma EarlyMove_root_value N next a l : EarlyMove N next 0 a l -> l=N.
Proof. apply FlatMove_root_value. Qed.

Lemma EarlyMove_cases N next k a l : EarlyMove N next k a l ->
  (k=0 /\ l=N) \/ (0<k /\ l=0) \/ (1<k /\ l=k-1).
Proof. intro H; destruct H; auto. Qed.

Lemma FlatStep_early_route N xs ds dt es et next b k a : Bump next b xs ds ->
  FlatStep N ds dt -> FlatStep N es et -> Bump k a ds es ->
  exists l c, EarlyMove N next k (nth k xs 0) l /\ Bump l c dt et.
Proof.
  intros HB HD HE HK; destruct (FlatStep_route HD HE HK) as [l [c [HM HL]]].
  exists l,c; split; [|exact HL].
  unfold EarlyMove; rewrite <- (Bump_value k HB), (proj1 (Bump_nth HK)); exact HM.
Qed.

(* Control phases for a unit added to the early orbit. The rank is linear;
   bit restrictions concern only a carry interval or the last two bits. *)
Inductive EarlyRank (N:nat) : list nat -> nat -> nat -> nat -> Prop :=
| ER_seek xs i k : 0<k -> k<N -> EarlyRank N xs i k (N*2+9+k)
| ER_wait xs i k : 0<i -> (k=0 \/ k=N) -> EarlyRank N xs i k (N+8+i)
| ER_start xs : EarlyRank N xs 0 N (N+7)
| ER_flip xs : Nat.odd (nth N xs 0)=false -> Nat.odd (nth (N-1) xs 0)=true ->
    EarlyRank N xs N (N-1) (N+6)
| ER_kick xs : Nat.odd (nth N xs 0)=true -> Nat.odd (nth (N-1) xs 0)=true ->
    EarlyRank N xs 0 (N-2) (N+5)
| ER_lead xs i k : 0<k -> i=k+3 ->
    (forall p, k<p -> p<=i -> Nat.odd (nth p xs 0)=true) -> EarlyRank N xs i k (i+3)
| ER_carry xs i k : 0<i -> i<N -> (k=0 \/ k=N) ->
    (i=N-1 -> k=N \/ Nat.odd (nth i xs 0)=true) -> EarlyRank N xs i k (i+2)
| ER_top xs : Nat.odd (nth N xs 0)=true -> EarlyRank N xs N 0 (N+2)
| ER_root xs : Nat.odd (nth N xs 0)=false -> Nat.odd (nth (N-1) xs 0)=false ->
    EarlyRank N xs 0 N 2
| ER_last xs : Nat.odd (nth N xs 0)=false -> Nat.odd (nth (N-1) xs 0)=false ->
    EarlyRank N xs N (N-1) 1.

Lemma EarlyRank_initial N xs i k : i<=N -> k<=N -> i<>k ->
  exists r, EarlyRank N xs i k r /\ r<=N*3+9.
Proof.
  intros HI HK Hne; destruct (Nat.eq_dec k 0) as [->|HK0].
  - exists (N+8+i); split; [constructor; auto; lia|lia].
  - destruct (Nat.eq_dec k N) as [->|HKN].
    + destruct i; [exists (N+7); split; [constructor|lia]|].
      exists (N+8+S i); split; [constructor; auto; lia|lia].
    + exists (N*2+9+k); split; [constructor; lia|lia].
Qed.

Lemma EarlyRank_step N xs i k r a ys j l : EarlyRank N xs i k r ->
  3<=N -> length xs=1+N -> i<=N -> k<=N -> CarryEven xs i -> i<>k ->
  Bump i a xs ys -> FlatMove N i a j -> EarlyMove N j k (nth k xs 0) l -> j<>l ->
  exists s, EarlyRank N ys j l s /\ s<r.
Proof.
  intros HR HN EL HI HK HC Hne HB HM HD Hout.
  pose proof (FlatMove_bound HM HI) as HJ.
  pose proof (EarlyMove_bound HD HK) as HL.
  destruct (Bump_nth HB) as [HA HY]; rewrite <- HA in HM.
  assert (HO : forall p, p<>i -> nth p ys 0=nth p xs 0) by (intros; eapply Bump_other; eassumption).
  assert (HP : Nat.odd (nth i ys 0)=negb (Nat.odd (nth i xs 0))).
  { rewrite HA, HY, odd_S; reflexivity. }
  destruct HR as [xs i k K0 KN|xs i k I0 KH|xs|xs EN EP|xs EN EP|
    xs i k K0 EIK HW|xs i k I0 IN KH HC0|xs EN|xs EN EP|xs EN EP].
  - destruct (EarlyMove_cases HD) as [[E _]|[[H ->]|[H ->]]]; [lia| |].
    + exists (N+8+j); split; [apply ER_wait; auto; lia|lia].
    + exists (N*2+9+(k-1)); split; [apply ER_seek; lia|lia].
  - assert (JI : j<i) by (inversion HM; subst; lia).
    assert (LH : l=0 \/ l=N).
    { destruct KH as [-> | ->].
      - right; apply EarlyMove_root_value in HD; exact HD.
      - assert (EN : Nat.odd (nth N xs 0)=false).
        { destruct HC as [HC|HC]; [lia|apply HC; lia]. }
        apply EarlyMove_away in HD; [|lia].
        pose proof (FlatMove_positive HD ltac:(lia)) as E; rewrite EN in E; auto. }
    destruct (Nat.eq_dec j 0) as [->|J0].
    + assert (l=N) by lia; subst l; exists (N+7); split; [constructor|lia].
    + exists (N+8+j); split; [apply ER_wait; auto; lia|lia].
  - apply FlatMove_root_value in HM; subst j.
    unfold EarlyMove in HD; rewrite Nat.eqb_refl in HD.
    pose proof (FlatMove_positive HD ltac:(lia)) as E; rewrite odd_S in E.
    destruct (Nat.odd (nth N xs 0)) eqn:EN; cbn in E; subst l.
    + exists (N+2); split; [apply ER_top; rewrite HO by lia; exact EN|lia].
    + destruct (Nat.odd (nth (N-1) xs 0)) eqn:EP.
      * exists (N+6); split; [apply ER_flip; rewrite HO by lia; assumption|lia].
      * exists 1; split; [apply ER_last; rewrite HO by lia; assumption|lia].
  - pose proof (FlatMove_positive HM ltac:(lia)) as E; rewrite EN in E; subst j.
    apply EarlyMove_away in HD; [|lia].
    pose proof (FlatMove_positive HD ltac:(lia)) as E; rewrite EP in E.
    replace (N-1-1) with (N-2) in E by lia; subst l.
    exists (N+5); split; [apply ER_kick|lia].
    + rewrite HP, EN; reflexivity.
    + rewrite HO by lia; exact EP.
  - apply FlatMove_root_value in HM; subst j.
    apply EarlyMove_away in HD; [|lia].
    pose proof (FlatMove_positive HD ltac:(lia)) as E.
    destruct (Nat.eq_dec l 0) as [->|L0].
    + exists (N+2); split; [apply ER_top; rewrite HO by lia; exact EN|lia].
    + assert (Nat.odd (nth (N-2) xs 0)=true /\ l=N-3) as [EK EKL].
      { destruct (Nat.odd (nth (N-2) xs 0)); cbn in E; split; auto; lia. }
      exists (N+3); split; [apply ER_lead; try lia|lia].
      intros p PL PN; rewrite HO by lia.
      assert (p=N-2 \/ p=N-1 \/ p=N) as [-> | [-> | ->]] by lia; assumption.
  - assert (EI : Nat.odd (nth i xs 0)=true) by (apply HW; lia).
    pose proof (FlatMove_positive HM ltac:(lia)) as E; rewrite EI in E; subst j.
    apply EarlyMove_away in HD; [|lia].
    pose proof (FlatMove_positive HD K0) as E.
    destruct (Nat.eq_dec l 0) as [->|L0].
    + exists (i-1+2); split; [apply ER_carry; try lia|lia].
      intros; right; rewrite HO by lia; apply HW; lia.
    + assert (Nat.odd (nth k xs 0)=true /\ l=k-1) as [EK EKL].
      { destruct (Nat.odd (nth k xs 0)); cbn in E; split; auto; lia. }
      exists (i-1+3); split; [apply ER_lead; try lia|lia].
      intros p PL PI; rewrite HO by lia; destruct (Nat.eq_dec p k) as [->|PK]; [exact EK|apply HW; lia].
  - assert (JI : j<i) by (inversion HM; subst; lia).
    assert (LH : (k=0 /\ l=N) \/ (k=N /\ l=0)).
    { destruct KH as [-> | ->].
      - left; split; [reflexivity|apply EarlyMove_root_value in HD; exact HD].
      - right; split; [reflexivity|].
        assert (EN : Nat.odd (nth N xs 0)=false).
        { destruct HC as [HC|HC]; [lia|apply HC; lia]. }
        apply EarlyMove_away in HD; [|lia].
        pose proof (FlatMove_positive HD ltac:(lia)) as E; rewrite EN in E; exact E. }
    destruct (Nat.eq_dec j 0) as [->|J0].
    + destruct LH as [[-> ->]|[_ E]]; [|congruence].
      assert (EI : Nat.odd (nth i xs 0)=false) by (inversion HM; subst; try lia; congruence).
      assert (IP : i<N-1).
      { destruct (Nat.eq_dec i (N-1)) as [E|E]; [destruct (HC0 E); [lia|congruence]|lia]. }
      destruct HC as [HC|HC]; [lia|].
      exists 2; split; [apply ER_root; rewrite HO by lia; apply HC; lia|lia].
    + exists (j+2); split; [apply ER_carry; try lia; destruct LH as [[_ ->]|[_ ->]]; auto|lia].
  - pose proof (FlatMove_positive HM ltac:(lia)) as E; rewrite EN in E; subst j.
    apply EarlyMove_root_value in HD; subst l.
    exists (N-1+2); split; [apply ER_carry; try lia; auto|lia].
  - apply FlatMove_root_value in HM; subst j.
    unfold EarlyMove in HD; rewrite Nat.eqb_refl in HD.
    pose proof (FlatMove_positive HD ltac:(lia)) as E; rewrite odd_S, EN in E; cbn in E; subst l.
    exists 1; split; [apply ER_last; rewrite HO by lia; assumption|lia].
  - pose proof (FlatMove_positive HM ltac:(lia)) as E; rewrite EN in E; subst j.
    apply EarlyMove_away in HD; [|lia].
    pose proof (FlatMove_positive HD ltac:(lia)) as E; rewrite EP in E; congruence.
Qed.

Lemma FlatSteps_cons N xs ys : FlatStep N xs ys -> forall n zs,
  FlatSteps N n ys zs -> FlatSteps N (1+n) xs zs.
Proof. intros HS n zs H; induction H; econstructor; eauto using FlatSteps_nil. Qed.

Lemma FlatSteps_uncons N n xs zs : FlatSteps N n xs zs -> forall m, n=1+m ->
  exists ys, FlatStep N xs ys /\ FlatSteps N m ys zs.
Proof.
  intro H; induction H; intros m E; [lia|].
  destruct n.
  - inversion H; subst; assert (m=0) by lia; subst m; exists zs; split; [exact H0|constructor].
  - destruct (IHFlatSteps n eq_refl) as [first [HS HP]].
    assert (m=1+n) by lia; subst m; exists first; split; [exact HS|econstructor; eassumption].
Qed.

Lemma FlatStep_below N xs ys zs : FlatStep N ys zs -> Forall2 le xs ys ->
  exists ws, FlatStep N xs ws /\ Forall2 le ws zs.
Proof.
  intros H HL; destruct H; inversion HL as [|u' u0 body' body Hu HX]; subst.
  destruct (Half_length H) as [EL _]; rewrite repeat_length in EL.
  assert (EB : length body'=N) by (pose proof (Forall2_length HX); lia).
  assert (HB : body'<>[]).
  { intro E; subst body'; inversion HX; subst; exact (Half_nonempty H eq_refl). }
  destruct (@Half_total (repeat false N) 1 body' u' ltac:(rewrite repeat_length; lia) HB)
    as [out [root [leak HS]]].
  destruct (Half_mono HS H HX Hu) as [HO [HR HD]].
  assert (leak=0) by lia; subst leak; exists (root::out); split; constructor; assumption.
Qed.

Lemma Bump_square i a xs ys j b zs ds c es : Bump i a xs ys -> Bump j b ys zs ->
  Bump j b xs ds -> Bump i c ds es -> es=zs.
Proof.
  intros HI HJ HD HE.
  assert (Hne : i<>j).
  { intro E; subst j; pose proof (Bump_nth HI); pose proof (Bump_nth HJ); pose proof (Bump_nth HD); lia. }
  destruct (Bump_swap HI HJ Hne) as [ws [HW HZ]].
  pose proof (Bump_functional HW HD) as E; subst ws; eapply Bump_functional; eassumption.
Qed.

Lemma FlatEarly_fill N xs ys ds i a b es : FlatEarly N xs ys ds ->
  Bump i a xs ys -> Bump i b ds es -> FlatStep N ys es.
Proof.
  intros H HB HE; destruct H as [xs ys zs ds j c k d HX HY HJ HK HD].
  destruct (Bump_position HB HJ) as [-> _].
  pose proof (Bump_square HJ HK HD HE) as ->; exact HY.
Qed.

Lemma FlatEarly_next N xs ys ds zs j b : FlatEarly N xs ys ds ->
  FlatStep N ys zs -> Bump j b ys zs -> Bump j b xs ds.
Proof.
  intros H HY HB; destruct H as [xs ys zs' ds i a k c HX HY' HI HK HD].
  pose proof (FlatStep_functional HY HY') as E; subst zs'.
  destruct (Bump_position HB HK) as [-> ->]; exact HD.
Qed.

Lemma FlatEarly_couple N t : 3<=N -> forall xs ys ds noise endc endn i a k b r,
  FlatEarly N xs ys ds -> FlatSteps N (1+t) ys endc -> FlatSteps N t noise endn ->
  Bump i a xs ys -> Bump k b ds noise -> CarryEven xs i -> EarlyRank N xs i k r -> r<t ->
  exists s zs, s<=t /\ FlatSteps N s noise zs /\ FlatSteps N (2+s) xs zs.
Proof.
  intro HN; induction t; intros xs ys ds noise endc endn i a k b r HE HCR HNR HB HK HC HR HT;
    [lia|].
  assert (HX : FlatStep N xs ys) by (inversion HE; eassumption).
  destruct (Nat.eq_dec i k) as [<-|Hne].
  - exists 0,noise; split; [lia|split; [constructor|]].
    apply FlatSteps_cons with (ys:=ys); [exact HX|].
    apply FlatSteps_cons with (ys:=noise); [eapply FlatEarly_fill; eassumption|constructor].
  - destruct (FlatSteps_uncons HCR eq_refl) as [next [HY HCR']].
    destruct (FlatSteps_uncons HCR' eq_refl) as [future [HZ HCR'']].
    destruct (FlatSteps_uncons HNR eq_refl) as [noise' [HNstep HNR']].
    destruct (FlatStep_below HNstep (One_le (Bump_one HK))) as [ds' [HD _]].
    pose proof (FlatEarly_step (N:=N) ltac:(lia) HE HY HZ HD) as HE'.
    destruct (FlatStep_route HX HY HB) as [j [c [HM HB']]].
    pose proof (FlatEarly_next HE HY HB') as HBnext.
    destruct (FlatStep_early_route HBnext HD HNstep HK) as [l [d [HM' HK']]].
    destruct (Nat.eq_dec j l) as [<-|Hne'].
    + exists 1,noise'; split; [lia|split].
      * apply FlatSteps_cons with (ys:=noise'); [exact HNstep|constructor].
      * apply FlatSteps_cons with (ys:=ys); [exact HX|].
        apply FlatSteps_cons with (ys:=next); [exact HY|].
        apply FlatSteps_cons with (ys:=noise'); [eapply FlatEarly_fill; eassumption|constructor].
    + pose proof (proj1 (FlatStep_length HX)) as EL.
      assert (HI : i<=N) by (pose proof (Bump_length HB); lia).
      assert (HKb : k<=N) by (pose proof (Bump_length HK); pose proof (Bump_length HBnext); lia).
      destruct (EarlyRank_step HR HN EL HI HKb HC Hne HB HM HM' Hne') as [s [HS ER]].
      destruct (IHt _ _ _ _ _ _ _ _ _ _ _ HE' HCR' HNR' HB' HK'
        (FlatMove_carry EL HC HB HM) HS ltac:(lia)) as [q [zs [HQ [HNQ HCQ]]]].
      exists (1+q),zs; split; [lia|split; eapply FlatSteps_cons; eassumption].
Qed.

Lemma FlatSteps_cancel N n : forall xs ys, FlatSteps N n xs ys ->
  forall t zs, FlatSteps N t xs zs -> forall m, t=n+m -> FlatSteps N m ys zs.
Proof.
  induction n; intros xs ys HP t zs HT m E.
  - inversion HP; subst; exact HT.
  - destruct (FlatSteps_uncons HP eq_refl) as [first [HS HP']].
    destruct (FlatSteps_uncons (m:=n+m) HT ltac:(lia)) as [first' [HS' HT']].
    pose proof (FlatStep_functional HS HS') as E'; subst first'.
    eapply IHn; eassumption || reflexivity.
Qed.

Lemma FlatSteps_functional N n xs ys zs : FlatSteps N n xs ys -> FlatSteps N n xs zs -> ys=zs.
Proof.
  intros H H'; pose proof (FlatSteps_cancel H H' 0 ltac:(lia)) as E.
  inversion E; reflexivity.
Qed.

Theorem FlatEarly_absorbs N t xs ys ds noise endc endn i a k b : 3<=N -> N*3+9<t ->
  FlatEarly N xs ys ds -> FlatSteps N (1+t) ys endc -> FlatSteps N t noise endn ->
  Bump i a xs ys -> Bump k b ds noise -> CarryEven xs i -> endn=endc.
Proof.
  intros HN HT HE HCR HNR HB HK HC.
  assert (HX : FlatStep N xs ys) by (inversion HE; eassumption).
  destruct (Nat.eq_dec i k) as [<-|Hne].
  - pose proof (FlatEarly_fill HE HB HK) as HY.
    assert (HP : FlatSteps N 1 ys noise) by (eapply FlatSteps_cons; [exact HY|constructor]).
    eapply FlatSteps_functional; [exact HNR|eapply FlatSteps_cancel; [exact HP|exact HCR|reflexivity]].
  - pose proof (proj1 (FlatStep_length HX)) as EL.
    assert (HI : i<=N) by (pose proof (Bump_length HB); lia).
    assert (HDlen : length ds=length xs).
    { inversion HE; subst; match goal with H : Bump _ _ xs ds |- _ => pose proof (Bump_length H); lia end. }
    assert (HKb : k<=N) by (pose proof (Bump_length HK); lia).
    destruct (EarlyRank_initial xs HI HKb Hne) as [r [HR ER]].
    destruct (FlatEarly_couple (N:=N) (t:=t) HN HE HCR HNR HB HK HC HR ltac:(lia))
      as [s [zs [HS [HNS HCS]]]].
    assert (HCR0 : FlatSteps N (2+t) xs endc) by (eapply FlatSteps_cons; eassumption).
    eapply FlatSteps_functional with (n:=t-s) (xs:=zs).
    + eapply FlatSteps_cancel; [exact HNS|exact HNR|lia].
    + eapply FlatSteps_cancel; [exact HCS|exact HCR0|lia].
Qed.

Lemma FlatSteps_one N xs ys : FlatSteps N 1 xs ys -> FlatStep N xs ys.
Proof.
  intro H; destruct (FlatSteps_uncons H eq_refl) as [zs [HS HT]].
  inversion HT; subst; exact HS.
Qed.

Lemma FlatSteps_unsnoc N n xs zs : FlatSteps N (1+n) xs zs ->
  exists ys, FlatSteps N n xs ys /\ FlatStep N ys zs.
Proof. intro H; inversion H; subst; eauto. Qed.

Lemma FlatEarly_steps N t : 0<N -> forall xs ys ds endc endd,
  FlatEarly N xs ys ds -> FlatSteps N (1+t) ys endc -> FlatSteps N t ds endd ->
  exists p q, FlatSteps N t xs p /\ FlatStep N p q /\ FlatStep N q endc /\ FlatEarly N p q endd.
Proof.
  intro HN; induction t; intros xs ys ds endc endd HE HC HD.
  - inversion HD; subst; exists xs,ys; split; [constructor|split].
    + inversion HE; eassumption.
    + split; [apply FlatSteps_one; exact HC|exact HE].
  - destruct (FlatSteps_uncons HC eq_refl) as [next [HY HC']].
    destruct (FlatSteps_uncons HC' eq_refl) as [future [HZ HC'']].
    destruct (FlatSteps_uncons HD eq_refl) as [ds' [HS HD']].
    destruct (IHt _ _ _ _ _ (FlatEarly_step HN HE HY HZ HS) HC' HD') as [p [q [HP HQ]]].
    exists p,q; split; [|exact HQ].
    eapply FlatSteps_cons; [inversion HE; eassumption|exact HP].
Qed.

Lemma Flat_couple N t : 0<N -> forall xs ys noise endc endn i a k b,
  FlatStep N xs ys -> FlatSteps N (1+t) ys endc -> FlatSteps N t noise endn ->
  Bump i a xs ys -> Bump k b xs noise -> CarryEven xs i -> FlatRank N i k<t ->
  exists p q, FlatSteps N t xs p /\ FlatStep N p q /\ FlatStep N q endc /\
    (endn=q \/ FlatEarly N p q endn).
Proof.
  intro HN; induction t; intros xs ys noise endc endn i a k b HX HCR HNR HB HK HC HR; [lia|].
  destruct (Nat.eq_dec i k) as [<-|Hne].
  - pose proof (Bump_functional HB HK) as E; subst noise.
    assert (HP : FlatSteps N (1+S t) xs endn) by (eapply FlatSteps_cons; eassumption).
    destruct (FlatSteps_unsnoc HP) as [p [Hpre Hlast]].
    exists p,endn; split; [exact Hpre|split; [exact Hlast|split; [|auto]]].
    apply FlatSteps_one; eapply FlatSteps_cancel; [exact HNR|exact HCR|lia].
  - destruct (FlatSteps_uncons HCR eq_refl) as [next [HY HCR']].
    destruct (FlatStep_route HX HY HB) as [j [c [HM HB']]].
    destruct (Nat.eq_dec j k) as [<-|Hne'].
    + assert (E : b=c).
      { destruct (Bump_nth HK) as [EK _]; destruct (Bump_nth HB') as [EJ _].
        rewrite (Bump_other (j:=j) HB ltac:(lia)) in EJ; congruence. }
      subst b; assert (HE : FlatEarly N xs ys noise) by (econstructor; eassumption).
      destruct (FlatEarly_steps HN HE HCR HNR) as [p [q [HP [HQ [HEnd HE']]]]].
      exists p,q; auto.
    + destruct (FlatSteps_uncons HNR eq_refl) as [noise' [HS HNR']].
      destruct (FlatStep_route HX HS HK) as [l [d [HD HK']]].
      rewrite <- (proj1 (Bump_nth HK)) in HD.
      pose proof (proj1 (FlatStep_length HX)) as EL.
      assert (HI : i<=N) by (pose proof (Bump_length HB); lia).
      assert (HKb : k<=N) by (pose proof (Bump_length HK); lia).
      pose proof (FlatRank_step EL HI HKb HC Hne Hne' HM HD) as ER.
      destruct (IHt _ _ _ _ _ _ _ _ _ HY HCR' HNR' HB' HK'
        (FlatMove_carry EL HC HB HM) ltac:(lia)) as [p [q [HP HQ]]].
      exists p,q; split; [eapply FlatSteps_cons; eassumption|exact HQ].
Qed.

Theorem Flat_absorbs N t xs ys noise endc endn i a k b : 0<N -> N*2<t ->
  FlatStep N xs ys -> FlatSteps N (1+t) ys endc -> FlatSteps N t noise endn ->
  Bump i a xs ys -> Bump k b xs noise -> CarryEven xs i ->
  exists p q, FlatSteps N t xs p /\ FlatStep N p q /\ FlatStep N q endc /\
    (endn=q \/ FlatEarly N p q endn).
Proof.
  intros HN HT HX HCR HNR HB HK HC; eapply Flat_couple; eauto.
  pose proof (proj1 (FlatStep_length HX)) as EL.
  assert (HI : i<=N) by (pose proof (Bump_length HB); lia).
  assert (HKb : k<=N) by (pose proof (Bump_length HK); lia).
  pose proof (FlatRank_bound HI HKb); lia.
Qed.

Lemma le_trans_list xs ys zs : Forall2 le xs ys -> Forall2 le ys zs -> Forall2 le xs zs.
Proof.
  intro H; revert zs; induction H; intros zs H'; inversion H'; subst; constructor; eauto; lia.
Qed.

Lemma le_tail_list xs ys : Forall2 le xs ys -> Forall2 le (tl xs) (tl ys).
Proof. intro H; destruct H; cbn; [constructor|assumption]. Qed.

(* The lower anchor is subfixed, not necessarily zero. Its body mass is
   unavailable to the root, giving a larger independent safe window. *)
Theorem FlatSteps_window N bounds h lower next t :
  Half (repeat false N) 0 bounds h bounds h 0 ->
  FlatStep N lower next -> Forall2 le lower next ->
  forall xs, Forall2 le lower xs -> Forall2 le (tl xs) bounds ->
  total xs+t<=h+total (tl lower) -> exists ys,
    FlatSteps N t xs ys /\ Forall2 le lower ys /\
    Forall2 le (tl ys) bounds /\ total ys=total xs+t.
Proof.
  intros HB HL Hstable; induction t; intros xs Hlow Hbox Hbudget.
  - exists xs; split; [constructor|repeat split; auto; lia].
  - destruct xs as [|u xs].
    { inversion Hbox; subst bounds; exact (False_rect _ (Half_nonempty HB eq_refl)). }
    assert (Hu : u<=h).
    { pose proof (total_le (le_tail_list Hlow)); cbn[tl total] in *; lia. }
    destruct (Half_box_total 1 HB Hbox Hu) as [body [root [HS Hbound]]].
    assert (Hstep : FlatStep N (u::xs) (root::body)) by (constructor; exact HS).
    assert (Hlower : Forall2 le lower (root::body)).
    { eapply le_trans_list; [exact Hstable|eapply FlatStep_mono; eassumption]. }
    pose proof (FlatStep_mass Hstep) as HM.
    destruct (IHt (root::body) Hlower Hbound ltac:(lia)) as [ys [HT [HLo [HBo HMass]]]].
    exists ys; split; [eapply FlatSteps_cons; eassumption|repeat split; auto; lia].
Qed.

Definition FlatLower bounds h := (2+h*2)::0::bounds++[2+h*2].
Definition FlatUpper bounds h := bounds++[1+h*2;3+h*4].

Lemma FlatBox_upper N bounds h : FlatBox N bounds h -> FlatBox (2+N) (FlatUpper bounds h) (3+h*4).
Proof.
  intro H; unfold FlatUpper.
  replace [1+h*2;3+h*4] with ([1+h*2]++[3+h*4]) by reflexivity; rewrite app_assoc.
  replace (3+h*4) with (1+(1+h*2)*2) by lia; constructor; constructor; exact H.
Qed.

Lemma CarryEven_penult xs a b : Nat.odd b=false -> CarryEven (xs++[a;b]) (length xs).
Proof.
  intro H; right; intros p HP HL; rewrite length_app in HL; cbn[length] in HL.
  assert (p=length xs+1) by lia; subst p.
  rewrite app_nth2 by lia; replace (length xs+1-length xs) with 1 by lia; exact H.
Qed.

Lemma FlatLower_step N bounds h : FlatBox N bounds h -> exists next,
  FlatStep (2+N) (FlatLower bounds h) next /\ Bump (1+N) h (FlatLower bounds h) next /\
  CarryEven (FlatLower bounds h) (1+N).
Proof.
  intro H; destruct (FlatBox_spec H) as [EL [HB EH]].
  destruct (Half_fixed_scatter HB) as [qs [EB HS]]; subst bounds.
  rewrite length_app in EL; cbn[length] in EL.
  unfold FlatLower; exists ((2+h*2)::((0::qs++[1+h])++[2+h*2])); split.
  - constructor.
    replace (repeat false (2+N)) with (false::(repeat false N++[false]))
      by (pose proof (repeat_app false N 1) as E; replace (N+1) with (1+N) in E by lia;
          cbn[repeat Nat.add] in E |- *; congruence).
    apply (Half_make 1 (2+h*2) (qs:=0::qs++[1+h]) (r:=1+h*2)).
    replace (1+h*2) with (0+(h+(1+h))) by lia.
    apply Scatter_cons; [apply (Split_even false 0)|].
    eapply (Scatter_app HS); apply Scatter_single.
    replace (2+h*2) with ((1+h)*2) by lia; constructor.
  - split.
    + replace (1+N) with (1+(1+length qs)) by lia.
      apply Bump_later, Bump_later, Bump_app, Bump_last.
    + rewrite <- app_assoc; change (CarryEven (((2+h*2)::0::qs)++[h;2+h*2]) (1+N)).
      replace (1+N) with (length ((2+h*2)::0::qs)) by (cbn; lia).
      apply CarryEven_penult; replace (2+h*2) with ((1+h)*2) by lia; apply odd_0.
Qed.

Theorem FlatLower_window N bounds h k t xs : FlatBox N bounds h ->
  Forall2 le (FlatLower bounds h) xs -> Forall2 le (tl xs) (FlatUpper bounds h) ->
  total xs<=total (FlatLower bounds h)+k -> k+t+1<=2+h*2 -> exists ys,
    FlatSteps (2+N) t xs ys /\ Forall2 le (FlatLower bounds h) ys /\
    Forall2 le (tl ys) (FlatUpper bounds h) /\ total ys=total xs+t.
Proof.
  intros H HL HU HM HT; destruct (FlatLower_step H) as [next [HS [HB HC]]].
  destruct (FlatBox_spec (FlatBox_upper H)) as [_ [Hbox _]].
  eapply FlatSteps_window; [exact Hbox|exact HS|exact (One_le (Bump_one HB))|exact HL|exact HU|].
  cbn[FlatLower total tl] in *; lia.
Qed.

Lemma FlatBox_shift N bounds h : FlatBox N bounds h ->
  Forall2 le (0::bounds) (bounds++[1+h*2]).
Proof.
  intro H; induction H; [repeat constructor; lia|].
  change (Forall2 le ((0::xs)++[1+h*2]) ((xs++[1+h*2])++[1+(1+h*2)*2])).
  apply Forall2_app; [exact IHFlatBox|constructor; [lia|constructor]].
Qed.

Lemma FlatLower_bounds N bounds h : FlatBox N bounds h ->
  Forall2 le (tl (FlatLower bounds h)) (FlatUpper bounds h).
Proof.
  intro H; unfold FlatLower, FlatUpper; cbn[tl].
  change (Forall2 le ((0::bounds)++[2+h*2]) (bounds++([1+h*2]++[3+h*4]))).
  rewrite app_assoc; apply Forall2_app; [eapply FlatBox_shift; exact H|constructor; [lia|constructor]].
Qed.

Lemma FlatLower_capacity N bounds h : FlatBox N bounds h ->
  2+h*2=2^(1+N) /\ total (tl (FlatLower bounds h))+(2+N)=(2+h*2)*2.
Proof.
  intro H; destruct (FlatBox_spec H) as [EL [_ EH]].
  pose proof (FlatBox_mass H) as EM; split.
  - change (2+h*2=2*2^N); rewrite <- EH; lia.
  - cbn[FlatLower tl total]; rewrite total_app; cbn[total]; lia.
Qed.

Lemma FlatSteps_main_from N lower next i a : FlatStep N lower next ->
  Bump i a lower next -> CarryEven lower i -> forall n xs,
  FlatSteps N n lower xs -> forall ys, FlatStep N xs ys ->
  exists j b, Bump j b xs ys /\ CarryEven xs j.
Proof.
  intros HS HB HC n xs H; remember lower as start in H.
  induction H; intros ws HW.
  - subst xs; pose proof (FlatStep_functional HS HW) as <-; eauto.
  - destruct (IHFlatSteps Heqstart _ H0) as [j [b [HJ Hcarry]]].
    destruct (FlatStep_route H0 HW HJ) as [k [c [HM HK]]].
    exists k,c; split; [exact HK|eapply FlatMove_carry; eauto].
    exact (proj1 (FlatStep_length H0)).
Qed.

Lemma FlatLower_budget n :
  ((11+n*2)*4+12)*(10+n*2)+(11+n*2)+2 < 2^(10+n*2).
Proof.
  induction n.
  - cbn; lia.
  - replace (10+S n*2) with (2+(10+n*2)) by lia; rewrite Nat.pow_add_r.
    change (((11+S n*2)*4+12)*(10+S n*2)+(11+S n*2)+2 < 4*2^(10+n*2)); nia.
Qed.

Corollary FlatLower_large_window n bounds h e t xs : FlatBox (9+n*2) bounds h ->
  Forall2 le (FlatLower bounds h) xs -> Forall2 le (tl xs) (FlatUpper bounds h) ->
  total xs<=total (FlatLower bounds h)+e ->
  e+t<=((11+n*2)*4+12)*(10+n*2)+(10+n*2)+2 -> exists ys,
    FlatSteps (11+n*2) t xs ys /\ Forall2 le (FlatLower bounds h) ys /\
    Forall2 le (tl ys) (FlatUpper bounds h) /\ total ys=total xs+t.
Proof.
  intros H HL HU HM HT; eapply FlatLower_window; [exact H|exact HL|exact HU|exact HM|].
  destruct (FlatLower_capacity H) as [HP _]; rewrite HP.
  change (e+t+1<=2^(10+n*2)); pose proof (FlatLower_budget n); lia.
Qed.

Lemma FlatSteps_app N n xs ys : FlatSteps N n xs ys ->
  forall m zs, FlatSteps N m ys zs -> FlatSteps N (n+m) xs zs.
Proof.
  intros H m zs H'; induction H'.
  - rewrite Nat.add_0_r; exact H.
  - replace (n+(1+n0)) with (1+(n+n0)) by lia; econstructor; eauto.
Qed.

Lemma FlatSteps_split N n xs zs : FlatSteps N n xs zs ->
  forall m, m<=n -> exists ys, FlatSteps N m xs ys /\ FlatSteps N (n-m) ys zs.
Proof.
  intros H m; revert n xs H; induction m; intros n xs H HM.
  - exists xs; split; [constructor|rewrite Nat.sub_0_r; exact H].
  - destruct n; [lia|].
    destruct (FlatSteps_uncons H eq_refl) as [first [HS HT]].
    destruct (IHm _ _ HT ltac:(lia)) as [ys [HP HQ]].
    exists ys; split; [eapply FlatSteps_cons; eassumption|exact HQ].
Qed.

Lemma FlatSteps_below N n xs ys : FlatSteps N n xs ys -> forall zs,
  Forall2 le zs xs -> exists ws, FlatSteps N n zs ws /\ Forall2 le ws ys.
Proof.
  intro H; induction H; intros ws HL.
  - exists ws; split; [constructor|exact HL].
  - destruct (IHFlatSteps _ HL) as [cut [HP HQ]].
    destruct (FlatStep_below H0 HQ) as [last [HS HB]].
    exists last; split; [econstructor; eassumption|exact HB].
Qed.

Lemma FlatSteps_unit N n xs ys : FlatSteps N n xs ys ->
  forall zs ws, FlatSteps N n zs ws -> One xs zs -> One ys ws.
Proof.
  intro H; induction H; intros ws last HT HU.
  - inversion HT; subst; exact HU.
  - destruct (FlatSteps_unsnoc HT) as [cut [HP HQ]].
    eapply FlatStep_unit; [exact H0|exact HQ|eapply IHFlatSteps; eassumption].
Qed.

Lemma le_one_before xs ys : Forall2 le xs ys -> total xs<total ys ->
  exists zs, Forall2 le xs zs /\ One zs ys.
Proof.
  intro H; induction H; cbn[total]; intro HM; [lia|].
  destruct (Nat.eq_dec x y) as [->|HD].
  - destruct (IHForall2 ltac:(lia)) as [zs [HL HU]].
    exists (y::zs); split; constructor; assumption || lia.
  - exists ((y-1)::l'); split; [constructor; [lia|exact H0]|].
    replace y with (1+(y-1)) at 2 by lia; constructor.
Qed.

(* Index by mass, not simultaneous tape time: the early member at index j
   applies the next main increment to c_(j-1) before the current one. *)
Inductive FlatAligned (N:nat) (root:list nat) : nat -> list nat -> Prop :=
| FlatAligned_main j xs : FlatSteps N j root xs -> FlatAligned N root j xs
| FlatAligned_early j xs ys ds : FlatSteps N j root xs -> FlatStep N xs ys ->
    FlatEarly N xs ys ds -> FlatAligned N root (1+j) ds.

Lemma FlatAligned_unit N C root next i a : 3<=N -> N*3+9<C ->
  FlatStep N root next -> Bump i a root next -> CarryEven root i ->
  forall j xs noise endc endn,
  FlatAligned N root j xs -> One xs noise ->
  FlatSteps N (j+C+2) root endc -> FlatSteps N C noise endn ->
  FlatAligned N root (j+C+1) endn.
Proof.
  intros HN HC HS HB HE j xs noise endc endn HA HU Hmain Hnoise.
  destruct HA as [j xs HP|j xs ys ds HP HX HD].
  - pose proof (FlatSteps_cancel HP Hmain (C+2) ltac:(lia)) as HT.
    destruct (FlatSteps_uncons (m:=1+C) HT ltac:(lia)) as [ys [HX HR]].
    destruct (FlatSteps_main_from HS HB HE HP HX) as [k [b [HK Hcarry]]].
    destruct (One_bump HU) as [l [c HL]].
    destruct (@Flat_absorbs N C xs ys noise endc endn k b l c ltac:(lia) ltac:(lia)
      HX HR Hnoise HK HL Hcarry) as [p [q [Hpre [Hpq [Hlast Hend]]]]].
    pose proof (FlatSteps_app HP Hpre) as Hprefix.
    replace (j+C+1) with (1+(j+C)) by lia.
    destruct Hend as [->|Hearly].
    + apply FlatAligned_main; econstructor; eassumption.
    + eapply FlatAligned_early; eassumption.
  - destruct (FlatSteps_split Hmain (m:=j+C+2) ltac:(lia)) as [cut [Hprefix _]].
    assert (Hys : FlatSteps N (1+j) root ys) by (econstructor; eassumption).
    pose proof (FlatSteps_cancel Hys Hprefix (1+C) ltac:(lia)) as HR.
    destruct (FlatSteps_main_from HS HB HE HP HX) as [k [b [HK Hcarry]]].
    destruct (One_bump HU) as [l [c HL]].
    pose proof (@FlatEarly_absorbs N C xs ys ds noise cut endn k b l c
      HN HC HD HR Hnoise HK HL Hcarry) as E; subst endn.
    replace (1+j+C+1) with (j+C+2) by lia; constructor; exact Hprefix.
Qed.

Theorem Flat_many_absorbs N C root next i a : 3<=N -> N*3+9<C ->
  FlatStep N root next -> Bump i a root next -> CarryEven root i ->
  forall k xs endc endn,
  Forall2 le root xs -> total xs=total root+k ->
  FlatSteps N (C*k+k+1) root endc -> FlatSteps N (C*k) xs endn ->
  FlatAligned N root (C*k+k) endn.
Proof.
  intros HN HC HS HB HE k; induction k; intros xs endc endn HL HM Hmain Hnoise.
  - rewrite Nat.mul_0_r in *; cbn[Nat.add] in *.
    assert (E : root=xs) by (apply total_eq; [exact HL|lia]); subst xs.
    inversion Hnoise; subst; constructor; constructor.
  - destruct (le_one_before HL ltac:(lia)) as [mid [Hmid HU]].
    pose proof (One_mass HU) as HU_mass.
    destruct (FlatSteps_split Hnoise (m:=C*k) ltac:(nia)) as [cut [Hcut Htail]].
    destruct (FlatSteps_below Hcut (One_le HU)) as [midcut [Hmidcut _]].
    destruct (FlatSteps_split Hmain (m:=C*k+k+1) ltac:(nia)) as [maincut [Hmaincut _]].
    pose proof (IHk _ _ _ Hmid ltac:(lia) Hmaincut Hmidcut) as HA.
    pose proof (FlatSteps_unit Hmidcut Hcut HU) as HCunit.
    replace (C*S k-C*k) with C in Htail by nia.
    replace (C*S k+S k+1) with ((C*k+k)+C+2) in Hmain by nia.
    replace (C*S k+S k) with ((C*k+k)+C+1) by nia.
    eapply FlatAligned_unit; eassumption.
Qed.

Lemma FlatEarly_complement N xs ys ds zs : FlatEarly N xs ys ds ->
  FlatStep N ys zs -> One ds zs.
Proof.
  intros HE HS; destruct HE as [xs ys ws ds i a j b HX HY HI HJ HD].
  pose proof (FlatStep_functional HY HS) as E; subst ws.
  assert (Hne : i<>j).
  { intro E; subst j; destruct (Bump_nth HI) as [HA HB].
    destruct (Bump_nth HJ) as [HC _]; destruct (Bump_nth HD) as [HE _]; lia. }
  destruct (Bump_swap HI HJ Hne) as [es [HP HQ]].
  pose proof (Bump_functional HP HD) as E; subst es.
  exact (Bump_one HQ).
Qed.

Lemma FlatEarly_functional N xs ys ds es : FlatEarly N xs ys ds ->
  FlatEarly N xs ys es -> ds=es.
Proof.
  intros HD HE; destruct HD as [xs ys zs ds i a j b HX HY HI HJ HB].
  destruct HE as [xs ys ws es k c l d HX' HY' HK HL HC].
  pose proof (FlatStep_functional HY HY') as E; subst ws.
  destruct (Bump_position HJ HL) as [-> ->]. eapply Bump_functional; eassumption.
Qed.

Lemma FlatAligned_continue N root j xs : 0<N -> FlatAligned N root j xs ->
  forall t endc, FlatSteps N (j+t+1) root endc -> exists ys,
  FlatSteps N t xs ys /\ FlatAligned N root (j+t) ys.
Proof.
  intros HN HA t endc HM; destruct HA as [j xs HP|j xs ys ds HP HX HE].
  - pose proof (FlatSteps_cancel HP HM (t+1) ltac:(lia)) as HR.
    destruct (FlatSteps_split HR (m:=t) ltac:(lia)) as [zs [HZ _]].
    exists zs; split; [exact HZ|constructor; eapply FlatSteps_app; eassumption].
  - assert (Hys : FlatSteps N (1+j) root ys) by (econstructor; eassumption).
    pose proof (FlatSteps_cancel Hys HM (1+t) ltac:(lia)) as HR.
    destruct (FlatSteps_uncons HR eq_refl) as [zs [HY HT]].
    destruct (FlatSteps_below HT (One_le (FlatEarly_complement HE HY))) as [out [HO _]].
    destruct (FlatEarly_steps HN HE HR HO) as [p [q [Hp [Hq [_ HD]]]]].
    exists out; split; [exact HO|].
    replace (1+j+t) with (1+(j+t)) by lia; eapply FlatAligned_early; [|exact Hq|exact HD].
    eapply FlatSteps_app; eassumption.
Qed.

(* Finite row certificates for the first all-false exit and for its lower
   anchor prefix. The rows are symbolic proof objects, never evaluated. *)
Definition FlatRow sink i := Cycles [0;match i with 0=>sink | S k=>S k end] (2^i).
Fixpoint FlatRowsBody sink n := match n with
  | 0 => [] | S n => FlatRowsBody sink n++[FlatRow sink n] end.
Definition FlatExitRows N := Cycles [N] (2^N)::FlatRowsBody (N+1) N.

Lemma FlatRowsBody_length sink n : length (FlatRowsBody sink n)=n.
Proof. induction n; cbn[FlatRowsBody]; rewrite ?length_app, ?IHn; cbn; lia. Qed.

Lemma FlatRow_length sink i : length (FlatRow sink i)=2^i*2.
Proof. unfold FlatRow; rewrite Cycles_length; reflexivity. Qed.

Lemma FlatRow_count sink i v : count_occ Nat.eq_dec (FlatRow sink i) v=
  2^i*(mark 0 v+mark (match i with 0=>sink | S k=>S k end) v).
Proof. unfold FlatRow; rewrite Cycles_count, !count_cons; cbn[count_occ]; lia. Qed.

Lemma FlatRowsBody_at sink n : forall i, i<n -> nth i (FlatRowsBody sink n) []=FlatRow sink i.
Proof.
  induction n; intros i HI; [lia|].
  cbn[FlatRowsBody]; destruct (Nat.eq_dec i n) as [->|HD].
  - rewrite app_nth2, FlatRowsBody_length by (rewrite FlatRowsBody_length; lia).
    rewrite Nat.sub_diag; reflexivity.
  - rewrite app_nth1 by (rewrite FlatRowsBody_length; lia); apply IHn; lia.
Qed.

Lemma FlatRowsBody_balance sink n v :
  incoming (FlatRowsBody sink (1+n)) v+2^(1+n)*mark (1+n) v =
  weighted (FlatRowsBody sink (1+n)) 1 v+(2^(1+n)-1)*mark 0 v+mark sink v.
Proof.
  induction n.
  - change (count_occ Nat.eq_dec ([0;sink]++[]) v+2*mark 1 v=
      2*mark 1 v+0+1*mark 0 v+mark sink v).
    rewrite app_nil_r, !count_cons; cbn[count_occ]; lia.
  - change (incoming (FlatRowsBody sink (1+n)++[FlatRow sink (1+n)]) v+
      (2*2^(1+n))*mark (2+n) v =
      weighted (FlatRowsBody sink (1+n)++[FlatRow sink (1+n)]) 1 v+
      (2*2^(1+n)-1)*mark 0 v+mark sink v).
    unfold incoming in *; rewrite concat_app, count_occ_app, weighted_app, FlatRowsBody_length.
    cbn[concat weighted]; rewrite app_nil_r, FlatRow_length, FlatRow_count.
    change (match 1+n with 0=>sink | S k=>S k end) with (1+n).
    replace (1+n+1) with (2+n) by lia.
    pose proof (Nat.pow_nonzero 2 (1+n) ltac:(lia)); nia.
Qed.

Lemma FlatExitRows_length N : length (FlatExitRows N)=1+N.
Proof. unfold FlatExitRows; cbn[length]; rewrite FlatRowsBody_length; reflexivity. Qed.

Lemma FlatExitRows_balance N : 0<N -> Balance (FlatExitRows N) 0 (N+1).
Proof.
  intros HN v; destruct N as [|n]; [lia|].
  pose proof (FlatRowsBody_balance (S n+1) n v) as H.
  unfold FlatExitRows, Balance, incoming; cbn[concat].
  rewrite count_occ_app, Cycles_count, count_cons; cbn[count_occ].
  rewrite <- weighted_outgoing; cbn[weighted]; rewrite Cycles_length; cbn[length].
  change (incoming (FlatRowsBody (S n+1) (1+n)) v) with
    (count_occ Nat.eq_dec (concat (FlatRowsBody (S n+1) (S n))) v) in H.
  pose proof (Nat.pow_nonzero 2 (1+n) ltac:(lia)); cbn[Nat.add] in *; nia.
Qed.

Definition FlatExitRank N i := if i =? 0 then N+1 else if i =? N+1 then 0 else i.

Lemma FlatExitRank_root N : FlatExitRank N 0=N+1.
Proof. reflexivity. Qed.

Lemma FlatExitRank_sink N : FlatExitRank N (N+1)=0.
Proof.
  unfold FlatExitRank; rewrite Nat.eqb_refl.
  destruct (N+1 =? 0) eqn:E; [apply Nat.eqb_eq in E; lia|reflexivity].
Qed.

Lemma FlatExitRank_body N i : 0<i -> i<=N -> FlatExitRank N i=i.
Proof.
  intros HI HN; unfold FlatExitRank.
  destruct (i =? 0) eqn:E, (i =? N+1) eqn:F;
    try (apply Nat.eqb_eq in E); try (apply Nat.eqb_eq in F); lia.
Qed.

Lemma FlatExitRows_forest N : 0<N -> LastForest (FlatExitRank N) (FlatExitRows N).
Proof.
  intros HN i HE.
  assert (HI : i<1+N).
  { destruct (Nat.lt_ge_cases i (length (FlatExitRows N))) as [HL|HL].
    - rewrite FlatExitRows_length in HL; exact HL.
    - rewrite nth_overflow in HE by lia; contradiction. }
  destruct i as [|i].
  - change (FlatExitRank N (last (Cycles [N] (2^N)) 0)<FlatExitRank N 0).
    rewrite Cycles_last by (discriminate || (apply Nat.pow_nonzero; lia)).
    cbn[last]; rewrite FlatExitRank_root, FlatExitRank_body by lia; lia.
  - change (FlatExitRank N (last (nth i (FlatRowsBody (N+1) N) []) 0)<FlatExitRank N (1+i)).
    rewrite FlatRowsBody_at by lia; unfold FlatRow.
    rewrite Cycles_last by (discriminate || (apply Nat.pow_nonzero; lia)).
    cbn[last]; rewrite (@FlatExitRank_body N (1+i)) by lia.
    destruct i; [rewrite FlatExitRank_sink; lia|rewrite FlatExitRank_body by lia; lia].
Qed.

Lemma FlatRowsBody_budget sink n : length (concat (FlatRowsBody sink n))=2^n*2-2.
Proof.
  induction n; [reflexivity|].
  cbn[FlatRowsBody]; rewrite concat_app, length_app; cbn[concat].
  rewrite app_nil_r, IHn, FlatRow_length.
  pose proof (Nat.pow_nonzero 2 n ltac:(lia)); cbn[Nat.pow]; lia.
Qed.

Lemma FlatExitRows_budget N : length (concat (FlatExitRows N))=2^N*3-2.
Proof.
  unfold FlatExitRows; cbn[concat]; rewrite length_app, Cycles_length, FlatRowsBody_budget.
  cbn[length]; pose proof (Nat.pow_nonzero 2 N ltac:(lia)); lia.
Qed.

Definition FlatExitMove N i a j := FlatMove N i a j \/ (i=1 /\ a=1 /\ j=N+1).

Lemma Indexed_Cycles R word : (forall a, Indexed R (a*length word) word) ->
  forall n, Indexed R 0 (Cycles word n).
Proof.
  intros HW n; rewrite <- (app_nil_r (Cycles word n)).
  change (Indexed R (0*length word) (Cycles word n++[])).
  apply Indexed_cycles; [exact HW|intro a; exact I].
Qed.

Lemma FlatCycles_rules N i q : 0<i -> Indexed (FlatMove N (1+i)) 0 (Cycles [0;i] q).
Proof.
  intro HI; apply Indexed_Cycles; intro a; cbn[length Indexed].
  split; [apply FlatMove_back; [lia|apply odd_0]|split; [|exact I]].
  replace i with ((1+i)-1) at 2 by lia; apply FlatMove_forward; [lia|apply odd_1].
Qed.

Lemma FlatRoot_rules N q : Indexed (FlatMove N 0) 0 (Cycles [N] q).
Proof. apply Indexed_Cycles; intro a; cbn[Indexed]; split; [constructor|exact I]. Qed.

Lemma FlatExitRows_rules N : RowRules (FlatExitMove N) (FlatExitRows N) (repeat 0 (1+N)).
Proof.
  rewrite <- FlatExitRows_length; apply RowRules_initial; intro i.
  destruct (Nat.lt_ge_cases i (length (FlatExitRows N))) as [HI|HI];
    [rewrite FlatExitRows_length in HI|rewrite nth_overflow by lia; exact I].
  destruct i as [|i].
  - change (Indexed (FlatExitMove N 0) 0 (Cycles [N] (2^N))).
    eapply Indexed_mono; [intros; left; eassumption|apply FlatRoot_rules].
  - change (Indexed (FlatExitMove N (1+i)) 0 (nth i (FlatRowsBody (N+1) N) [])).
    rewrite FlatRowsBody_at by lia; destruct i as [|i].
    + change (FlatExitMove N 1 0 0 /\ FlatExitMove N 1 1 (N+1) /\ True).
      split; [left; apply FlatMove_back; [lia|reflexivity]|split; [right; auto|exact I]].
    + unfold FlatRow; eapply Indexed_mono; [intros; left; eassumption|apply FlatCycles_rules; lia].
Qed.

Lemma FlatStep_available N xs : 0<N -> length xs=1+N -> nth 1 xs 0<=1 ->
  exists ys, FlatStep N xs ys.
Proof.
  intros HN EL HB; destruct N as [|N]; [lia|].
  destruct xs as [|u [|a xs]]; cbn[length] in EL; try lia.
  cbn[nth] in HB.
  destruct (@Half_front_total false (repeat false N) a xs u 1
    ltac:(rewrite repeat_length; lia) (Split_false_small HB)) as [ys [v HT]].
  exists (v::ys); constructor; exact HT.
Qed.

Definition FlatRowsSafe N original sink := forall rows xs i,
  RowRules (FlatExitMove N) rows xs -> VisitBudget original rows xs ->
  Balance rows i sink -> i<>N+1 -> nth 1 xs 0<=1.

Lemma FlatRows_sink N original rows xs : length original=1+N ->
  RowRules (FlatExitMove N) rows xs -> VisitBudget original rows xs -> nth (N+1) rows []=[].
Proof. intros EL [ER _] [EX _]; apply nth_overflow; lia. Qed.

Lemma FlatExitRows_safe N : 0<N -> FlatRowsSafe N (FlatExitRows N) (N+1).
Proof.
  intros HN rows xs i HR HV HB HI.
  pose proof (FlatRows_sink (FlatExitRows_length N) HR HV) as HE.
  specialize (HB (N+1)); unfold outgoing in HB; rewrite HE, mark_self, mark_other in HB by assumption.
  cbn[length] in HB.
  destruct (incoming_witness rows (N+1) ltac:(lia)) as [j [HJ HJ']].
  destruct HR as [EL HR]; destruct HV as [EX HV].
  destruct (Indexed_in (HR j) HJ') as [a [HA [HD|[-> [-> _]]]]]; [|assumption].
  pose proof (FlatMove_bound HD ltac:(rewrite FlatExitRows_length in EX; lia)); lia.
Qed.

Lemma stack_flat N original sink : 0<N -> length original=1+N -> FlatRowsSafe N original sink ->
  forall i rows j rows' n, StackWalk i rows j rows' n -> forall xs next a,
  RowRules (FlatExitMove N) rows xs -> VisitBudget original rows xs -> Balance rows i sink ->
  FlatStep N xs next -> Bump i a xs next -> exists ys,
    FlatSteps N n xs ys /\ VisitBudget original rows' ys.
Proof.
  intros HN EL HS i rows j rows' n HW; induction HW as [i rows|i j k rows rows' rows'' n HP HW IH];
    intros xs next a HR HV HF HT HB.
  - exists xs; split; [constructor|exact HV].
  - destruct (RowRules_pop HR HP HB) as [HD HR']; pose proof (VisitBudget_pop HV HP HB) as HV'.
    pose proof (Pop_balance HP HF) as HF'.
    destruct (Nat.eq_dec j (N+1)) as [HJ|HJ].
    + pose proof (FlatRows_sink EL HR' HV') as HE; rewrite <- HJ in HE.
      destruct (StackWalk_stuck HW HE) as [EJ [EN ER]]; subst.
      exists next; split; [eapply FlatSteps_cons; [exact HT|constructor]|exact HV'].
    + destruct (@FlatStep_available N next HN (proj2 (FlatStep_length HT))
        (HS _ _ _ HR' HV' HF' HJ)) as [next' HT'].
      destruct (FlatStep_route HT HT' HB) as [j' [a' [HD' HB']]].
      destruct HD as [HD|[_ [_ HE]]]; [|contradiction].
      pose proof (FlatMove_functional HD HD') as ->.
      destruct (IH _ _ _ HR' HV' HF' HT' HB') as [ys [HX HY]].
      exists ys; split; [eapply FlatSteps_cons; eassumption|exact HY].
Qed.

Theorem Flat_certificate N original sink rank : 0<N -> length original=1+N ->
  RowRules (FlatExitMove N) original (repeat 0 (1+N)) -> Balance original 0 sink ->
  LastForestExcept rank original sink -> FlatRowsSafe N original sink ->
  FlatSteps N (length (concat original)) (0::repeat 0 N) (map (@length nat) original).
Proof.
  intros HN EL HR HB HF HS; destruct (stack_certificate_except HB HF) as [rows [HW HE]].
  pose proof (VisitBudget_initial original) as HV; rewrite EL in HV.
  destruct (@stack_flat N original sink HN EL HS 0 original sink rows (length (concat original)) HW
    (0::repeat 0 N) (1::repeat 0 N) 0 HR HV HB (FlatStep_zero HN) (Bump_here 0 _)) as [ys [HT HY]].
  rewrite (VisitBudget_done HY HE) in HT; exact HT.
Qed.

Theorem Flat_zero_exit N : 0<N ->
  FlatSteps N (2^N*3-2) (0::repeat 0 N) (map (@length nat) (FlatExitRows N)).
Proof.
  intro HN; rewrite <- FlatExitRows_budget.
  eapply Flat_certificate; [exact HN|apply FlatExitRows_length|apply FlatExitRows_rules|
    apply FlatExitRows_balance; exact HN| |apply FlatExitRows_safe; exact HN].
  intros i _; apply FlatExitRows_forest; exact HN.
Qed.

Definition LowRow i := Cycles [0;1+i] (2^i-1)++[0].
Fixpoint LowRows n := match n with 0=>[] | S n=>LowRows n++[LowRow n] end.
Definition FlatLowerRows n := Cycles [3+n] (2^(2+n))::[]::
  (LowRows (1+n)++[Cycles [0;2+n] (2^(1+n))]).

Lemma LowRows_length n : length (LowRows n)=n.
Proof. induction n; cbn[LowRows]; rewrite ?length_app, ?IHn; cbn; lia. Qed.

Lemma LowRow_length i : length (LowRow i)=2^(1+i)-1.
Proof.
  unfold LowRow; rewrite length_app, Cycles_length; cbn[length Nat.add Nat.pow].
  pose proof (Nat.pow_nonzero 2 i ltac:(lia)); lia.
Qed.

Lemma LowRow_count i v : count_occ Nat.eq_dec (LowRow i) v=
  2^i*mark 0 v+(2^i-1)*mark (1+i) v.
Proof.
  unfold LowRow; rewrite count_occ_app, Cycles_count, !count_cons; cbn[count_occ].
  pose proof (Nat.pow_nonzero 2 i ltac:(lia)); nia.
Qed.

Lemma LowRows_at n : forall i, i<n -> nth i (LowRows n) []=LowRow i.
Proof.
  induction n; intros i HI; [lia|].
  cbn[LowRows]; destruct (Nat.eq_dec i n) as [->|HD].
  - rewrite app_nth2, LowRows_length by (rewrite LowRows_length; lia).
    rewrite Nat.sub_diag; reflexivity.
  - rewrite app_nth1 by (rewrite LowRows_length; lia); apply IHn; lia.
Qed.

Lemma LowRows_balance n v : incoming (LowRows n) v+(2^n-1)*mark (1+n) v=
  weighted (LowRows n) 2 v+(2^n-1)*mark 0 v.
Proof.
  induction n; [reflexivity|].
  cbn[LowRows]; unfold incoming in *.
  rewrite concat_app, count_occ_app, weighted_app, LowRows_length.
  cbn[concat weighted]; rewrite app_nil_r, LowRow_count, LowRow_length.
  replace (n+2) with (1+S n) by lia.
  pose proof (Nat.pow_nonzero 2 n ltac:(lia)).
  cbn[Nat.add Nat.pow] in *; nia.
Qed.

Lemma LowRows_budget n : length (concat (LowRows n))+n+2=2^(1+n).
Proof.
  induction n; [reflexivity|].
  cbn[LowRows]; rewrite concat_app, length_app; cbn[concat].
  rewrite app_nil_r, LowRow_length.
  pose proof (Nat.pow_nonzero 2 (1+n) ltac:(lia));
    change (length (concat (LowRows n))+(2^(1+n)-1)+S n+2=2*2^(1+n)); lia.
Qed.

Lemma FlatLowerRows_length n : length (FlatLowerRows n)=1+(3+n).
Proof. unfold FlatLowerRows; cbn[length]; rewrite length_app, LowRows_length; cbn; lia. Qed.

Lemma FlatLowerRows_balance n : Balance (FlatLowerRows n) 0 (2+n).
Proof.
  intro v; pose proof (LowRows_balance (1+n) v) as H.
  unfold FlatLowerRows, Balance, incoming; cbn[concat].
  rewrite concat_app, !count_occ_app; cbn[concat]; rewrite app_nil_r.
  rewrite !Cycles_count, !count_cons; cbn[count_occ].
  rewrite <- weighted_outgoing; cbn[weighted]; rewrite weighted_app, LowRows_length.
  cbn[weighted]; rewrite !Cycles_length; cbn[length].
  replace (1+n+2) with (3+n) by lia.
  unfold incoming in H; cbn[Nat.add Nat.pow] in H |- *.
  replace (n+2) with (S (S n)) by lia.
  pose proof (Nat.pow_nonzero 2 n ltac:(lia)); nia.
Qed.

Definition LowerRank n i := if i =? 2+n then 0 else
  if i =? 0 then 2 else if i =? 3+n then 1 else 3.

Lemma LowerRank_root n : LowerRank n 0=2.
Proof. reflexivity. Qed.

Lemma LowerRank_sink n : LowerRank n (2+n)=0.
Proof. unfold LowerRank; rewrite Nat.eqb_refl; reflexivity. Qed.

Lemma LowerRank_last n : LowerRank n (3+n)=1.
Proof.
  unfold LowerRank; rewrite Nat.eqb_refl.
  destruct (3+n =? 2+n) eqn:E; [apply Nat.eqb_eq in E; lia|reflexivity].
Qed.

Lemma LowerRank_middle n i : 0<i -> i<2+n -> LowerRank n i=3.
Proof.
  intros HI HL; unfold LowerRank.
  destruct (i =? 2+n) eqn:E, (i =? 0) eqn:F, (i =? 3+n) eqn:G;
    try (apply Nat.eqb_eq in E); try (apply Nat.eqb_eq in F); try (apply Nat.eqb_eq in G); lia.
Qed.

Lemma FlatLowerRows_forest n : LastForestExcept (LowerRank n) (FlatLowerRows n) (2+n).
Proof.
  intros i HS HE.
  assert (HI : i<1+(3+n)).
  { destruct (Nat.lt_ge_cases i (length (FlatLowerRows n))) as [HL|HL].
    - rewrite FlatLowerRows_length in HL; exact HL.
    - rewrite nth_overflow in HE by lia; contradiction. }
  destruct i as [|[|i]].
  - change (LowerRank n (last (Cycles [3+n] (2^(2+n))) 0)<LowerRank n 0).
    rewrite Cycles_last by (discriminate || (apply Nat.pow_nonzero; lia)).
    cbn[last]; rewrite LowerRank_root, LowerRank_last; lia.
  - change (([]:list nat)<>[]) in HE; contradiction.
  - change (LowerRank n (last (nth i (LowRows (1+n)++[Cycles [0;2+n] (2^(1+n))]) []) 0)
      <LowerRank n (2+i)).
    destruct (Nat.eq_dec i (1+n)) as [->|HD].
    + rewrite app_nth2, LowRows_length by (rewrite LowRows_length; lia).
      rewrite Nat.sub_diag; cbn[nth].
      rewrite Cycles_last by (discriminate || (apply Nat.pow_nonzero; lia)).
      cbn[last]; replace (2+(1+n)) with (3+n) by lia.
      rewrite LowerRank_sink, LowerRank_last; lia.
    + rewrite app_nth1 by (rewrite LowRows_length; lia); rewrite LowRows_at by lia.
      unfold LowRow; rewrite last_suffix by discriminate; cbn[last].
      rewrite LowerRank_root, LowerRank_middle by lia; lia.
Qed.

Lemma FlatLowerRows_budget n : length (concat (FlatLowerRows n))=2^(2+n)*3-(3+n).
Proof.
  pose proof (LowRows_budget (1+n)) as H.
  unfold FlatLowerRows; cbn[concat]; rewrite concat_app, !length_app.
  cbn[concat]; rewrite app_nil_r, !Cycles_length; cbn[length].
  cbn[Nat.add Nat.pow] in H |- *; lia.
Qed.

Lemma LowRows_rules N n : forall i, Indexed (FlatExitMove N (2+i)) 0 (nth i (LowRows n) []).
Proof.
  intros i; destruct (Nat.lt_ge_cases i n) as [HI|HI].
  - rewrite LowRows_at by assumption; unfold LowRow.
    change (Indexed (FlatExitMove N (2+i)) (0*length [0;1+i]) (Cycles [0;1+i] (2^i-1)++[0])).
    apply Indexed_cycles; intro a; cbn[Indexed length]; repeat split; left.
    + apply FlatMove_back; [lia|apply odd_0].
    + replace (1+i) with ((2+i)-1) by lia; apply FlatMove_forward; [lia|apply odd_1].
    + apply FlatMove_back; [lia|apply odd_0].
  - rewrite nth_overflow by (rewrite LowRows_length; lia); exact I.
Qed.

Lemma FlatLowerRows_rules n :
  RowRules (FlatExitMove (3+n)) (FlatLowerRows n) (repeat 0 (1+(3+n))).
Proof.
  rewrite <- FlatLowerRows_length; apply RowRules_initial; intro i.
  destruct i as [|[|i]].
  - change (Indexed (FlatExitMove (3+n) 0) 0 (Cycles [3+n] (2^(2+n)))).
    eapply Indexed_mono; [intros; left; eassumption|apply FlatRoot_rules].
  - exact I.
  - change (Indexed (FlatExitMove (3+n) (2+i)) 0
      (nth i (LowRows (1+n)++[Cycles [0;2+n] (2^(1+n))]) [])).
    destruct (Nat.lt_ge_cases i (1+n)) as [HI|HI].
    + rewrite app_nth1 by (rewrite LowRows_length; lia); apply LowRows_rules.
    + rewrite app_nth2, LowRows_length by (rewrite LowRows_length; lia).
      destruct (Nat.eq_dec i (1+n)) as [->|HD].
      * rewrite Nat.sub_diag; cbn[nth].
        replace (2+(1+n)) with (1+(2+n)) by lia.
        eapply Indexed_mono; [intros; left; eassumption|apply FlatCycles_rules; lia].
      * assert (i-(1+n)<>0) by lia; destruct (i-(1+n)); [contradiction|destruct n0; exact I].
Qed.

Lemma FlatLowerRows_safe n : FlatRowsSafe (3+n) (FlatLowerRows n) (2+n).
Proof.
  intros rows xs i HR HV HB HI; pose proof (VisitBudget_bound 1 HV) as H.
  change (nth 1 xs 0<=0) in H; lia.
Qed.

Theorem Flat_zero_lower n : FlatSteps (3+n) (2^(2+n)*3-(3+n)) (0::repeat 0 (3+n))
  (map (@length nat) (FlatLowerRows n)).
Proof.
  rewrite <- FlatLowerRows_budget; eapply Flat_certificate;
    [lia|apply FlatLowerRows_length|apply FlatLowerRows_rules|apply FlatLowerRows_balance|
     apply FlatLowerRows_forest|apply FlatLowerRows_safe].
Qed.

Lemma FlatStep_front N xs ys : FlatStep N xs ys -> nth 1 xs 0<=1.
Proof.
  intro H; destruct H as [xs u ys v H].
  inversion H as [body root q qs r HS]; subst; destruct N; cbn[repeat] in HS.
  - inversion HS.
  - inversion HS; subst; cbn[nth].
    match goal with H : Split false _ 0 _ |- _ => inversion H; subst; lia end.
Qed.

Lemma Bump_front_overflow i a xs u tail : Bump i a xs (u::2::tail) -> nth 1 xs 0<=1 ->
  xs=u::1::tail /\ i=1 /\ a=1.
Proof.
  intros H HF; inversion H; subst; cbn[nth] in HF; [lia|].
  match goal with HB : Bump _ _ _ (2::tail) |- _ => inversion HB; subst end.
  - repeat split; reflexivity || lia.
  - cbn[nth] in HF; lia.
Qed.

Lemma Bump_second_back a xs u b tail : Bump 2 a xs (u::b::4::tail) -> xs=u::b::3::tail.
Proof.
  intro H; inversion H; subst.
  match goal with H : Bump 1 _ _ _ |- _ => inversion H; subst end.
  match goal with H : Bump 0 _ _ _ |- _ => inversion H; subst end.
  f_equal; f_equal; f_equal; lia.
Qed.

Lemma FlatMove_to_first N i a : 1<N -> FlatMove N i a 1 -> i=2.
Proof. intros HN H; inversion H; subst; lia. Qed.

Lemma Flat_last_two N root next k c t u tail : 1<N ->
  FlatStep N root next -> Bump k c root next -> CarryEven root k ->
  FlatSteps N (2+t) root (u::2::4::tail) ->
  FlatSteps N t root (u::1::3::tail) /\
  FlatStep N (u::1::3::tail) (u::1::4::tail) /\
  FlatStep N (u::1::4::tail) (u::2::4::tail).
Proof.
  intros HN HS HK HC H; destruct (FlatSteps_unsnoc H) as [q [HP HQ]].
  destruct (FlatSteps_unsnoc HP) as [p [HR HT]].
  destruct (FlatSteps_main_from HS HK HC HP HQ) as [j [b [HB _]]].
  destruct (Bump_front_overflow HB (FlatStep_front HQ)) as [-> [-> ->]].
  destruct (FlatSteps_main_from HS HK HC HR HT) as [i [a [HI _]]].
  destruct (FlatStep_route HT HQ HI) as [j [b [HM HJ]]].
  destruct (Bump_position HB HJ) as [<- _].
  pose proof (FlatMove_to_first HN HM) as ->.
  pose proof (Bump_second_back HI) as ->; auto.
Qed.

Lemma Flat_last_early N u tail :
  FlatStep N (u::1::3::tail) (u::1::4::tail) ->
  FlatStep N (u::1::4::tail) (u::2::4::tail) ->
  FlatEarly N (u::1::3::tail) (u::1::4::tail) (u::2::3::tail).
Proof.
  intros HP HQ; eapply FlatEarly_make; [exact HP|exact HQ| | |].
  - apply Bump_later, Bump_later, Bump_here.
  - apply Bump_later, Bump_here.
  - apply Bump_later, Bump_here.
Qed.

Lemma FlatAligned_final N root next k c t u tail xs : 1<N ->
  FlatStep N root next -> Bump k c root next -> CarryEven root k ->
  FlatSteps N (2+t) root (u::2::4::tail) -> FlatAligned N root (1+t) xs ->
  (xs=u::1::4::tail /\ FlatStep N xs (u::2::4::tail)) \/ xs=u::2::3::tail.
Proof.
  intros HN HS HB HC HT HA.
  destruct (Flat_last_two HN HS HB HC HT) as [HP [HQ HE]].
  pose proof (Flat_last_early HQ HE) as HD.
  inversion HA as [j ys Hrun|j p q ds Hrun Hstep Hrel]; subst.
  - assert (HX : xs=u::1::4::tail).
    { eapply FlatSteps_functional; [exact Hrun|econstructor; eassumption]. }
    subst xs; auto.
  - pose proof (FlatSteps_functional HP Hrun) as E; subst p.
    pose proof (FlatStep_functional HQ Hstep) as E; subst q.
    right; eapply FlatEarly_functional; [exact Hrel|exact HD].
Qed.

Lemma FlatEarly_zero n : FlatEarly (1+n) (0::repeat 0 (1+n)) (1::repeat 0 (1+n))
  (0::(repeat 0 n++[1])).
Proof.
  assert (HS : FlatStep (1+n) (1::repeat 0 (1+n)) (1::(repeat 0 n++[1]))).
  { constructor. apply (Half_make 1 1 (qs:=repeat 0 n) (r:=0)).
    pose proof (Scatter_zeros (repeat false (1+n))) as H.
    rewrite repeat_length in H; exact H. }
  eapply FlatEarly_make; [apply FlatStep_zero; lia|exact HS|apply Bump_here| |].
  all: apply Bump_later; rewrite <- zeros_snoc;
    pose proof (Bump_last (repeat 0 n) 0) as H; rewrite repeat_length in H; exact H.
Qed.

Lemma FlatEarly_final_run N root next ds i a t u tail : 1<N ->
  FlatStep N root next -> Bump i a root next -> CarryEven root i ->
  FlatEarly N root next ds -> FlatSteps N (2+t) root (u::2::4::tail) ->
  FlatSteps N t ds (u::2::3::tail).
Proof.
  intros HN HS HB HC HE HF.
  destruct (FlatSteps_uncons HF eq_refl) as [q [HQ HT]].
  pose proof (FlatStep_functional HS HQ) as E; subst q.
  destruct (FlatSteps_uncons HT eq_refl) as [z [HZ HR]].
  destruct (FlatSteps_below HR (One_le (FlatEarly_complement HE HZ))) as [d [HD _]].
  destruct (FlatEarly_steps (N:=N) ltac:(lia) HE HT HD) as [p [q [HP [Hq [Hlast Hrel]]]]].
  destruct (Flat_last_two HN HS HB HC HF) as [HP' [Hq' Hlast']].
  pose proof (FlatSteps_functional HP HP') as E; subst p.
  pose proof (FlatStep_functional Hq Hq') as E; subst q.
  pose proof (FlatEarly_functional Hrel (Flat_last_early Hq' Hlast')) as E; subst d; exact HD.
Qed.

(* Stable bodies of a zero-injection half-step. Their complete visitation
   prefixes can be certified without tracing every binary carry. *)
Inductive FlatAnchor : nat -> list nat -> nat -> Prop :=
| FlatAnchor_base : FlatAnchor 1 [1] 1
| FlatAnchor_even N xs h : FlatAnchor N xs h -> FlatAnchor (1+N) (xs++[h*2]) (h*2)
| FlatAnchor_odd N xs h : FlatAnchor N xs h -> FlatAnchor (1+N) (xs++[1+h*2]) (1+h*2).

Definition AnchorRow i h b := Cycles [0;i] h++repeat 0 b.
Definition AnchorRowsSpec N xs h rows :=
  length rows=N /\ map (@length nat) rows=xs /\
  (forall v, incoming rows v+h*mark N v=weighted rows 1 v+h*mark 0 v) /\
  (forall M i, i<N -> Indexed (FlatMove M (1+i)) 0 (nth i rows [])) /\
  (forall i, i<N -> last (nth i rows []) 0<1+i) /\
  nth 0 rows []=[0].

Lemma AnchorRow_length i h b : length (AnchorRow i h b)=h*2+b.
Proof. unfold AnchorRow; rewrite length_app, Cycles_length, repeat_length; reflexivity. Qed.

Lemma AnchorRow_count i h b v : count_occ Nat.eq_dec (AnchorRow i h b) v=
  h*(mark 0 v+mark i v)+b*mark 0 v.
Proof.
  assert (E : count_occ Nat.eq_dec (repeat 0 b) v=b*mark 0 v).
  { induction b; [reflexivity|change (count_occ Nat.eq_dec (0::repeat 0 b) v=S b*mark 0 v)].
    rewrite count_cons, IHb; lia. }
  unfold AnchorRow; rewrite count_occ_app, Cycles_count, E, !count_cons; cbn[count_occ]; lia.
Qed.

Lemma AnchorRow_rules M i h b : 0<i -> b<=1 ->
  Indexed (FlatMove M (1+i)) 0 (AnchorRow i h b).
Proof.
  intros HI HB; unfold AnchorRow; change (Indexed (FlatMove M (1+i)) (0*length [0;i])
    (Cycles [0;i] h++repeat 0 b)).
  apply Indexed_cycles.
  - intro a; cbn[Indexed length]; split; [apply FlatMove_back; [lia|apply odd_0]|].
    split; [|exact I]; replace i with (1+i-1) at 2 by lia.
    apply FlatMove_forward; [lia|apply odd_1].
  - intro a; destruct b as [|[|b]]; try lia; cbn[repeat Indexed length]; [exact I|].
    split; [apply FlatMove_back; [lia|apply odd_0]|exact I].
Qed.

Lemma AnchorRow_last i h b : last (AnchorRow i h b) 0<=i.
Proof.
  unfold AnchorRow; destruct b as [|b].
  - cbn[repeat]; rewrite app_nil_r; destruct h; [cbn; lia|].
    rewrite Cycles_last by discriminate; cbn[last]; lia.
  - rewrite last_suffix by discriminate.
    assert (E : last (repeat 0 (S b)) 0=0).
    { induction b; cbn; auto. }
    rewrite E; lia.
Qed.

Lemma AnchorRows_extend N xs h rows b : 0<N -> b<=1 -> AnchorRowsSpec N xs h rows ->
  AnchorRowsSpec (1+N) (xs++[h*2+b]) (h*2+b) (rows++[AnchorRow N h b]).
Proof.
  intros HN HB [EL [EV [HF [HR [HL H0]]]]].
  unfold AnchorRowsSpec; rewrite length_app, map_app, EL, EV; cbn[map length].
  rewrite AnchorRow_length; split; [lia|split; [reflexivity|split]].
  - intro v; specialize (HF v); unfold incoming in *.
    rewrite concat_app, count_occ_app, weighted_app, EL; cbn[concat weighted].
    rewrite app_nil_r, AnchorRow_count, AnchorRow_length.
    replace (N+1) with (1+N) by lia; nia.
  - split.
    + intros M i HI; destruct (Nat.eq_dec i N) as [->|Hne].
      * rewrite app_nth2, EL, Nat.sub_diag by lia; cbn[nth]; apply AnchorRow_rules; assumption.
      * rewrite app_nth1 by lia; apply HR; lia.
    + split.
      * intros i HI; destruct (Nat.eq_dec i N) as [->|Hne].
        -- rewrite app_nth2, EL, Nat.sub_diag by lia; cbn[nth]; pose proof (AnchorRow_last N h b); lia.
        -- rewrite app_nth1 by lia; apply HL; lia.
      * rewrite app_nth1 by lia; exact H0.
Qed.

Lemma FlatAnchor_rows N xs h : FlatAnchor N xs h -> 0<N /\ exists rows, AnchorRowsSpec N xs h rows.
Proof.
  intro H; induction H as [|N xs h H [HN [rows HS]]|N xs h H [HN [rows HS]]].
  - split; [lia|exists [[0]]; unfold AnchorRowsSpec; repeat split].
    + intro v; change (count_occ Nat.eq_dec [0] v+1*mark 1 v=1*mark 1 v+0+1*mark 0 v).
      rewrite count_cons; cbn[count_occ]; lia.
    + intros M i HI; assert (i=0) by lia; subst i.
      change (FlatMove M 1 0 0 /\ True); split; [constructor; reflexivity || lia|exact I].
    + intros i HI; assert (i=0) by lia; subst i; cbn; lia.
  - split; [lia|exists (rows++[AnchorRow N h 0])].
    pose proof (AnchorRows_extend HN (Nat.le_0_l 1) HS) as HC.
    rewrite Nat.add_0_r in HC; exact HC.
  - split; [lia|exists (rows++[AnchorRow N h 1])].
    replace (1+h*2) with (h*2+1) by lia; apply AnchorRows_extend; assumption || lia.
Qed.

Lemma total_lengths rows : total (map (@length nat) rows)=length (concat rows).
Proof. induction rows; cbn; rewrite ?length_app, ?IHrows; reflexivity. Qed.

Theorem FlatAnchor_reachable N xs h : FlatAnchor N xs h ->
  FlatSteps N (h+total xs) (0::repeat 0 N) (h::xs).
Proof.
  intro HA; destruct (FlatAnchor_rows HA) as [HN [rows [EL [EV [HB [HR [HF H0]]]]]]].
  set (all:=Cycles [N] h::rows).
  assert (EA : length all=1+N) by (unfold all; cbn[length]; lia).
  assert (EM : map (@length nat) all=h::xs).
  { unfold all; cbn[map]; rewrite EV, Cycles_length; cbn[length]; f_equal; lia. }
  assert (ET : length (concat all)=h+total xs).
  { rewrite <- total_lengths, EM; reflexivity. }
  rewrite <- ET, <- EM; eapply Flat_certificate with (sink:=0) (rank:=fun i=>i);
    [exact HN|exact EA| | | |].
  - rewrite <- EA; apply RowRules_initial; intro i.
    destruct i as [|i].
    + change (Indexed (FlatExitMove N 0) 0 (Cycles [N] h)).
      eapply Indexed_mono; [intros; left; eassumption|apply FlatRoot_rules].
    + change (Indexed (FlatExitMove N (1+i)) 0 (nth i rows [])).
      destruct (Nat.lt_ge_cases i N).
      * eapply Indexed_mono; [intros; left; eassumption|apply HR; assumption].
      * rewrite nth_overflow by lia; exact I.
  - intro v; specialize (HB v); unfold all,incoming; cbn[concat].
    rewrite count_occ_app, Cycles_count, count_cons; cbn[count_occ].
    rewrite <- weighted_outgoing; cbn[weighted]; rewrite Cycles_length; cbn[length].
    unfold incoming in HB; cbn[Nat.add] in *; nia.
  - intros [|i] HI HE; [contradiction|].
    change (last (nth i rows []) 0<1+i); apply HF.
    destruct (Nat.lt_ge_cases i N); [assumption|rewrite nth_overflow in HE by (cbn[all length]; lia); contradiction].
  - intros rest ys i HY HV HB' HI.
    pose proof (VisitBudget_bound 1 HV) as Hbound; unfold outgoing, all in Hbound.
    change (nth 1 ys 0<=length (nth 0 rows [])) in Hbound; rewrite H0 in Hbound; exact Hbound.
Qed.

(* Small finite initialization checks; every computed half-step rejects overflow. *)
Module FlatEval.

Fixpoint run N t c := match t with
  | 0 => Some c
  | S t => match CounterEval.half_c (repeat false N) 1 c with
    | Some d => run N t d | None => None end end.

Lemma run_spec N t : forall xs u ys v, run N t (xs,u)=Some (ys,v) ->
  FlatSteps N t (u::xs) (v::ys).
Proof.
  induction t; intros xs u ys v H; cbn[run] in H.
  - inversion H; constructor.
  - destruct (CounterEval.half_c (repeat false N) 1 (xs,u)) as [[zs w]|] eqn:HT;
      [|discriminate].
    eapply FlatSteps_cons; [constructor; apply CounterEval.half_c_spec; exact HT|].
    apply IHt; exact H.
Qed.

Definition check N t xs u ys v := match run N t (xs,u) with
  | Some (zs,w) => if Nat.eqb w v then CounterEval.counts_eqb zs ys else false
  | None => false end.

Theorem check_spec N t xs u ys v : check N t xs u ys v=true ->
  FlatSteps N t (u::xs) (v::ys).
Proof.
  unfold check; destruct (run N t (xs,u)) as [[zs w]|] eqn:H; [|discriminate].
  destruct (Nat.eqb w v) eqn:E; [apply Nat.eqb_eq in E; subst|discriminate].
  intro HE; apply CounterEval.counts_eqb_spec in HE; subst; eapply run_spec; exact H.
Qed.

End FlatEval.

(* A seed may occupy any body positions, not just the root. Every compared
   future is supplied independently by the same finite capacity certificate. *)
Lemma Ticks_many_absorbs es early bounds h C : Half es 0 bounds h bounds h 0 ->
  (forall j xs u noise z endc w endn q,
    Ticks es early j (repeat 0 (length es)) 0 xs u ->
    Ticks es early (1+C) xs u endc w -> Ticks es early C noise z endn q ->
    One (u::xs) (z::noise) -> exists s ys v, s<=C /\
    Ticks es early s noise z ys v /\ Ticks es early (1+s) xs u ys v) ->
  forall k xs u, total xs+u=k -> Forall2 le xs bounds -> k*(C+1)+1<=h ->
  exists t ys v, t<=k*C /\ Ticks es early t xs u ys v /\
    Ticks es early (t+k) (repeat 0 (length es)) 0 ys v /\ Forall2 le ys bounds.
Proof.
  intros HB Couple; induction k; intros xs u HM HX HK.
  - assert (EU : u=0) by lia; subst u.
    assert (EL : length xs=length es).
    { apply Forall2_length in HX; pose proof (Half_length HB); lia. }
    assert (E : repeat 0 (length es)=xs).
    { rewrite <- EL; apply total_eq; [apply zeros_le|rewrite total_zeros; lia]. }
    subst xs; exists 0,(repeat 0 (length es)),0; repeat split; auto using Ticks_nil; lia.
  - destruct (@le_one_before (repeat 0 (length (u::xs))) (u::xs)
      (zeros_le (u::xs)) ltac:(rewrite total_zeros; cbn; lia)) as [mid [HL HU]].
    destruct mid as [|z noise]; [inversion HU|].
    pose proof (One_mass HU) as EM; cbn[total] in EM.
    pose proof (One_le HU) as HE; inversion HE as [|z0 u0 ns xs0 Hzu Hnx]; subst.
    assert (Hbound : Forall2 le noise bounds) by (eapply le_trans_list; eassumption).
    destruct (IHk noise z ltac:(lia) Hbound ltac:(nia)) as [t [ys [v [Ht [HR [HP HY]]]]]].
    destruct (@Ticks_box_total es bounds h early t HB xs u HX ltac:(nia))
      as [noisecut [q [HN HNbound]]].
    pose proof (Ticks_unit HR HN HU) as Hunit.
    pose proof (Ticks_mass HP) as EP; rewrite total_zeros in EP.
    pose proof (Ticks_mass HN) as EN.
    destruct (@Ticks_box_total es bounds h early (1+C) HB ys v HY ltac:(nia))
      as [endc [w [HC _]]].
    destruct (@Ticks_box_total es bounds h early C HB noisecut q HNbound ltac:(nia))
      as [endn [r [HF _]]].
    destruct (Couple _ _ _ _ _ _ _ _ _ HP HC HF Hunit) as [s [zs [a [Hs [HD HE']]]]].
    assert (HA : Ticks es early (t+s) xs u zs a) by (eapply Ticks_app; eassumption).
    exists (t+s),zs,a; split; [nia|split; [exact HA|split]].
    + replace (t+s+S k) with ((t+k)+(1+s)) by lia; eapply Ticks_app; eassumption.
    + eapply Ticks_box_preserves; [exact HB|exact HA|exact HX|nia].
Qed.

(* Machines TM2, TM4, TM3, TM6, TM7 and TM5. *)

From BusyCoq Require Import Individual62 SimplTape ES_v3 DivModCases.
From Coq Require Import ZifyNat Lia String List PeanoNat Bool ArithRing Wf_nat.
Import ListNotations.
Set Implicit Arguments.
Open Scope sym.


Module TM2.
Definition tm := Eval compute in (TM_from_str "1RB1LD_1RC---_0LD1RE_0LF1RE_0RC0RB_0LA1LF").
Notation "c -->* c'" := (c -[tm]->* c') (at level 40).
Notation "c -->+ c'" := (c -[tm]->+ c') (at level 40).

Fixpoint LC (xs:list nat) :=
  match xs with [] => 0inf | a::xs => LC xs <* <[1;0]^^a <* <[1] end.
Definition S1 xs n := LC xs {{C}}> [1;0]^^n *> 0inf.
Definition QL (p:bool) := if p then D else F.

Inductive Edge : nat -> nat -> list nat -> Prop :=
| Edge_even a : Edge (a*2) (1+a*2) [0;0]%nat
| Edge_odd a : Edge (1+a*2) (3+a*2) [0]%nat.

Notation LInc := (Flow_LInc Edge).
Notation Run := (Flow_Run Edge).
Definition retire a := Alt (Nat.odd a) (1+a).

Lemma Edge_size a b kids : Edge a b kids -> length kids<=2.
Proof. intro H; destruct H; cbn; lia. Qed.

Lemma Edge_functional a b kids c kids' :
  Edge a b kids -> Edge a c kids' -> b=c /\ kids=kids'.
Proof. intros H H'; destruct H; inversion H'; subst; split; try reflexivity; f_equal; lia. Qed.

Lemma LInc_spec p xs ys : LInc p xs ys ->
  forall r, LC xs <{{QL p}} [1;0] *> r -->* LC ys {{C}}> r.
Proof.
  intro H; induction H; intros r.
  - cbn[LC QL]; es.
  - destruct (mod2 a) as [k E|k E]; subst a.
    + rewrite odd_0 in IHLInc. destruct k as [|k]; [lia|].
      replace (S k*2) with (2+k*2) by lia.
      cbn[LC QL] in *; es; er; follow IHLInc; es.
    + rewrite odd_1 in IHLInc. cbn[LC QL] in *; es; er; follow IHLInc; es.
  - destruct H; cbn[LC QL]; es.
Qed.

Lemma Inc_right n xs ys : LInc (Nat.odd n) xs ys ->
  S1 xs (1+n) -->* S1 ys n.
Proof.
  intro H; destruct (mod2 n) as [a E|a E]; subst n.
  - rewrite odd_0 in H. eapply LInc_spec in H. es; er; follow H; finish.
  - rewrite odd_1 in H. eapply LInc_spec in H. es; er; follow H; finish.
Qed.

Lemma Inc_zero a xs ys : LInc (Nat.odd a) xs ys ->
  S1 (a::xs) 0 -->+ S1 ys a.
Proof.
  intro H; destruct (mod2 a) as [k E|k E]; subst a.
  - rewrite odd_0 in H. eapply LInc_spec in H. unfold S1; cbn[LC].
    es; er; follow H; finish.
  - rewrite odd_1 in H. eapply LInc_spec in H. unfold S1; cbn[LC].
    es; er; follow H; finish.
Qed.

Lemma Run_right n xs ys : Run (Alt (negb (Nat.odd n)) n) xs ys ->
  S1 xs n -->* S1 ys 0.
Proof.
  revert xs; induction n; intros xs H.
  - inversion H; subst; apply evstep_refl.
  - cbn[Alt] in H. rewrite Nat.odd_succ, Nat.negb_even in H.
    inversion H as [|p w source cut target HL HR]; subst.
    follow (Inc_right n HL). apply IHn; assumption.
Qed.

Lemma Macro_spec xs ys : Flow_Macro Edge retire xs ys -> S1 xs 0 -->+ S1 ys 0.
Proof.
  intro H; destruct H. cbn[retire Alt] in H.
  inversion H as [|p w source cut target HL HR]; subst.
  follow10 (Inc_zero a HL). apply Run_right; assumption.
Qed.

Lemma init : c0 -->* S1 [2] 1.
Proof. unfold S1; esx. Qed.

Lemma first_cut : c0 -->* S1 [3;0;0]%nat 0.
Proof. follow init. apply Inc_right. apply LInc_edge, (Edge_even 1). Qed.

Lemma InfiniteMacro_nonhalt xs :
  Flow_InfiniteMacro Edge retire xs -> ~halts tm (S1 xs 0).
Proof.
  intro HI. eapply progress_nonhalt with
    (P:=fun c => exists ys, Flow_InfiniteMacro Edge retire ys /\ c=S1 ys 0).
  - intros c [ys [H ->]]. destruct H as [ys zs HM HI'].
    exists (S1 zs 0); split; [exists zs; auto|apply Macro_spec; assumption].
  - exists xs; auto.
Qed.

Lemma nonhalt_from_lives :
  Flow_InfiniteLife Edge retire [] [3;0;0]%nat -> ~halts tm c0.
Proof.
  intro H; eapply multistep_nonhalt; [apply first_cut|].
  apply InfiniteMacro_nonhalt. eapply InfiniteLife_sound;
    eauto using Edge_size, Edge_functional, Run_nil.
Qed.

Close Scope sym.
Definition Word xs u := CWord true 2 0 xs u.

Lemma parent_column (two:bool) xs qs r u : TailSplit false xs (O::qs) r ->
  Flow_Life Edge retire ((if two then [true] else [])++Word xs u) [O]
    (Word (qs++[u]) (1+r)) (if two then [O;O] else [O]).
Proof.
  intro H; inversion H as [|e x q r0 tail out s HS HT]; subst.
  destruct (CWord_pass HT 1 1 u (3+r0) ltac:(lia) HS ltac:(lia)) as [A [o [HP EO]]].
  change (o++retire A = CWord true 2 O (qs++[u]) (1+(r0+s))) in EO.
  unfold Word; rewrite <- EO.
  destruct two; inversion HS; subst; cbn[CWord Alt Nat.add Nat.mul List.app].
  - eapply Life_terminal with (k:=2) (b:=3); [apply (Edge_even 1)|exact HP].
  - eapply Life_terminal with (k:=2) (b:=3); [apply (Edge_even 1)|apply Pass_P; exact HP].
  - eapply Life_terminal with (k:=1) (b:=3); [apply (Edge_odd 0)|exact HP].
  - eapply Life_terminal with (k:=1) (b:=3); [apply (Edge_odd 0)|apply Pass_P; exact HP].
Qed.

Lemma internal_column xs qs r u : TailSplit false xs (O::qs) r ->
  Flow_Life Edge retire (Word xs u) [O;O] (true::Word (qs++[u]) r) [O].
Proof.
  intro H; inversion H as [|e x q r0 tail out s HS HT]; subst.
  destruct (CWord_pass HT 1 0 u (1+r0) ltac:(lia) HS ltac:(lia)) as [A [o [HP EO]]].
  change (o++retire A = CWord true 2 O (qs++[u]) (r0+s)) in EO.
  unfold Word; rewrite <- EO. eapply Life_internal with (b:=A) (o:=true::o); [discriminate|].
  inversion HS; subst; cbn[CWord Alt Nat.add Nat.mul List.app];
    apply Pass_P, Pass_I; [lia|exact HP|lia|apply Pass_P; exact HP].
Qed.

Lemma Tick_lives n xs u ys v : Tick (Alt false (n*2)) true xs u ys v 0 ->
  Lives Edge retire 2 (true::Word xs u) [0] (true::Word ys v) [0].
Proof.
  intro H; inversion H as [xs0 u0 middle root ys0 v0 a b H1 H2]; subst.
  assert (a=0 /\ b=0) as [-> ->] by lia.
  destruct (Half_tail n H1) as [qs [r [HS [Em Er]]]]; subst middle root.
  destruct (Half_tail n H2) as [ps [s [HT [Ey Ev]]]]; subst ys v.
  eapply Lives_cons; [apply (parent_column true); exact HS|].
  eapply Lives_cons; [apply internal_column; exact HT|constructor].
Qed.

Lemma Ticks_lives n t xs u ys v : Ticks (Alt false (n*2)) true t xs u ys v ->
  Lives Edge retire (t*2) (true::Word xs u) [0] (true::Word ys v) [0].
Proof.
  intro H; induction H; [constructor|].
  replace ((1+n0)*2) with (2+n0*2) by lia.
  eapply Lives_app; [apply (Tick_lives n); eassumption|assumption].
Qed.

(* The index k corresponds to N=2+k*2 stream coordinates. A capacity
   certificate is a fixed point of the zero-injection auxiliary half-step. *)
Inductive Box : nat -> list nat -> nat -> Prop :=
| Box_base : Box 0 [0;0] 0
| Box_step k xs h : Box k xs h ->
    Box (1+k) (xs++[1+h*2;2+h*4]) (2+h*4).

Lemma Box_total k : exists xs h, Box k xs h.
Proof. induction k as [|k [xs [h H]]]; eauto using Box_base, Box_step. Qed.

Lemma Box_spec k xs h : Box k xs h ->
  length xs=2+k*2 /\ Half (Alt false (2+k*2)) 0 xs h xs h 0 /\
  exists tail, xs=0::0::tail.
Proof.
  intro H; induction H as [|k xs h H [EL [HB [tail ->]]]].
  - split; [reflexivity|split; [|exists (@nil nat); reflexivity]].
    change (Half ([false]++[true]) 0 ([0]++[0]) 0 ([0]++[0]) 0 0).
    eapply Half_box_extend; [apply Half_box_base; apply (Split_even false 0)|].
    apply (Split_even true 0).
  - split; [rewrite length_app; cbn in *; lia|split; [|exists (tail++[1+h*2;2+h*4]); reflexivity]].
    replace (2+(1+k)*2) with ((1+k)*2+2) by lia.
    rewrite Alt_app_even.
    replace ((1+k)*2) with (2+k*2) by lia.
    change (Half (Alt false (2+k*2)++[false;true]) 0
      ((0::0::tail)++[1+h*2;2+h*4]) (2+h*4)
      ((0::0::tail)++[1+h*2;2+h*4]) (2+h*4) 0).
    rewrite (app_assoc _ [false] [true]), (app_assoc _ [1+h*2] [2+h*4]).
    eapply Half_box_extend; [eapply Half_box_extend; [exact HB|constructor]|].
    replace (2+h*4) with ((1+h*2)*2) by lia; constructor.
Qed.

Lemma Box_capacity k xs h : Box k xs h -> h*6+4=4^(1+k).
Proof.
  intro H; induction H; [reflexivity|].
  change ((2+h*4)*6+4=4*4^(1+k)); rewrite <- IHBox; lia.
Qed.

Lemma Box_budget n : forall xs h, Box (6+n) xs h ->
  (177+n*16)*(7+n)+1<=h.
Proof.
  induction n; intros xs h H.
  - repeat match goal with H : Box _ _ _ |- _ => inversion H; subst; clear H end.
    cbn; lia.
  - inversion H as [|j ys r HS]; subst. apply IHn in HS; nia.
Qed.

(* The ordinary unit-routing table. The two first-position overflow branches
   are not transitions of this relation; their separate boundary rules are
   needed when leaving the ordinary phase. *)
Inductive Move (N:nat) : nat -> nat -> nat -> Prop :=
| Move_root_even a : Move N 0 (a*2) (N-1)
| Move_root_odd a : Move N 0 (1+a*2) 0
| Move_even_odd i a : 0<i -> Nat.odd i=false -> Move N i (1+a*2) N
| Move_odd_even i a : 0<i -> Nat.odd i=true -> Move N i (a*2) N
| Move_even0 i a : 1<i -> Nat.odd i=false -> Move N i (a*4) 0
| Move_even2 i a : 2<i -> Nat.odd i=false -> Move N i (2+a*4) (i-2)
| Move_odd1 i a : 2<i -> Nat.odd i=true -> Move N i (1+a*4) (i-2)
| Move_odd3 i a : 1<i -> Nat.odd i=true -> Move N i (3+a*4) 0.

Lemma Move_return N i a : 0<i -> xorb (Nat.odd i) (Nat.odd a)=true -> Move N i a N.
Proof.
  intros HI HE; destruct (mod2 a) as [b E|b E]; subst a;
    rewrite ?odd_0, ?odd_1 in HE; destruct (Nat.odd i) eqn:EI;
    cbn in HE; try discriminate; constructor; assumption.
Qed.

Lemma Move_root N a j : j=(if Nat.odd a then 0 else N-1) -> Move N 0 a j.
Proof.
  intros ->; destruct (mod2 a) as [b E|b E]; subst a; rewrite ?odd_0, ?odd_1; constructor.
Qed.

Lemma Move_forward N i a q r flag : 1<i -> (flag=true -> 2<i) ->
  Split (negb (Nat.odd i)) a q r -> xorb (negb (Nat.odd i)) (Nat.odd a)=true ->
  xorb (Nat.odd i) (Nat.odd q)=flag -> Move N i a (if flag then i-2 else 0).
Proof.
  intros HI Hfront HS HE HQ; pose proof (Split_forward HS HE) as E.
  destruct (mod2 q) as [b EQ|b EQ]; subst q; rewrite ?odd_0, ?odd_1 in HQ;
    destruct (Nat.odd i) eqn:EI; destruct flag; cbn in HQ, E; try discriminate.
  - replace a with (1+b*4) by lia; constructor; auto.
  - replace a with (b*4) by lia; constructor; auto.
  - replace a with (3+b*4) by lia; constructor; auto.
  - replace a with (2+b*4) by lia; constructor; auto.
Qed.

Lemma AltMove_pair N root out i a j b k c : 1<N -> Nat.odd N=false ->
  AltMove false N root i a j b -> AltMove false N out j b k c -> Move N i a k.
Proof.
  intros HN EN H1 H2.
  destruct H1 as [a0|i0 a0 HI HE|i0 a0 q0 r0 HI HS HE];
    inversion H2 as [a1|i1 a1 HI1 HE1|i1 a1 q1 r1 HI1 HS1 HE1]; subst;
    cbn[xorb] in *; try lia.
  - apply Move_root; rewrite EN in HE1; cbn in HE1; rewrite HE1; reflexivity.
  - apply Move_root; rewrite EN in HE1; cbn in HE1.
    apply negb_true_iff in HE1; rewrite HE1; reflexivity.
  - apply Move_return; assumption.
  - eapply Move_forward with (flag:=false); [exact HI|discriminate|exact HS|exact HE|].
    rewrite odd_pred, <- negb_xorb_l in HE1 by lia; apply negb_true_iff in HE1; exact HE1.
  - replace (i0-1-1) with (i0-2) by lia.
    eapply Move_forward with (flag:=true); [exact HI|lia|exact HS|exact HE|].
    rewrite odd_pred, negb_involutive in HE1 by lia; exact HE1.
Qed.

Lemma Tick_route n xs u ys v xs' u' ys' v' i a :
  Tick (Alt false (2+n*2)) true xs u ys v 0 ->
  Tick (Alt false (2+n*2)) true xs' u' ys' v' 0 ->
  Bump i a (u::xs) (u'::xs') -> exists j b,
  Move (2+n*2) i a j /\ Bump j b (v::ys) (v'::ys').
Proof.
  intros H H' HU. destruct (Tick_length H) as [EL _]; rewrite Alt_length in EL.
  destruct (Bump_length HU) as [_ IL]; cbn in IL.
  destruct (Tick_bump H H' HU) as [root [j [b [k [c [HM [HM' HB]]]]]]].
  assert (HJ : j<=2+n*2).
  { eapply HalfMove_bound in HM; [rewrite Alt_length in HM; exact HM|rewrite Alt_length; lia]. }
  exists k,c; split; [|exact HB].
  eapply AltMove_pair; [lia|change (Nat.odd ((1+n)*2)=false); apply odd_0| |].
  - apply HalfMove_alt; [exact HM|lia].
  - apply HalfMove_alt; [exact HM'|exact HJ].
Qed.

Lemma Move_root_depart N a j : 1<N -> Move N 0 a j -> j<>0 -> Nat.odd a=false.
Proof. intros HN H HJ; inversion H; subst; try lia; apply odd_0. Qed.

Lemma Move_last_depart N a j : 1<N -> Nat.odd N=false ->
  Move N N a j -> j<>N -> Nat.odd a=false.
Proof.
  intros HN EN H HJ; inversion H; subst; try lia; try congruence.
  - apply odd_four.
  - rewrite Nat.odd_add, odd_four; reflexivity.
Qed.

Lemma Move_root_stay N a j : 1<N -> Move N 0 a j -> Nat.odd a=true -> j=0.
Proof.
  intros HN HM HE; destruct (Nat.eq_dec j 0); [assumption|].
  pose proof (Move_root_depart HN HM n); congruence.
Qed.

Lemma Move_last_stay N a j : 1<N -> Nat.odd N=false ->
  Move N N a j -> Nat.odd a=true -> j=N.
Proof.
  intros HN EN HM HE; destruct (Nat.eq_dec j N); [assumption|].
  pose proof (Move_last_depart HN EN HM n); congruence.
Qed.

Lemma Move_waiting N xs ys i a j : 1<N -> Nat.odd N=false ->
  Bump i a xs ys -> Move N i a j ->
  Waiting 0 xs i -> Waiting N xs i -> Waiting 0 ys j /\ Waiting N ys j.
Proof.
  intros HN EN HB HM H0 HN'. split; eapply Bump_wait; eauto.
  - intros -> HJ; eapply Move_root_depart; eauto.
  - intros -> HJ; eapply Move_last_depart; eauto.
Qed.

Lemma Move_descends N i a j : Move N i a j -> i<>0 -> j<>0 -> j<>N -> j+2=i.
Proof. intros H HI H0 HN; inversion H; subst; lia. Qed.

Lemma Move_penultimate N a j : 1<N -> Nat.odd N=false ->
  Move N (N-1) a j -> Nat.odd a=false -> j=N.
Proof.
  intros HN EN HM HE.
  assert (EP : Nat.odd (N-1)=true) by (rewrite odd_pred, EN by lia; reflexivity).
  inversion HM; subst; try lia; try congruence.
  all: rewrite Nat.odd_add, odd_four in HE; discriminate.
Qed.

Lemma Move_internal N i a j : Move N i a j -> i<>0 ->
  j=N \/ (j=0 /\ 1<i) \/ (j+2=i /\ 2<i).
Proof. intros H HI; inversion H; subst; intuition lia. Qed.

Lemma Move_root_value N a j : Move N 0 a j -> j=(if Nat.odd a then 0 else N-1).
Proof. intro H; inversion H; subst; try lia; rewrite ?odd_0, ?odd_1; reflexivity. Qed.

(* m=N/2. Only the parity at N-1 and at the root is needed. *)
Definition LastRank m (penult root:bool) i :=
  if i =? m*2 then 0 else
  if i =? m*2-1 then (if penult then m+1+(if root then 1 else 0) else 1)
  else (if penult then m+3 else 2)+(if root then 1 else 0)+i/2.

Lemma LastRank_last m e f : LastRank m e f (m*2)=0.
Proof. unfold LastRank; rewrite Nat.eqb_refl; reflexivity. Qed.

Lemma LastRank_penult m e f : 0<m ->
  LastRank m e f (m*2-1)=(if e then m+1+(if f then 1 else 0) else 1).
Proof.
  intro HM; unfold LastRank; rewrite Nat.eqb_refl.
  destruct (m*2-1 =? m*2) eqn:E; [apply Nat.eqb_eq in E; lia|reflexivity].
Qed.

Lemma LastRank_regular m e f i : i<>m*2 -> i<>m*2-1 ->
  LastRank m e f i=(if e then m+3 else 2)+(if f then 1 else 0)+i/2.
Proof.
  intros H1 H2; unfold LastRank.
  destruct (i =? m*2) eqn:E; [apply Nat.eqb_eq in E; contradiction|].
  destruct (i =? m*2-1) eqn:F; [apply Nat.eqb_eq in F; contradiction|reflexivity].
Qed.

Lemma LastRank_bound m e f i : 2<=m -> i<=m*2 -> LastRank m e f i<=m*2+3.
Proof.
  intros HM HI; unfold LastRank.
  destruct (i =? m*2) eqn:E, (i =? m*2-1) eqn:F, e, f;
    apply Nat.eqb_eq in E || apply Nat.eqb_neq in E;
    apply Nat.eqb_eq in F || apply Nat.eqb_neq in F; lia.
Qed.

Lemma LastRank_step m i a j e f : 2<=m -> i<m*2 -> Move (m*2) i a j ->
  (i=m*2-1 -> e=Nat.odd a) -> (i=0 -> f=Nat.odd a) ->
  LastRank m (if i =? m*2-1 then negb e else e)
    (if i =? 0 then negb f else f) j < LastRank m e f i.
Proof.
  intros HM HI H HE HF.
  destruct (Nat.eq_dec i 0) as [->|H0].
  - specialize (HF eq_refl); subst f. apply Move_root_value in H; subst j.
    assert (EZ : (0 =? m*2-1)=false) by (apply Nat.eqb_neq; lia).
    rewrite EZ; cbn[Nat.eqb].
    rewrite (@LastRank_regular m e (Nat.odd a) 0) by lia.
    destruct (Nat.odd a),e; cbn[negb];
      rewrite ?LastRank_penult, ?LastRank_regular by lia; lia.
  - assert (E0 : (i =? 0)=false) by (apply Nat.eqb_neq; assumption).
    rewrite E0. destruct (Nat.eq_dec i (m*2-1)) as [->|HS].
    + rewrite Nat.eqb_refl, LastRank_penult by lia.
      destruct (Move_internal H H0) as [->|[[-> Hpos]|[E Hpos]]].
      * rewrite LastRank_last; destruct e,f; lia.
      * assert (EA : Nat.odd a=true).
        { destruct (Nat.odd a) eqn:EA; [reflexivity|].
          pose proof (Move_penultimate (N:=m*2) ltac:(lia) (odd_0 m) H EA); lia. }
        specialize (HE eq_refl); rewrite EA in HE; subst e.
        cbn[negb]; rewrite LastRank_regular by lia; destruct f; lia.
      * assert (EA : Nat.odd a=true).
        { destruct (Nat.odd a) eqn:EA; [reflexivity|].
          pose proof (Move_penultimate (N:=m*2) ltac:(lia) (odd_0 m) H EA); lia. }
        specialize (HE eq_refl); rewrite EA in HE; subst e.
        cbn[negb]; rewrite LastRank_regular by lia; destruct f; lia.
    + assert (ES : (i =? m*2-1)=false) by (apply Nat.eqb_neq; assumption).
      rewrite ES, (@LastRank_regular m e f i) by lia.
      destruct (Move_internal H H0) as [->|[[-> Hpos]|[E Hpos]]].
      * rewrite LastRank_last; destruct e,f; lia.
      * rewrite LastRank_regular by lia; destruct e,f; lia.
      * rewrite LastRank_regular by lia; destruct e,f; lia.
Qed.

Definition RankN m xs i :=
  LastRank m (Nat.odd (nth (m*2-1) xs 0)) (Nat.odd (nth 0 xs 0)) i.

Lemma RankN_bound m xs i : 2<=m -> i<=m*2 -> RankN m xs i<=m*2+3.
Proof. apply LastRank_bound. Qed.

Lemma RankN_step m xs i a ys j : 2<=m -> i<m*2 ->
  Bump i a xs ys -> Move (m*2) i a j -> RankN m ys j<RankN m xs i.
Proof.
  intros HM HI HB HD; unfold RankN.
  rewrite (Bump_odd (m*2-1) HB), (Bump_odd 0 HB).
  apply LastRank_step with (a:=a); auto;
    intros E; subst i; f_equal; exact (proj1 (Bump_nth HB)).
Qed.

Definition Countdown a := if a mod 4 =? 0 then 1 else 5-a mod 4.

Lemma Countdown_bound a : 1<=Countdown a /\ Countdown a<=4.
Proof.
  unfold Countdown; destruct (a mod 4 =? 0) eqn:E;
    apply Nat.eqb_eq in E || apply Nat.eqb_neq in E; lia.
Qed.

Lemma Countdown_step a : a mod 4<>0 -> Countdown (1+a)+1=Countdown a.
Proof.
  intro H; unfold Countdown.
  destruct (a mod 4 =? 0) eqn:E, ((1+a) mod 4 =? 0) eqn:F;
    apply Nat.eqb_eq in E || apply Nat.eqb_neq in E;
    apply Nat.eqb_eq in F || apply Nat.eqb_neq in F; lia.
Qed.

Lemma Move_bound N i a j : Move N i a j -> i<=N -> j<=N.
Proof. intro H; destruct H; lia. Qed.

Lemma Move_last_countdown N a j : 1<N -> Nat.odd N=false ->
  Move N N a j -> j<>0 -> Countdown (1+a)+1=Countdown a.
Proof.
  intros HN EN H HJ; apply Countdown_step.
  inversion H; subst; try congruence; lia.
Qed.

Definition Rank0 m xs i :=
  if i =? 0 then 0 else Countdown (nth (m*2) xs 0)*(m*2+4)+RankN m xs i.

Lemma Rank0_bound m xs i : 2<=m -> i<=m*2 -> Rank0 m xs i<=m*10+19.
Proof.
  intros HM HI; unfold Rank0; destruct (i =? 0); [lia|].
  pose proof (Countdown_bound (nth (m*2) xs 0)).
  pose proof (RankN_bound xs HM HI); nia.
Qed.

Lemma Rank0_step m xs i a ys j : 2<=m -> i<=m*2 -> i<>0 ->
  Bump i a xs ys -> Move (m*2) i a j -> Rank0 m ys j<Rank0 m xs i.
Proof.
  intros HM HI H0 HB HD.
  assert (EI : (i =? 0)=false) by (apply Nat.eqb_neq; assumption).
  unfold Rank0; rewrite EI.
  destruct (j =? 0) eqn:EJ.
  - pose proof (Countdown_bound (nth (m*2) xs 0)); nia.
  - apply Nat.eqb_neq in EJ.
    destruct (Nat.eq_dec i (m*2)) as [->|HN].
    + destruct (Bump_nth HB) as [EX EY]; rewrite EX, EY.
      unfold RankN at 2; rewrite LastRank_last.
      pose proof (Move_last_countdown (N:=m*2) ltac:(lia) (odd_0 m) HD EJ) as EC.
      pose proof (Move_bound HD HI) as HJ.
      pose proof (RankN_bound ys HM HJ); nia.
    + rewrite (Bump_other (j:=m*2) HB ltac:(lia)).
      apply Nat.add_lt_mono_l; apply RankN_step with (a:=a); auto; lia.
Qed.

Definition MeetRank m xs i k :=
  if k =? 0 then Rank0 m xs i else
  if k =? m*2 then RankN m xs i else m*10+20+k.

Lemma MeetRank_bound m xs i k : 2<=m -> i<=m*2 -> k<=m*2 ->
  MeetRank m xs i k<=m*12+20.
Proof.
  intros HM HI HK; unfold MeetRank.
  destruct (k =? 0), (k =? m*2);
    pose proof (Rank0_bound xs HM HI); pose proof (RankN_bound xs HM HI); lia.
Qed.

Lemma MeetRank_step m xs i a ys j k l : 2<=m -> i<=m*2 -> i<>k ->
  Bump i a xs ys -> Move (m*2) i a j -> Move (m*2) k (nth k xs 0) l ->
  Waiting 0 xs i -> Waiting (m*2) xs i ->
  MeetRank m ys j l < MeetRank m xs i k.
Proof.
  intros HM HI Hneq HB HD HE HW0 HWN.
  pose proof (Move_bound HD HI) as HJ.
  unfold MeetRank.
  destruct (k =? 0) eqn:E0.
  - apply Nat.eqb_eq in E0; subst k.
    assert (HF : Nat.odd (nth 0 xs 0)=true) by (destruct HW0; congruence).
    assert (l=0) by (eapply Move_root_stay with (N:=m*2); eauto; lia); subst l.
    cbn[Nat.eqb]. apply Rank0_step with (a:=a); assumption.
  - apply Nat.eqb_neq in E0.
    destruct (k =? m*2) eqn:EN.
    + apply Nat.eqb_eq in EN; subst k.
      assert (HF : Nat.odd (nth (m*2) xs 0)=true) by (destruct HWN; congruence).
      assert (l=m*2) by (eapply Move_last_stay; eauto using odd_0; lia); subst l.
      assert (EZ : (m*2 =? 0)=false) by (apply Nat.eqb_neq; lia).
      rewrite EZ, Nat.eqb_refl; apply RankN_step with (a:=a); auto; lia.
    + apply Nat.eqb_neq in EN.
      destruct (l =? 0) eqn:F0.
      * pose proof (Rank0_bound ys HM HJ); lia.
      * apply Nat.eqb_neq in F0; destruct (l =? m*2) eqn:FN.
        -- pose proof (RankN_bound ys HM HJ); lia.
        -- apply Nat.eqb_neq in FN; pose proof (Move_descends HE E0 F0 FN); lia.
Qed.

Lemma Apart_rank m n xs i k ys j l : 2<=m ->
  Apart (Move (m*2)) n xs i k ys j l -> i<=m*2 -> k<=m*2 ->
  Waiting 0 xs i -> Waiting (m*2) xs i ->
  n+MeetRank m ys j l<=MeetRank m xs i k.
Proof.
  intros HM H; induction H; intros HI HK HW0 HWN; [lia|].
  pose proof (Move_bound H1 HI) as HJ; pose proof (Move_bound H2 HK) as HL.
  destruct (Move_waiting (N:=m*2) ltac:(lia) (odd_0 m) H0 H1 HW0 HWN) as [HV0 HVN].
  specialize (IHApart HJ HL HV0 HVN).
  pose proof (MeetRank_step HM HI H H0 H1 H2 HW0 HWN); lia.
Qed.

Lemma Apart_bound m n xs i k ys j l : 2<=m ->
  Apart (Move (m*2)) n xs i k ys j l -> i<=m*2 -> k<=m*2 ->
  Waiting 0 xs i -> Waiting (m*2) xs i -> n<=m*12+20.
Proof.
  intros HM H HI HK HW0 HWN.
  pose proof (Apart_rank HM H HI HK HW0 HWN).
  pose proof (MeetRank_bound xs HM HI HK); lia.
Qed.

Lemma Tick_route_even m xs u ys v xs' u' ys' v' i a : 0<m ->
  Tick (Alt false (m*2)) true xs u ys v 0 ->
  Tick (Alt false (m*2)) true xs' u' ys' v' 0 ->
  Bump i a (u::xs) (u'::xs') -> exists j b,
  Move (m*2) i a j /\ Bump j b (v::ys) (v'::ys').
Proof. destruct m; [lia|intros _; apply Tick_route]. Qed.

Lemma Tick_initial_bump m xs u : Tick (Alt false (m*2)) true (repeat 0 (m*2)) 0 xs u 0 ->
  Bump (m*2) 0 (0::repeat 0 (m*2)) (u::xs).
Proof.
  pose proof (@Tick_zeros_bump (Alt false (m*2)) xs u) as H; rewrite Alt_length in H; exact H.
Qed.

Lemma Move_last_zero m i : 0<m -> Move (m*2) (m*2) 0 i -> i=0.
Proof.
  intros HM H; pose proof (odd_0 m) as E; inversion H; subst; try lia; congruence.
Qed.

Lemma canonical_waiting m n : 2<=m -> forall xs u ys v i a,
  Ticks (Alt false (m*2)) true n (repeat 0 (m*2)) 0 xs u ->
  Tick (Alt false (m*2)) true xs u ys v 0 ->
  Bump i a (u::xs) (v::ys) ->
  Waiting (m*2) (u::xs) i /\ (n=0 \/ Waiting 0 (u::xs) i).
Proof.
  intro HM; induction n; intros xs u ys v i a HP HT HB.
  - inversion HP; subst.
    destruct (Bump_position HB (Tick_initial_bump m HT)) as [-> ->].
    split; [left; reflexivity|auto].
  - destruct (Ticks_unsnoc HP) as [prev [root [HR HS]]].
    assert (HU : One (root::prev) (u::xs)).
    { eapply (@Ticks_zero_unit (Alt false (m*2)) true n); rewrite Alt_length; eassumption. }
    destruct (One_bump HU) as [p [b Hprev]].
    destruct (IHn _ _ _ _ _ _ HR HS Hprev) as [HWN HW0].
    destruct (Tick_route_even (m:=m) ltac:(lia) HS HT Hprev) as [j [c [HD Hnext]]].
    destruct (Bump_position Hnext HB) as [-> _].
    split.
    + eapply Bump_wait; [exact Hprev| |exact HWN].
      intros -> HJ; eapply Move_last_depart with (N:=m*2); eauto using odd_0; lia.
    + right; destruct HW0 as [E|HW0].
      * subst n; inversion HR; subst.
        destruct (Bump_position Hprev (Tick_initial_bump m HS)) as [-> ->].
        assert (i=0) by (eapply Move_last_zero with (m:=m); eauto; lia).
        left; assumption.
      * eapply Bump_wait; [exact Hprev| |exact HW0].
        intros -> HJ; eapply Move_root_depart with (N:=m*2); eauto; lia.
Qed.

Lemma couple_prefix m t : 2<=m -> forall xs u next v endc w noise z endn q i a k b,
  Tick (Alt false (m*2)) true xs u next v 0 ->
  Ticks (Alt false (m*2)) true t next v endc w ->
  Ticks (Alt false (m*2)) true t noise z endn q ->
  Bump i a (u::xs) (v::next) -> Bump k b (u::xs) (z::noise) ->
  Waiting 0 (u::xs) i -> Waiting (m*2) (u::xs) i ->
  MeetRank m (u::xs) i k<t -> exists s ys root,
  s<=t /\ Ticks (Alt false (m*2)) true s noise z ys root /\
  Ticks (Alt false (m*2)) true (1+s) xs u ys root.
Proof.
  intros HM xs u next v endc w noise z endn q i a k b HC HCR HNR HB HK HW0 HWN HR.
  destruct (@Ticks_couple_or_apart (Alt false (m*2)) true (Move (m*2))
    (fun _ _ _ _ _ _ _ _ _ _ => @Tick_route_even m _ _ _ _ _ _ _ _ _ _ ltac:(lia))
    t _ _ _ _ _ _ _ _ _ _ _ _ _ _ HC HCR HNR HB HK) as [HJ|[last [l [r HA]]]]; [exact HJ|].
  destruct (Tick_length HC) as [EL _]; rewrite Alt_length in EL.
  destruct (Bump_length HB) as [_ HI]; destruct (Bump_length HK) as [_ Hk]; cbn in HI, Hk.
  pose proof (Apart_rank HM HA ltac:(lia) ltac:(lia) HW0 HWN); lia.
Qed.

Lemma couple_positive m j t xs u noise z endc w endn q : 2<=m -> 0<j -> m*12+20<t ->
  Ticks (Alt false (m*2)) true j (repeat 0 (m*2)) 0 xs u ->
  Ticks (Alt false (m*2)) true (1+t) xs u endc w ->
  Ticks (Alt false (m*2)) true t noise z endn q ->
  One (u::xs) (z::noise) -> exists s ys root,
  s<=t /\ Ticks (Alt false (m*2)) true s noise z ys root /\
  Ticks (Alt false (m*2)) true (1+s) xs u ys root.
Proof.
  intros HM HJ Ht HP HC HN HU.
  inversion HC as [|n0 xs0 u0 next v endc0 w0 HT HR]; subst.
  assert (HV : One (u::xs) (v::next)).
  { eapply (@Ticks_zero_unit (Alt false (m*2)) true j); rewrite Alt_length;
      [exact HP|eapply Ticks_snoc; eassumption]. }
  destruct (One_bump HV) as [i [a HB]]; destruct (One_bump HU) as [k [b HK]].
  destruct (canonical_waiting (m:=m) HM HP HT HB) as [HWN [E|HW0]]; [lia|].
  destruct (Tick_length HT) as [EL _]; rewrite Alt_length in EL.
  destruct (Bump_length HB) as [_ HI]; destruct (Bump_length HK) as [_ Hk]; cbn in HI, Hk.
  eapply couple_prefix; [exact HM|exact HT|exact HR|exact HN|exact HB|exact HK|exact HW0|exact HWN|].
  pose proof (MeetRank_bound (m:=m) (i:=i) (k:=k) (u::xs) HM ltac:(lia) ltac:(lia)); lia.
Qed.

(* One initial step also covers j=0, where the root Waiting condition is false.
   The canonical future has one more Tick than the perturbed future. *)
Lemma couple_ticks m j t xs u noise z endc w endn q : 2<=m -> m*12+21<t ->
  Ticks (Alt false (m*2)) true j (repeat 0 (m*2)) 0 xs u ->
  Ticks (Alt false (m*2)) true (1+t) xs u endc w ->
  Ticks (Alt false (m*2)) true t noise z endn q ->
  One (u::xs) (z::noise) -> exists s ys root,
  s<=t /\ Ticks (Alt false (m*2)) true s noise z ys root /\
  Ticks (Alt false (m*2)) true (1+s) xs u ys root.
Proof.
  intros HM Ht HP HC HN HU; destruct t; [lia|].
  inversion HC as [|n0 xs0 u0 next v endc0 w0 HT HR]; subst.
  inversion HN as [|n0 xs0 u0 noise' z' endn0 q0 HT' HR']; subst.
  assert (HP' : Ticks (Alt false (m*2)) true (1+j) (repeat 0 (m*2)) 0 next v)
    by (eapply Ticks_snoc; eassumption).
  pose proof (Tick_unit HT HT' HU) as HV.
  edestruct (@couple_positive m (1+j) t) as [s [ys [root [HS [HA HB]]]]];
    [exact HM|lia|lia|exact HP'|exact HR|exact HR'|exact HV|].
  exists (1+s),ys,root; split; [lia|split].
  - eapply Ticks_cons; [exact HT'|exact HA].
  - eapply Ticks_cons; [exact HT|exact HB].
Qed.

Lemma seed_absorbs m bounds h C : 2<=m -> m*12+21<C ->
  Half (Alt false (m*2)) 0 bounds h bounds h 0 -> forall k, k*(C+1)+1<=h ->
  exists t xs u, t<=k*C /\
  Ticks (Alt false (m*2)) true t (repeat 0 (m*2)) k xs u /\
  Ticks (Alt false (m*2)) true (t+k) (repeat 0 (m*2)) 0 xs u /\ Forall2 le xs bounds.
Proof.
  intros HM HC HB.
  pose proof (@Ticks_seed_absorbs (Alt false (m*2)) true bounds h C HB) as H.
  rewrite Alt_length in H; apply H; intros.
  eapply couple_ticks; eassumption.
Qed.

Theorem seed_absorption n : exists t xs u,
  t<=(7+n)*(176+n*16) /\
  Ticks (Alt false (14+n*2)) true t (repeat 0 (14+n*2)) (7+n) xs u /\
  Ticks (Alt false (14+n*2)) true (t+(7+n)) (repeat 0 (14+n*2)) 0 xs u /\
  Lives Edge retire (t*2) (true::Word (repeat 0 (14+n*2)) (7+n)) [0]
    (true::Word xs u) [0].
Proof.
  destruct (Box_total (6+n)) as [bounds [h HB]].
  destruct (Box_spec HB) as [_ [HC _]]; pose proof (Box_budget HB) as HM.
  replace (2+(6+n)*2) with ((7+n)*2) in HC by lia.
  destruct (@seed_absorbs (7+n) bounds h (176+n*16) ltac:(lia) ltac:(lia) HC (7+n) ltac:(nia))
    as [t [xs [u [Ht [HR [HP HX]]]]]].
  replace ((7+n)*2) with (14+n*2) in HR, HP by lia.
  exists t,xs,u; repeat split; try assumption.
  apply (Ticks_lives (7+n)); exact HR.
Qed.

(* Symbolic finite exit certificate, grouped into pairs of positions.
   Quarter m=(4^m-1)/3; no division or exponentially long evaluation is used. *)
Fixpoint Quarter m := match m with 0 => 0 | S m => 1+Quarter m*4 end.
Definition OddRow N d q := Cycles [N;d;N;0] q ++ [N].
Definition EvenRow N d q := Cycles [0;N;d;N] (q*2) ++ [0;N;d].
Fixpoint CertBody N m : list (list nat) :=
  match m with
  | 0 => []
  | S k => CertBody N k ++
      [OddRow N (k*2-1) (Quarter k);
       EvenRow N (match k with 0 => N+1 | _ => k*2 end) (Quarter k)]
  end.
Definition RootRow N m := Cycles [N-1;0] (Quarter m-1) ++ [N-1].
Definition CertRows m := RootRow (m*2) m :: CertBody (m*2) m.

Lemma Quarter_positive m : 0<m -> 0<Quarter m.
Proof. destruct m; cbn; lia. Qed.

Lemma Quarter_power m : Quarter m*3+1=4^m.
Proof. induction m; cbn[Quarter Nat.pow]; nia. Qed.

Lemma OddRow_length N d q : length (OddRow N d q)=1+q*4.
Proof. unfold OddRow; rewrite length_app, Cycles_length; cbn; lia. Qed.

Lemma EvenRow_length N d q : length (EvenRow N d q)=3+q*8.
Proof. unfold EvenRow; rewrite length_app, Cycles_length; cbn; lia. Qed.

Lemma OddRow_count N d q v : count_occ Nat.eq_dec (OddRow N d q) v=
  (1+q*2)*mark N v + q*mark d v + q*mark 0 v.
Proof.
  unfold OddRow; rewrite count_occ_app, Cycles_count, !count_cons.
  cbn[count_occ]; nia.
Qed.

Lemma EvenRow_count N d q v : count_occ Nat.eq_dec (EvenRow N d q) v=
  (1+q*4)*mark N v + (1+q*2)*mark d v + (1+q*2)*mark 0 v.
Proof.
  unfold EvenRow; rewrite count_occ_app, Cycles_count, !count_cons.
  cbn[count_occ]; nia.
Qed.

Lemma CertBody_length N m : length (CertBody N m)=m*2.
Proof. induction m; cbn[CertBody]; rewrite ?length_app, ?IHm; cbn[length]; lia. Qed.

Lemma CertBody_balance N m v :
  incoming (CertBody N (1+m)) v +
    Quarter (1+m)*mark (1+m*2) v + (1+Quarter (1+m)*2)*mark (2+m*2) v =
  weighted (CertBody N (1+m)) 1 v +
    Quarter (1+m)*2*mark N v + Quarter (1+m)*mark 0 v + mark (N+1) v.
Proof.
  induction m as [|m IH].
  - cbn[Quarter CertBody Nat.add Nat.mul].
    unfold incoming; cbn[app concat weighted].
    rewrite ?count_occ_app, ?OddRow_count, ?EvenRow_count,
      ?OddRow_length, ?EvenRow_length, ?count_cons; cbn[count_occ].
    cbn[Nat.add Nat.mul Nat.sub]; nia.
  - change (incoming (CertBody N (1+m) ++
      [OddRow N ((1+m)*2-1) (Quarter (1+m));EvenRow N ((1+m)*2) (Quarter (1+m))]) v +
      Quarter (1+(1+m))*mark (1+(1+m)*2) v +
      (1+Quarter (1+(1+m))*2)*mark (2+(1+m)*2) v =
      weighted (CertBody N (1+m) ++
      [OddRow N ((1+m)*2-1) (Quarter (1+m));EvenRow N ((1+m)*2) (Quarter (1+m))]) 1 v +
      Quarter (1+(1+m))*2*mark N v+Quarter (1+(1+m))*mark 0 v+mark (N+1) v).
    unfold incoming in *; rewrite concat_app, count_occ_app, weighted_app, CertBody_length.
    cbn[concat weighted]; rewrite !count_occ_app, OddRow_count, EvenRow_count,
      OddRow_length, EvenRow_length; cbn[count_occ].
    replace ((1+m)*2-1) with (1+m*2) by lia.
    replace ((1+m)*2) with (2+m*2) by lia.
    replace (2+m*2+1) with (1+(2+m*2)) by lia.
    change (Quarter (1+(1+m))) with (1+Quarter (1+m)*4).
    cbn[Nat.add] in *; ring_simplify in IH; ring_simplify; lia.
Qed.

Lemma RootRow_length N m : 0<m -> length (RootRow N m)=Quarter m*2-1.
Proof.
  intro HM; pose proof (Quarter_positive HM).
  unfold RootRow; rewrite length_app, Cycles_length; cbn[length]; lia.
Qed.

Lemma RootRow_count N m v : 0<m -> count_occ Nat.eq_dec (RootRow N m) v=
  Quarter m*mark (N-1) v+(Quarter m-1)*mark 0 v.
Proof.
  intro HM; pose proof (Quarter_positive HM).
  unfold RootRow; rewrite count_occ_app, Cycles_count, !count_cons; cbn[count_occ]; nia.
Qed.

Theorem CertRows_balance m : 0<m -> Balance (CertRows m) (m*2) (m*2+1).
Proof.
  intros HM v; destruct m as [|m]; [lia|].
  pose proof (CertBody_balance ((1+m)*2) m v) as HB.
  unfold CertRows, Balance, incoming; cbn[concat]; rewrite count_occ_app, RootRow_count by lia.
  rewrite <- weighted_outgoing; cbn[weighted]; rewrite RootRow_length by lia.
  replace ((S m)*2) with (2+m*2) in * by lia.
  replace (2+m*2-1) with (1+m*2) by lia.
  change (Quarter (S m)) with (Quarter (1+m)).
  unfold incoming in HB; pose proof (Quarter_positive (m:=1+m) ltac:(lia)).
  cbn[Nat.mul Nat.add] in *.
  replace (m*2+1) with (S (m*2)) in * by lia.
  remember (Quarter (S m)) as q in *; destruct q; [lia|].
  cbn[Nat.mul Nat.add Nat.sub] in *; rewrite ?Nat.sub_0_r in *.
  ring_simplify in HB; ring_simplify; cbn[Nat.add] in *; lia.
Qed.

Lemma CertBody_at N m : forall k, k<m ->
  nth (k*2) (CertBody N m) [] = OddRow N (k*2-1) (Quarter k) /\
  nth (1+k*2) (CertBody N m) [] =
    EvenRow N (match k with 0 => N+1 | _ => k*2 end) (Quarter k).
Proof.
  induction m as [|m IH]; intros k HK; [lia|].
  destruct (Nat.eq_dec k m) as [->|Hne]; cbn[CertBody].
  - rewrite !app_nth2 by (rewrite CertBody_length; lia).
    rewrite CertBody_length, Nat.sub_diag.
    replace (1+m*2-m*2) with 1 by lia; split; reflexivity.
  - rewrite !app_nth1 by (rewrite CertBody_length; lia); apply IH; lia.
Qed.

Definition ExitRank m i :=
  if i =? 0 then m+2 else if i =? m*2+1 then 0 else
  if Nat.odd i then m+1 else i/2.

Lemma ExitRank_root m : ExitRank m 0=m+2.
Proof. reflexivity. Qed.

Lemma ExitRank_sink m : ExitRank m (m*2+1)=0.
Proof.
  unfold ExitRank; assert (E : (m*2+1 =? 0)=false) by (apply Nat.eqb_neq; lia).
  rewrite E, Nat.eqb_refl; reflexivity.
Qed.

Lemma ExitRank_odd m k : k<m -> ExitRank m (1+k*2)=m+1.
Proof.
  intro H; unfold ExitRank; rewrite odd_1.
  assert (E : (1+k*2 =? 0)=false) by (apply Nat.eqb_neq; lia).
  assert (F : (1+k*2 =? m*2+1)=false) by (apply Nat.eqb_neq; lia).
  rewrite E, F; reflexivity.
Qed.

Lemma ExitRank_even m k : 0<k -> k<=m -> ExitRank m (k*2)=k.
Proof.
  intros H K; unfold ExitRank; rewrite odd_0.
  assert (E : (k*2 =? 0)=false) by (apply Nat.eqb_neq; lia).
  assert (F : (k*2 =? m*2+1)=false) by (apply Nat.eqb_neq; lia).
  rewrite E, F, Nat.div_mul by lia; reflexivity.
Qed.

Theorem CertRows_forest m : 0<m -> LastForest (ExitRank m) (CertRows m).
Proof.
  intros HM i Hne.
  assert (HI : i<1+m*2).
  { destruct (Nat.lt_ge_cases i (length (CertRows m))) as [HL|HL].
    - unfold CertRows in HL; cbn[length] in HL; rewrite CertBody_length in HL; lia.
    - rewrite nth_overflow in Hne by lia; contradiction. }
  destruct i as [|i].
  - change (ExitRank m (last (RootRow (m*2) m) 0)<ExitRank m 0).
    unfold RootRow; rewrite last_suffix by discriminate; cbn[last].
    replace (m*2-1) with (1+(m-1)*2) by lia.
    rewrite ExitRank_odd by lia; rewrite ExitRank_root; lia.
  - change (ExitRank m (last (nth i (CertBody (m*2) m) []) 0)<ExitRank m (1+i)).
    destruct (mod2 i) as [k E|k E]; subst i.
    + rewrite (proj1 (CertBody_at (m*2) (m:=m) (k:=k) ltac:(lia))).
      unfold OddRow; rewrite last_suffix by discriminate; cbn[last].
      rewrite ExitRank_even, ExitRank_odd by lia; lia.
    + rewrite (proj2 (CertBody_at (m*2) (m:=m) (k:=k) ltac:(lia))).
      unfold EvenRow; rewrite last_suffix by discriminate; cbn[last].
      replace (1+(1+k*2)) with ((1+k)*2) by lia.
      rewrite ExitRank_even by lia; destruct k as [|k].
      * rewrite ExitRank_sink; lia.
      * rewrite ExitRank_even by lia; lia.
Qed.

Lemma CertBody_budget N m : length (concat (CertBody N m))=Quarter m*4.
Proof.
  induction m; [reflexivity|].
  cbn[CertBody]; rewrite concat_app, length_app, IHm.
  cbn[concat]; rewrite !length_app, OddRow_length, EvenRow_length.
  cbn[length Quarter]; lia.
Qed.

Lemma CertRows_budget m : 0<m -> length (concat (CertRows m))=Quarter m*6-1.
Proof.
  intro HM; unfold CertRows; cbn[concat].
  rewrite length_app, RootRow_length, CertBody_budget by assumption.
  pose proof (Quarter_positive HM); lia.
Qed.

Theorem stack_exit m : 0<m -> exists rows',
  StackWalk (m*2) (CertRows m) (m*2+1) rows' (Quarter m*6-1) /\
  forall i, nth i rows' []=[].
Proof.
  intro HM; pose proof (stack_certificate (CertRows_balance HM) (CertRows_forest HM)) as H.
  rewrite CertRows_budget in H by assumption; exact H.
Qed.

Definition ExitMove N i a j := Move N i a j \/ (i=2 /\ a=2 /\ j=N+1).

Lemma RootRow_rules N m : Indexed (Move N 0) 0 (RootRow N m).
Proof.
  unfold RootRow; change (Indexed (Move N 0) (0*length [N-1;0])
    (Cycles [N-1;0] (Quarter m-1)++[N-1])).
  apply Indexed_cycles; intros a; cbn[length Indexed]; repeat split; constructor.
Qed.

Lemma OddRow_rules N i q : 2<i -> Nat.odd i=true ->
  Indexed (Move N i) 0 (OddRow N (i-2) q).
Proof.
  intros HI HE; unfold OddRow.
  change (Indexed (Move N i) (0*length [N;i-2;N;0]) (Cycles [N;i-2;N;0] q++[N])).
  apply Indexed_cycles; intro a; cbn[length Indexed]; repeat split.
  - replace (a*4) with ((a*2)*2) by lia; apply Move_odd_even; auto; lia.
  - apply Move_odd1; assumption.
  - replace (1+(1+a*4)) with ((1+a*2)*2) by lia; apply Move_odd_even; auto; lia.
  - replace (1+(1+(1+a*4))) with (3+a*4) by lia; apply Move_odd3; auto; lia.
  - replace (a*4) with ((a*2)*2) by lia; apply Move_odd_even; auto; lia.
Qed.

Lemma EvenRow_rules N i q : 2<i -> Nat.odd i=false ->
  Indexed (Move N i) 0 (EvenRow N (i-2) q).
Proof.
  intros HI HE; unfold EvenRow.
  change (Indexed (Move N i) (0*length [0;N;i-2;N])
    (Cycles [0;N;i-2;N] (q*2)++[0;N;i-2])).
  apply Indexed_cycles; intro a; cbn[length Indexed]; repeat split.
  - apply Move_even0; auto; lia.
  - replace (1+a*4) with (1+(a*2)*2) by lia; apply Move_even_odd; auto; lia.
  - replace (1+(1+a*4)) with (2+a*4) by lia; apply Move_even2; assumption.
  - replace (1+(1+(1+a*4))) with (1+(1+a*2)*2) by lia; apply Move_even_odd; auto; lia.
  - apply Move_even0; auto; lia.
  - replace (1+a*4) with (1+(a*2)*2) by lia; apply Move_even_odd; auto; lia.
  - replace (1+(1+a*4)) with (2+a*4) by lia; apply Move_even2; assumption.
Qed.

Lemma CertRows_length m : length (CertRows m)=1+m*2.
Proof. unfold CertRows; cbn[length]; rewrite CertBody_length; reflexivity. Qed.

Lemma CertRows_rules m : 0<m ->
  RowRules (ExitMove (m*2)) (CertRows m) (repeat 0 (1+m*2)).
Proof.
  intro HM; rewrite <- CertRows_length; apply RowRules_initial; intro i.
  destruct (Nat.lt_ge_cases i (length (CertRows m))) as [HI|HI];
    [rewrite CertRows_length in HI|rewrite nth_overflow by lia; exact I].
  destruct i as [|i].
  - change (Indexed (ExitMove (m*2) 0) 0 (RootRow (m*2) m)).
    eapply Indexed_mono; [intros; left; eassumption|apply RootRow_rules].
  - change (Indexed (ExitMove (m*2) (1+i)) 0 (nth i (CertBody (m*2) m) [])).
    destruct (mod2 i) as [k E|k E]; subst i.
    + rewrite (proj1 (CertBody_at (m*2) (m:=m) (k:=k) ltac:(lia))).
      destruct k as [|k].
      * change (ExitMove (m*2) 1 0 (m*2) /\ True).
        split; [left; change (Move (m*2) 1 (0*2) (m*2)); apply Move_odd_even; reflexivity || lia|exact I].
      * replace ((S k)*2-1) with (1+(S k)*2-2) by lia.
        eapply Indexed_mono; [intros; left; eassumption|apply OddRow_rules; [lia|apply odd_1]].
    + rewrite (proj2 (CertBody_at (m*2) (m:=m) (k:=k) ltac:(lia))).
      destruct k as [|k].
      * change (ExitMove (m*2) 2 0 0 /\ ExitMove (m*2) 2 1 (m*2) /\
          ExitMove (m*2) 2 2 (m*2+1) /\ True).
        repeat split.
        -- left; change (Move (m*2) 2 (0*4) 0); apply Move_even0; reflexivity || lia.
        -- left; change (Move (m*2) 2 (1+0*2) (m*2)); apply Move_even_odd; reflexivity || lia.
        -- right; auto.
      * change (Indexed (ExitMove (m*2) (1+(1+(S k)*2))) 0 (EvenRow (m*2) ((S k)*2) (Quarter (S k)))).
        replace ((S k)*2) with ((1+(1+(S k)*2))-2) at 2 by lia.
        eapply Indexed_mono; [intros; left; eassumption|apply EvenRow_rules; [lia|]].
        change (Nat.odd ((2+k)*2)=false); apply odd_0.
Qed.

Lemma Move_functional N i a j : Move N i a j -> forall k, Move N i a k -> j=k.
Proof. intros H k H'; destruct H; inversion H'; subst; try congruence; lia. Qed.

Lemma CertRows_front m : 0<m ->
  nth 1 (CertRows m) []=[m*2] /\ nth 2 (CertRows m) []=[0;m*2;m*2+1].
Proof.
  intro HM; destruct (CertBody_at (m*2) (m:=m) (k:=0) HM) as [H1 H2].
  cbn[Nat.mul Nat.add] in H1, H2.
  change (nth 0 (CertBody (m*2) m) []=[m*2] /\ nth 1 (CertBody (m*2) m) []=[0;m*2;m*2+1]).
  rewrite H1, H2; split; reflexivity.
Qed.

Lemma RowRules_sink m rows xs : RowRules (ExitMove (m*2)) rows xs ->
  VisitBudget (CertRows m) rows xs -> nth (m*2+1) rows []=[].
Proof.
  intros [EL HR] [ES HV]; apply nth_overflow; rewrite CertRows_length in ES; lia.
Qed.

Lemma RowRules_safe m rows xs i : 0<m -> RowRules (ExitMove (m*2)) rows xs ->
  VisitBudget (CertRows m) rows xs -> Balance rows i (m*2+1) -> i<>m*2+1 ->
  nth 1 xs 0<=1 /\ nth 2 xs 0<=2.
Proof.
  intros HM HR HV HF HI; split.
  - pose proof (VisitBudget_bound 1 HV) as HB.
    unfold outgoing in HB; rewrite (proj1 (CertRows_front HM)) in HB; exact HB.
  - pose proof (RowRules_sink HR HV) as HE.
    specialize (HF (m*2+1)); unfold outgoing in HF; rewrite HE, mark_self, mark_other in HF by assumption.
    cbn[length] in HF.
    destruct (incoming_witness rows (m*2+1) ltac:(lia)) as [j [HJ HJ']].
    destruct HR as [EL HR]; destruct HV as [ES HV].
    destruct (Indexed_in (HR j) HJ') as [a [HA [HD|[-> [-> _]]]]]; [|assumption].
    pose proof (Move_bound HD ltac:(rewrite CertRows_length in ES; lia)); lia.
Qed.

Lemma Tick_available m xs u : 0<m -> length xs=m*2 ->
  nth 0 xs 0<=1 -> nth 1 xs 0<=2 ->
  exists ys v, Tick (Alt false (m*2)) true xs u ys v 0.
Proof.
  intros HM EL H1 H2; destruct m as [|m]; [lia|].
  destruct xs as [|a [|b xs]]; cbn[length] in EL; try lia.
  replace ((S m)*2) with (2+m*2) by lia; cbn[Alt].
  apply Tick_front_total; [rewrite Alt_length; lia|exact H1|exact H2].
Qed.

Lemma stack_ticks m i rows j rows' n : 0<m -> StackWalk i rows j rows' n ->
  forall xs u next v a,
  RowRules (ExitMove (m*2)) rows (u::xs) -> VisitBudget (CertRows m) rows (u::xs) ->
  Balance rows i (m*2+1) -> Tick (Alt false (m*2)) true xs u next v 0 ->
  Bump i a (u::xs) (v::next) -> exists ys w,
  Ticks (Alt false (m*2)) true n xs u ys w /\ VisitBudget (CertRows m) rows' (w::ys).
Proof.
  intros HM HW; induction HW as [i rows|i j k rows rows' rows'' n HP HW IH];
    intros xs u next v a HR HV HF HT HB.
  - exists xs,u; split; [constructor|assumption].
  - destruct (RowRules_pop HR HP HB) as [HD HR']; pose proof (VisitBudget_pop HV HP HB) as HV'.
    pose proof (Pop_balance HP HF) as HF'.
    destruct (Nat.eq_dec j (m*2+1)) as [HJ|HJ].
    + pose proof (RowRules_sink HR' HV') as HE; rewrite <- HJ in HE.
      destruct (StackWalk_stuck HW HE) as [EJ [EN ER]]; subst.
      exists next,v; split; [eapply Ticks_cons; [exact HT|constructor]|exact HV'].
    + destruct (RowRules_safe HM HR' HV' HF' HJ) as [H1 H2].
      destruct (Tick_length HT) as [EL EN]; rewrite Alt_length in EL.
      destruct (@Tick_available m next v HM ltac:(lia) H1 H2) as [next' [v' HT']].
      destruct (Tick_route_even HM HT HT' HB) as [j' [a' [HD' HB']]].
      destruct HD as [HD|[_ [_ HE]]]; [|contradiction].
      pose proof (Move_functional HD HD') as ->.
      destruct (IH next v next' v' a' HR' HV' HF' HT' HB') as [ys [w [HX HY]]].
      exists ys,w; split; [eapply Ticks_cons; eassumption|assumption].
Qed.

Theorem canonical_exit m : 0<m -> exists xs u,
  Ticks (Alt false (m*2)) true (Quarter m*6-1) (repeat 0 (m*2)) 0 xs u /\
  u::xs=map (@length nat) (CertRows m) /\
  Lives Edge retire ((Quarter m*6-1)*2) (true::Word (repeat 0 (m*2)) 0) [0]
    (true::Word xs u) [0].
Proof.
  intro HM; destruct (stack_exit HM) as [rows' [HW HE]].
  destruct (@Tick_available m (repeat 0 (m*2)) 0 HM ltac:(rewrite repeat_length; reflexivity)
    ltac:(rewrite nth_repeat; lia) ltac:(rewrite nth_repeat; lia)) as [next [v HT]].
  pose proof (Tick_initial_bump m HT) as HB.
  pose proof (CertRows_rules HM) as HR.
  pose proof (VisitBudget_initial (CertRows m)) as HV; rewrite CertRows_length in HV.
  destruct (@stack_ticks m (m*2) (CertRows m) (m*2+1) rows' (Quarter m*6-1)
    HM HW (repeat 0 (m*2)) 0 next v 0 HR HV (CertRows_balance HM) HT HB) as [xs [u [HX HY]]].
  exists xs,u; split; [exact HX|split; [eapply VisitBudget_done; eassumption|]].
  apply (Ticks_lives m); exact HX.
Qed.

Theorem seed_exit n : exists xs u,
  Ticks (Alt false (14+n*2)) true (Quarter (7+n)*6-1-(7+n))
    (repeat 0 (14+n*2)) (7+n) xs u /\
  u::xs=map (@length nat) (CertRows (7+n)) /\
  Lives Edge retire ((Quarter (7+n)*6-1-(7+n))*2)
    (true::Word (repeat 0 (14+n*2)) (7+n)) [0] (true::Word xs u) [0].
Proof.
  destruct (seed_absorption n) as [t [mid [root [Ht [HR [HP HL]]]]]].
  destruct (@canonical_exit (7+n) ltac:(lia)) as [xs [u [HC [HE _]]]].
  replace ((7+n)*2) with (14+n*2) in HC by lia.
  destruct (Box_total (6+n)) as [bounds [h HB]].
  pose proof (Box_capacity HB) as EC; pose proof (Box_budget HB) as EB.
  pose proof (Quarter_power (7+n)) as EQ.
  replace (1+(6+n)) with (7+n) in EC by lia.
  assert (Ht' : t+(7+n)<=Quarter (7+n)*6-1) by nia.
  eapply Ticks_suffix with (k:=t+(7+n)) in HC; [|exact Ht'|exact HP].
  assert (HX : Ticks (Alt false (14+n*2)) true (Quarter (7+n)*6-1-(7+n))
      (repeat 0 (14+n*2)) (7+n) xs u).
  { replace (Quarter (7+n)*6-1-(7+n)) with (t+(Quarter (7+n)*6-1-(t+(7+n)))) by lia.
    eapply Ticks_app; eassumption. }
  exists xs,u; split; [exact HX|split; [exact HE|apply (Ticks_lives (7+n)); exact HX]].
Qed.

(* The exported endpoint uses a linear-length counter list, not the logical
   exponential-length lists of destinations used by the exit certificate. *)
Fixpoint ExitBody m : list nat := match m with
  | 0 => [] | S k => ExitBody k ++ [1+Quarter k*4;3+Quarter k*8] end.
Definition ExitWord m := Word (ExitBody m) (Quarter m*2-1).

Lemma CertBody_visits N m : map (@length nat) (CertBody N m)=ExitBody m.
Proof.
  induction m; [reflexivity|].
  cbn[CertBody ExitBody]; rewrite map_app, IHm.
  cbn[map]; rewrite OddRow_length, EvenRow_length; reflexivity.
Qed.

Lemma CertRows_visits m : 0<m ->
  map (@length nat) (CertRows m)=(Quarter m*2-1)::ExitBody m.
Proof. intro H; unfold CertRows; cbn[map]; rewrite RootRow_length, CertBody_visits by assumption; reflexivity. Qed.

Corollary seed_exit_lives n :
  Lives Edge retire ((Quarter (7+n)*6-1-(7+n))*2)
    (true::Word (repeat 0 (14+n*2)) (7+n)) [0] (true::ExitWord (7+n)) [0].
Proof.
  destruct (seed_exit n) as [xs [u [_ [HE HL]]]].
  rewrite CertRows_visits in HE by lia; inversion HE; subst; exact HL.
Qed.

Fixpoint PairNums k n : list nat := match n with
  | 0 => [] | S n => Quarter (1+k)::(1+Quarter (1+k)*2)::PairNums (1+k) n end.

Lemma PairNums_snoc n : forall k, PairNums k (n+1)=PairNums k n ++
  [Quarter (1+(k+n));1+Quarter (1+(k+n))*2].
Proof.
  induction n; intro k; cbn[Nat.add PairNums]; [rewrite Nat.add_0_r; reflexivity|].
  rewrite IHn, Nat.add_succ_r; cbn[Nat.add app]; reflexivity.
Qed.

Lemma ExitBody_pairs m : ExitBody m=PairNums 0 m.
Proof.
  induction m; [reflexivity|].
  cbn[ExitBody]; rewrite IHm; replace (S m) with (m+1) by lia.
  rewrite PairNums_snoc; cbn[Nat.add Quarter].
  f_equal; f_equal; f_equal; lia.
Qed.

Lemma Quarter_odd k : Nat.odd (Quarter (1+k))=true.
Proof.
  replace (Quarter (1+k)) with (1+(Quarter k*2)*2) by (cbn[Nat.add Quarter]; lia); apply odd_1.
Qed.

Lemma CWord_pairs n : forall k u,
  CWord true (4^k*2) (1+Quarter k*2) (PairNums k n) u =
  Doubles (4^k*4) n ++ Alt false (4^(k+n)*2+1+Quarter (k+n)*2+u*2).
Proof.
  induction n; intros k u.
  - cbn[PairNums CWord Doubles]; rewrite odd_1, Nat.add_0_r; cbn[xorb app]; f_equal; lia.
  - cbn[PairNums CWord]; rewrite !odd_1, Quarter_odd; cbn[xorb negb].
    replace (4^k*2*2*2) with (4^(1+k)*2) by (cbn[Nat.add Nat.pow]; lia).
    rewrite IHn; replace (k+S n) with (1+k+n) by lia.
    cbn[Doubles].
    replace (4^k*4*4) with (4^(1+k)*4) by (cbn[Nat.add Nat.pow]; lia).
    pose proof (Quarter_power k) as E1; pose proof (Quarter_power (1+k)) as E2.
    cbn[Nat.add Nat.pow] in E2.
    replace (4^k*2+(1+Quarter k*2)+Quarter (1+k)) with (4^k*4)
      by (cbn[Nat.add Quarter]; lia).
    replace (4^k*2*2+Quarter (1+k)+(1+Quarter (1+k)*2)) with (4^k*4*2) by (cbn[Nat.add]; lia).
    rewrite !app_assoc; reflexivity.
Qed.

Lemma SwitchWord_shape m : 0<m ->
  CWord true 2 1 (ExitBody m) (Quarter m*2-1) =
  Doubles 4 m ++ Alt false (4^m*4-3).
Proof.
  intro HM; rewrite ExitBody_pairs.
  change (CWord true (4^0*2) (1+Quarter 0*2) (PairNums 0 m) (Quarter m*2-1)=
    Doubles 4 m ++ Alt false (4^m*4-3)).
  rewrite CWord_pairs; cbn[Nat.pow Nat.add Quarter].
  pose proof (Quarter_power m) as E.
  pose proof (Quarter_positive HM); f_equal; f_equal; lia.
Qed.

Lemma ExitWord_shape n : ExitWord (1+n)=
  Alt true 3 ++ Alt true 8 ++ Doubles 16 n ++ Alt false (4^(1+n)*4-3).
Proof.
  pose proof (@SwitchWord_shape (1+n) ltac:(lia)) as H.
  rewrite ExitBody_pairs in H; cbn[Nat.add PairNums Quarter CWord Doubles Nat.pow] in H.
  rewrite <- app_assoc in H.
  change (Alt false 4 ++ CWord false 4 1 (3::PairNums 1 n) (Quarter (1+n)*2-1)=
    Alt false 4 ++ (Alt true 8 ++ Doubles 16 n ++ Alt false (4^(1+n)*4-3))) in H.
  apply app_inv_head in H.
  unfold ExitWord, Word; rewrite ExitBody_pairs.
  change (Alt true 3 ++ CWord false 4 1 (3::PairNums 1 n) (Quarter (1+n)*2-1)=
    Alt true 3 ++ Alt true 8 ++ Doubles 16 n ++ Alt false (4^(1+n)*4-3)).
  rewrite H; reflexivity.
Qed.

Definition SWord m := Alt true 2 ++ Doubles 4 m ++ Alt false (4^m*4-3).
Definition MidWord n := Alt true 4 ++ Doubles 8 n ++
  Alt false (4^(1+n)*2-1) ++ Alt false (4^(1+n)*4-1).

Lemma parent_exit_pass n :
  Pass (Alt true 8 ++ Doubles 16 n ++ Alt false (4^n*16-3)) 4 (4^n*16-2)
    (Alt true 4 ++ Doubles 8 n ++ Alt false (4^n*8-1)).
Proof.
  assert (HP : 4^n<>0) by (apply Nat.pow_nonzero; lia).
  eapply Pass_cat; [apply (@Pass_alt_even true 4 4); auto|].
  eapply Pass_cat with (b:=4^n*8).
  - applys_eq (@Pass_Doubles n 8 8 ltac:(lia) ltac:(lia) eq_refl eq_refl); flia.
  - pose proof (@Pass_alt_odd_I (4^n*8-2) (4^n*8) ltac:(lia)) as H.
    rewrite Nat.odd_mul in H; change (Nat.odd 8) with false in H; rewrite andb_false_r in H.
    applys_eq H; flia.
Qed.

Lemma internal_exit_pass n :
  Pass (MidWord n) 0 (4^n*16-4)
    (Alt true 2 ++ Doubles 4 n ++ Alt false (4^n*4) ++ Alt true (4^n*8)).
Proof.
  assert (HP : 4^n<>0) by (apply Nat.pow_nonzero; lia).
  unfold MidWord; cbn[Nat.add Nat.pow].
  replace (4*4^n*2) with (4^n*8) by lia; replace (4*4^n*4) with (4^n*16) by lia.
  eapply Pass_cat; [apply (@Pass_alt_even true 2 0); auto|].
  eapply Pass_cat with (b:=4^n*4-2).
  - applys_eq (@Pass_Doubles n 4 2 ltac:(lia) ltac:(lia) eq_refl eq_refl); flia.
  - eapply Pass_cat with (b:=4^n*8-3).
    + pose proof (@Pass_alt_odd_I (4^n*4-1) (4^n*4-2) ltac:(lia)) as H.
      assert (E : Nat.odd (4^n*4-2)=false).
      { replace (4^n*4-2) with ((4^n*2-1)*2) by lia; apply odd_0. }
      rewrite E in H; applys_eq H; flia.
    + pose proof (@Pass_alt_odd_I (4^n*8-1) (4^n*8-3) ltac:(lia)) as H.
      assert (E : Nat.odd (4^n*8-3)=true).
      { replace (4^n*8-3) with (1+(4^n*4-2)*2) by lia; apply odd_1. }
      rewrite E in H; applys_eq H; flia.
Qed.

Lemma parent_exit_column n :
  Flow_Life Edge retire (true::ExitWord (1+n)) [0] (MidWord n) [0;0].
Proof.
  assert (HP : 4^n<>0) by (apply Nat.pow_nonzero; lia).
  assert (ER : retire (4^n*16-2)=Alt false (4^n*16-1)).
  { unfold retire; replace (4^n*16-2) with ((4^n*8-1)*2) by lia.
    rewrite odd_0; f_equal; lia. }
  rewrite ExitWord_shape; unfold MidWord; cbn[Nat.add Nat.pow].
  replace (4*4^n*2) with (4^n*8) by lia; replace (4*4^n*4) with (4^n*16) by lia.
  rewrite <- ER; rewrite !app_assoc.
  eapply Life_terminal with (k:=2) (b:=3); [apply (Edge_even 1)|].
  apply Pass_P; pose proof (parent_exit_pass n) as H; rewrite !app_assoc in H; exact H.
Qed.

Lemma internal_exit_column n :
  Flow_Life Edge retire (MidWord n) [0;0] (SWord (1+n)) [0].
Proof.
  assert (HP : 4^n<>0) by (apply Nat.pow_nonzero; lia).
  assert (ER : retire (4^n*16-4)=Alt false (4^n*16-3)).
  { unfold retire; replace (4^n*16-4) with ((4^n*8-2)*2) by lia.
    rewrite odd_0; f_equal; lia. }
  unfold SWord; replace (1+n) with (n+1) by lia; rewrite Doubles_snoc.
  replace (4^(n+1)*4) with (4^n*16) by (rewrite Nat.pow_add_r; cbn; lia).
  replace (4*4^n) with (4^n*4) by lia.
  replace (4^n*4*2) with (4^n*8) by lia.
  rewrite <- ER; rewrite !app_assoc.
  eapply Life_internal; [discriminate|].
  pose proof (internal_exit_pass n) as H; rewrite !app_assoc in H; exact H.
Qed.

Theorem exit_boundary n : Lives Edge retire 2
  (true::ExitWord (1+n)) [0] (SWord (1+n)) [0].
Proof.
  eapply Lives_cons; [apply parent_exit_column|].
  eapply Lives_cons; [apply internal_exit_column|constructor].
Qed.

Corollary seed_to_single n : Lives Edge retire ((Quarter (7+n)*6-(7+n))*2)
  (true::Word (repeat 0 (14+n*2)) (7+n)) [0] (SWord (7+n)) [0].
Proof.
  pose proof (seed_exit_lives n) as H; pose proof (exit_boundary (6+n)) as H'.
  assert (HQ : 7+n<Quarter (7+n)*6).
  { pose proof (Quarter_power (7+n)); destruct (Box_total (6+n)) as [xs [h HB]].
    pose proof (Box_capacity HB); pose proof (Box_budget HB); cbn[Nat.add] in *; nia. }
  replace ((Quarter (7+n)*6-(7+n))*2) with (((Quarter (7+n)*6-1-(7+n))*2)+2) by lia.
  eapply Lives_app; [exact H|exact H'].
Qed.

(* A regular single-column counter. The Boolean index is the current block
   phase; the list stores following phases, most significant first. *)
Inductive Num : bool -> nat -> list bool -> list bool -> Prop :=
| Num_nil0 a : Num false a [] (Alt false (1+a*2))
| Num_nil1 a : Num true a [] (Alt true (2+a*2))
| Num_00 a bits w : Num false (a*2) bits w ->
    Num false a (false::bits) (Alt false (1+a*2)++w)
| Num_01 a bits w : Num true (1+a*2) bits w ->
    Num false a (true::bits) (Alt false (2+a*2)++w)
| Num_10 a bits w : Num false (1+a*2) bits w ->
    Num true a (false::bits) (Alt true (2+a*2)++w)
| Num_11 a bits w : Num true (2+a*2) bits w ->
    Num true a (true::bits) (Alt true (3+a*2)++w).

(* The marker is after [bits]; the [n] less significant phases are all I. *)
Inductive Carry : bool -> nat -> list bool -> nat -> list bool -> Prop :=
| Carry_here0 a n : Carry false a [] n
    (Alt false (3+a*2)++Ladder false ((3+a*2)*2) n)
| Carry_here1 a n : Carry true a [] n
    (Alt true (4+a*2)++Ladder false ((4+a*2)*2) n)
| Carry_00 a bits n w : Carry false (a*2) bits n w ->
    Carry false a (false::bits) n (Alt false (1+a*2)++w)
| Carry_01 a bits n w : Carry true (1+a*2) bits n w ->
    Carry false a (true::bits) n (Alt false (2+a*2)++w)
| Carry_10 a bits n w : Carry false (1+a*2) bits n w ->
    Carry true a (false::bits) n (Alt true (2+a*2)++w)
| Carry_11 a bits n w : Carry true (2+a*2) bits n w ->
    Carry true a (true::bits) n (Alt true (3+a*2)++w).

Lemma Num_zeros0 n : forall a, Num false a (repeat false n) (Ladder false (a*2) (1+n)).
Proof.
  induction n; intro a.
  - cbn[Ladder Nat.add]; rewrite app_nil_r; constructor.
  - change (Num false a (false::repeat false n)
      (Alt false (1+a*2)++Ladder false (a*2*2) (1+n))).
    apply Num_00; apply IHn.
Qed.

Lemma Num_zeros1 n : forall a, Num true a (repeat false n)
  (Alt true (2+a*2)++Ladder false (2+a*4) n).
Proof.
  destruct n; intro a; [cbn[Ladder repeat]; rewrite app_nil_r; constructor|].
  apply Num_10; replace (2+a*4) with ((1+a*2)*2) by lia; apply Num_zeros0.
Qed.

Lemma Carry_here0_pass a n : exists A o w,
  Num true (1+a) (repeat false n) w /\
  Pass (Alt false (3+a*2)++Ladder false ((3+a*2)*2) n) (a+2) A o /\
  o++retire A=Alt (Nat.odd a) (2+a)++w.
Proof.
  destruct (Pass_ladder_return n (t:=3+a*2) ltac:(lia)) as [A [o [HT HE]]].
  exists A,(Alt (Nat.odd a) (2+a)++o),
    (Alt true (4+a*2)++Ladder false ((3+a*2)*2) n); split.
  - applys_eq (Num_zeros1 n (1+a)); flia.
  - split.
    + eapply Pass_cat; [|exact HT].
      pose proof (@Pass_alt_odd_I (1+a) (a+2) ltac:(lia)) as H.
      rewrite Nat.odd_add in H; change (Nat.odd 2) with false in H; rewrite xorb_false_r in H.
      applys_eq H; flia.
    + unfold retire; rewrite <- app_assoc, HE.
      replace (3+a*2) with (1+(1+a)*2) at 1 by lia; rewrite odd_1.
      f_equal; f_equal; flia.
Qed.

Lemma Carry_here1_pass a n : exists A o,
  Pass (Alt true (4+a*2)++Ladder false ((4+a*2)*2) n) (a+2) A o /\
  o++retire A=Alt (negb (Nat.odd a)) (2+a)++Ladder false ((2+a)*2) (1+n).
Proof.
  destruct (Pass_ladder_return n (t:=4+a*2) ltac:(lia)) as [A [o [HT HE]]].
  exists A,(Alt (negb (Nat.odd a)) (2+a)++o); split.
  - eapply Pass_cat; [|exact HT].
    pose proof (@Pass_alt_even true (2+a) (a+2) (or_intror eq_refl)) as H.
    rewrite Nat.odd_add in H; change (Nat.odd 2) with false in H.
    rewrite xorb_false_r, xorb_true_r in H; applys_eq H; flia.
  - unfold retire; rewrite <- app_assoc, HE.
    replace (4+a*2) with ((2+a)*2) at 1 by lia; rewrite odd_0.
    cbn[Nat.add Ladder]; f_equal; f_equal; flia.
Qed.

Lemma Pass_num00 a : Pass (Alt false (1+a*2)) (a+2) (a*2+2)
  (Alt (xorb (Nat.odd a) false) (1+a)).
Proof.
  pose proof (@Pass_alt_odd_I a (a+2) ltac:(lia)) as H.
  rewrite Nat.odd_add in H; change (Nat.odd 2) with false in H.
  rewrite xorb_false_r in *; applys_eq H; flia.
Qed.

Lemma Pass_num01 a : Pass (Alt false (2+a*2)) (a+2) (1+a*2+2)
  (Alt (xorb (Nat.odd a) false) (1+a)).
Proof.
  pose proof (@Pass_alt_even false (1+a) (a+2) ltac:(left; lia)) as H.
  rewrite Nat.odd_add in H; change (Nat.odd 2) with false in H.
  rewrite !xorb_false_r in *; applys_eq H; flia.
Qed.

Lemma Pass_num10 a : Pass (Alt true (2+a*2)) (a+2) (1+a*2+2)
  (Alt (xorb (Nat.odd a) true) (1+a)).
Proof.
  pose proof (@Pass_alt_even true (1+a) (a+2) (or_intror eq_refl)) as H.
  rewrite Nat.odd_add in H; change (Nat.odd 2) with false in H.
  rewrite xorb_false_r in H; applys_eq H; flia.
Qed.

Lemma Pass_num11 a : Pass (Alt true (3+a*2)) (a+2) (2+a*2+2)
  (Alt (xorb (Nat.odd a) true) (1+a)).
Proof.
  pose proof (@Pass_alt_odd_P (1+a) (a+2)) as H.
  rewrite Nat.odd_add in H; change (Nat.odd 2) with false in H; rewrite xorb_false_r in H.
  rewrite xorb_true_r; applys_eq H; flia.
Qed.

Lemma Num_pass p a bits w : Num p a bits w -> exists A o cw,
  Carry p a bits 0 cw /\ Pass w (a+2) A o /\
  o++retire A=Alt (xorb (Nat.odd a) p) (1+a)++cw.
Proof.
  intro H; induction H.
  { exists (a*2+2), (Alt (xorb (Nat.odd a) false) (1+a)),
      (Alt false (3+a*2)++Ladder false ((3+a*2)*2) 0).
    split; [constructor|split; [apply Pass_num00|]].
    unfold retire; replace (a*2+2) with ((1+a)*2) by lia.
    rewrite odd_0; cbn[Ladder]; rewrite app_nil_r; f_equal; f_equal; lia. }
  { exists (1+a*2+2), (Alt (xorb (Nat.odd a) true) (1+a)),
      (Alt true (4+a*2)++Ladder false ((4+a*2)*2) 0).
    split; [constructor|split; [apply Pass_num10|]].
    unfold retire; replace (1+a*2+2) with (1+(1+a)*2) by lia.
    rewrite odd_1; cbn[Ladder]; rewrite app_nil_r; f_equal; f_equal; lia. }
  all: destruct IHNum as [A [o [cw [HC [HP HE]]]]].
  all: eexists A,_,_; split; [eauto using Carry_00, Carry_01, Carry_10, Carry_11|].
  all: split; [eapply Pass_cat; [first [apply Pass_num00 | apply Pass_num01 |
      apply Pass_num10 | apply Pass_num11] | exact HP]|].
  all: rewrite <- app_assoc, HE; cbn[Nat.add];
    repeat rewrite ?odd_0, ?odd_1; try reflexivity.
  rewrite !odd_S, odd_0; reflexivity.
Qed.

Lemma Carry_zero_here p a n w : Carry p a [false] n w -> exists A o w',
  Num p a (true::repeat false n) w' /\ Pass w (a+2) A o /\
  o++retire A=Alt (xorb (Nat.odd a) p) (1+a)++w'.
Proof.
  intro H; inversion H; subst;
    match goal with H : Carry false ?b [] n _ |- _ =>
      inversion H; subst; destruct (Carry_here0_pass b n) as [A [o [w' [HN [HP HE]]]]]
    end.
  all: eexists A,_,_; split; [econstructor; applys_eq HN; flia|].
  all: split; [eapply Pass_cat; [first [apply Pass_num00 | apply Pass_num10] | exact HP]|].
  all: rewrite <- app_assoc, HE; rewrite ?odd_0, ?odd_1; reflexivity.
Qed.

Lemma Carry_one_here p a n w : Carry p a [true] n w -> exists A o w',
  Carry p a [] (1+n) w' /\ Pass w (a+2) A o /\
  o++retire A=Alt (xorb (Nat.odd a) p) (1+a)++w'.
Proof.
  intro H; inversion H; subst;
    match goal with H : Carry true ?b [] n _ |- _ =>
      inversion H; subst; destruct (Carry_here1_pass b n) as [A [o [HP HE]]]
    end.
  all: eexists A,_,_; split; [constructor|].
  all: split; [eapply Pass_cat; [first [apply Pass_num01 | apply Pass_num11] | exact HP]|].
  all: rewrite <- app_assoc, HE; rewrite ?odd_1; cbn[Nat.add].
  { reflexivity. }
  rewrite !odd_S, odd_0; cbn[negb].
  f_equal; f_equal; flia.
Qed.

Lemma Carry_zero_pass bs : forall p a n w, Carry p a (bs++[false]) n w -> exists A o w',
  Num p a (bs++true::repeat false n) w' /\ Pass w (a+2) A o /\
  o++retire A=Alt (xorb (Nat.odd a) p) (1+a)++w'.
Proof.
  induction bs as [|q bs IH]; intros p a n w H; [apply Carry_zero_here; exact H|].
  cbn in H; inversion H; subst;
    match goal with H : Carry ?p ?b (bs++[false]) n ?w |- _ =>
      destruct (IH p b n w H) as [A [o [w' [HN [HP HE]]]]]
    end.
  all: eexists A,_,_; split; [econstructor; exact HN|].
  all: split; [eapply Pass_cat; [first [apply Pass_num00 | apply Pass_num01 |
      apply Pass_num10 | apply Pass_num11] | exact HP]|].
  all: rewrite <- app_assoc, HE; cbn[Nat.add];
    repeat rewrite ?odd_0, ?odd_1; try reflexivity.
  rewrite !odd_S, odd_0; reflexivity.
Qed.

Lemma Carry_one_pass bs : forall p a n w, Carry p a (bs++[true]) n w -> exists A o w',
  Carry p a bs (1+n) w' /\ Pass w (a+2) A o /\
  o++retire A=Alt (xorb (Nat.odd a) p) (1+a)++w'.
Proof.
  induction bs as [|q bs IH]; intros p a n w H; [apply Carry_one_here; exact H|].
  cbn in H; inversion H; subst;
    match goal with H : Carry ?p ?b (bs++[true]) n ?w |- _ =>
      destruct (IH p b n w H) as [A [o [w' [HC [HP HE]]]]]
    end.
  all: eexists A,_,_; split; [econstructor; exact HC|].
  all: split; [eapply Pass_cat; [first [apply Pass_num00 | apply Pass_num01 |
      apply Pass_num10 | apply Pass_num11] | exact HP]|].
  all: rewrite <- app_assoc, HE; cbn[Nat.add];
    repeat rewrite ?odd_0, ?odd_1; try reflexivity.
  rewrite !odd_S, odd_0; reflexivity.
Qed.

(* The first PI creates one child. Starting Pass at 2 has exactly the same
   continuation at 3, but emits one extra P; remove that synthetic output. *)
Lemma Pass_terminal2 u A o w : Pass (true::false::u) 2 A o ->
  o++retire A=true::w -> Life Edge retire (true::false::u) [0] w [0].
Proof.
  intros H E; inversion H; subst.
  match goal with H : Pass (false::u) _ _ _ |- _ => inversion H; subst end.
  cbn in E; injection E as E; subst w.
  change (Life Edge retire (repeat true 1++false::u) [0] (o0++retire A) [0]).
  eapply Life_terminal; [exact (Edge_odd 0)|assumption].
Qed.

Lemma Num_PI bits w : Num true 0 bits w -> exists u, w=true::false::u.
Proof. intro H; inversion H; subst; cbn[Nat.mul Nat.add Alt app]; eauto. Qed.

Lemma Carry_PI bits n w : Carry true 0 bits n w -> exists u, w=true::false::u.
Proof. intro H; inversion H; subst; cbn[Nat.mul Nat.add Alt app]; eauto. Qed.

Lemma Num_life bits w : Num true 0 bits w -> exists w',
  Carry true 0 bits 0 w' /\ Life Edge retire w [0] w' [0].
Proof.
  intro H; destruct (Num_pass H) as [A [o [w' [HC [HP HE]]]]].
  exists w'; split; [exact HC|].
  destruct (Num_PI H) as [u ->]; eapply Pass_terminal2; eassumption.
Qed.

Lemma Carry_zero_life bs n w : Carry true 0 (bs++[false]) n w -> exists w',
  Num true 0 (bs++true::repeat false n) w' /\ Life Edge retire w [0] w' [0].
Proof.
  intro H; destruct (Carry_zero_pass bs H) as [A [o [w' [HN [HP HE]]]]].
  exists w'; split; [exact HN|].
  destruct (Carry_PI H) as [u ->]; eapply Pass_terminal2; eassumption.
Qed.

Lemma Carry_one_life bs n w : Carry true 0 (bs++[true]) n w -> exists w',
  Carry true 0 bs (1+n) w' /\ Life Edge retire w [0] w' [0].
Proof.
  intro H; destruct (Carry_one_pass bs H) as [A [o [w' [HC [HP HE]]]]].
  exists w'; split; [exact HC|].
  destruct (Carry_PI H) as [u ->]; eapply Pass_terminal2; eassumption.
Qed.

Definition EWord n := false::Ladder false 4 n.

Lemma Carry_exit n w : Carry true 0 [] n w -> Life Edge retire w [0] (EWord (1+n)) [0].
Proof.
  intro H; inversion H; subst.
  destruct (Carry_here1_pass 0 n) as [A [o [HP HE]]].
  eapply Pass_terminal2; [exact HP|exact HE].
Qed.

Fixpoint BVal (bs:list bool) : nat := match bs with
  | [] => 0 | p::bs => (if p then 2^length bs else 0)+BVal bs end.

Lemma BVal_bound bs : BVal bs<2^length bs.
Proof. induction bs as [|p bs IH]; cbn[BVal length Nat.pow]; [lia|destruct p; lia]. Qed.

Lemma BVal_app bs cs : BVal (bs++cs)=BVal bs*2^length cs+BVal cs.
Proof.
  induction bs as [|p bs IH]; [reflexivity|].
  cbn[BVal app]; rewrite length_app, Nat.pow_add_r, IH; destruct p; cbn; nia.
Qed.

Lemma BVal_zeros n : BVal (repeat false n)=0.
Proof. induction n; cbn; assumption || reflexivity. Qed.

Lemma BVal_carry_zero bs n :
  BVal (bs++true::repeat false n)=(1+BVal (bs++[false]))*2^n.
Proof.
  rewrite !BVal_app; cbn[BVal length]; rewrite repeat_length, BVal_zeros.
  cbn[Nat.pow]; ring.
Qed.

Lemma BVal_carry_one bs n :
  (1+BVal (bs++[true]))*2^n=(1+BVal bs)*2^(1+n).
Proof. rewrite BVal_app; cbn[BVal length Nat.add Nat.pow]; ring. Qed.

(* The major component counts pending increments. In Carry, bits already
   traversed are zero, and only the prefix length can decrease at fixed value. *)
Inductive Single r : nat -> list bool -> Prop :=
| Single_num bs w : length bs=r -> Num true 0 bs w ->
    Single r ((2^r-BVal bs)*(r+2)) w
| Single_carry bs n w : length bs+n=r -> Carry true 0 bs n w ->
    Single r ((2^r-(1+BVal bs)*2^n)*(r+2)+length bs+1) w.

Lemma Single_step r k w : Single r k w ->
  Life Edge retire w [0] (EWord (1+r)) [0] \/
  exists k' w', k'<k /\ Single r k' w' /\ Life Edge retire w [0] w' [0].
Proof.
  intro H; destruct H as [bs w Hr HN | bs n w Hr HC].
  - destruct (Num_life HN) as [w' [HC HL]].
    right; eexists _,w'; split; [|split; [eapply Single_carry; [|exact HC]; lia|exact HL]].
    pose proof (BVal_bound bs) as HB; rewrite Hr in HB.
    cbn[Nat.pow]; rewrite Nat.mul_1_r; nia.
  - assert (E : bs=[] \/ exists cs p, bs=cs++[p]).
    { induction bs using rev_ind; eauto. }
    destruct E as [->|[cs [p ->]]].
    + left; cbn in Hr; subst r; apply Carry_exit; exact HC.
    + destruct p.
      * destruct (Carry_one_life cs HC) as [w' [HC' HL]].
        right; eexists _,w'; split;
          [|split; [eapply Single_carry; [|exact HC']; rewrite length_app in Hr; cbn in Hr; lia|exact HL]].
        rewrite BVal_carry_one, length_app; cbn[length]; lia.
      * destruct (Carry_zero_life cs HC) as [w' [HN HL]].
        right; eexists _,w'; split;
          [|split; [eapply Single_num; [|exact HN]; rewrite length_app in *; cbn[length]; rewrite repeat_length; cbn in Hr; lia|exact HL]].
        rewrite BVal_carry_zero, length_app; cbn[length]; lia.
Qed.

Lemma Single_exit r k : forall w, Single r k w ->
  exists t, Lives Edge retire (1+t) w [0] (EWord (1+r)) [0].
Proof.
  induction k using lt_wf_ind; intros w HS.
  destruct (Single_step HS) as [HL|[k' [w' [Hk [HS' HL]]]]].
  - exists 0; econstructor; [exact HL|constructor].
  - destruct (H k' Hk w' HS') as [t HT].
    exists (1+t); econstructor; eassumption.
Qed.

Theorem Num_exit bs w : Num true 0 bs w ->
  exists t, Lives Edge retire (1+t) w [0] (EWord (1+length bs)) [0].
Proof. intro H; eapply Single_exit, Single_num; [|exact H]; reflexivity. Qed.

Lemma Pass_even_odd p k a : Pass (Alt p (k*2)) (1+a*2) (1+a*2+k) (Alt (negb p) k).
Proof.
  pose proof (@Pass_alt_even p k (1+a*2) ltac:(left; lia)) as H.
  rewrite odd_1 in H; destruct p; exact H.
Qed.

Lemma Pass_even_positive p k a : Pass (Alt p (k*2)) (2+a*2) (2+a*2+k) (Alt p k).
Proof.
  pose proof (@Pass_alt_even p k (2+a*2) ltac:(left; lia)) as H.
  replace (2+a*2) with ((1+a)*2) in H by lia; rewrite odd_0 in H.
  applys_eq H; destruct p; flia.
Qed.

Lemma Pass_odd_I_odd k a :
  Pass (Alt false (1+k*2)) (1+a*2) (1+a*2+k) (Alt true (1+k)).
Proof.
  pose proof (@Pass_alt_odd_I k (1+a*2) ltac:(lia)) as H; rewrite odd_1 in H; exact H.
Qed.

Lemma Pass_odd_P_odd k a :
  Pass (Alt true (1+k*2)) (1+a*2) (2+a*2+k) (Alt false k).
Proof.
  pose proof (@Pass_alt_odd_P k (1+a*2)) as H; rewrite odd_1 in H.
  applys_eq H; flia.
Qed.

Definition Entry0 a := Alt true (2+a*2) ++ Alt false (4+a*4) ++
  Alt true (8+a*8) ++ Alt false (13+a*16).
Definition Entry1 a := Alt true (2+a*2) ++ Alt false (4+a*4) ++
  Alt true (7+a*8) ++ Alt true (16+a*16).
Definition Entry2 a := Alt true (2+a*2) ++ Alt false (3+a*4) ++
  Alt false (8+a*8) ++ Alt true (18+a*16).
Definition Entry3 a := Alt true (2+a*2) ++ Alt false (4+a*4) ++
  Alt true (9+a*8) ++ Alt true (18+a*16).

Lemma Entry01 a : exists A o, Pass (Entry0 a) (a+2) A o /\
  o++retire A=Alt (negb (Nat.odd a)) (1+a)++Entry1 a.
Proof.
  exists (15+a*16), (Alt (negb (Nat.odd a)) (1+a) ++ Alt true (2+a*2) ++
    Alt false (4+a*4) ++ Alt true (7+a*8)); split.
  - unfold Entry0; eapply Pass_cat; [rewrite <- xorb_true_r; apply Pass_num10|].
    eapply Pass_cat with (b:=5+a*4).
    + applys_eq (@Pass_even_odd false (2+a*2) (1+a)); flia.
    + eapply Pass_cat with (b:=9+a*8).
      * applys_eq (@Pass_even_odd true (4+a*4) (2+a*2)); flia.
      * applys_eq (Pass_odd_I_odd (6+a*8) (4+a*4)); flia.
  - unfold retire, Entry1; replace (15+a*16) with (1+(7+a*8)*2) by lia.
    rewrite odd_1, <- !app_assoc; f_equal; f_equal; f_equal; f_equal; f_equal; lia.
Qed.

Lemma Entry12 a : exists A o, Pass (Entry1 a) (a+2) A o /\
  o++retire A=Alt (negb (Nat.odd a)) (1+a)++Entry2 a.
Proof.
  exists (17+a*16), (Alt (negb (Nat.odd a)) (1+a) ++ Alt true (2+a*2) ++
    Alt false (3+a*4) ++ Alt false (8+a*8)); split.
  - unfold Entry1; eapply Pass_cat; [rewrite <- xorb_true_r; apply Pass_num10|].
    eapply Pass_cat with (b:=5+a*4).
    + applys_eq (@Pass_even_odd false (2+a*2) (1+a)); flia.
    + eapply Pass_cat with (b:=9+a*8).
      * applys_eq (Pass_odd_P_odd (3+a*4) (2+a*2)); flia.
      * applys_eq (@Pass_even_odd true (8+a*8) (4+a*4)); flia.
  - unfold retire, Entry2; replace (17+a*16) with (1+(8+a*8)*2) by lia.
    rewrite odd_1, <- !app_assoc; f_equal; f_equal; f_equal; f_equal; f_equal; lia.
Qed.

Lemma Entry23 a : exists A o, Pass (Entry2 a) (a+2) A o /\
  o++retire A=Alt (negb (Nat.odd a)) (1+a)++Entry3 a.
Proof.
  exists (17+a*16), (Alt (negb (Nat.odd a)) (1+a) ++ Alt true (2+a*2) ++
    Alt false (4+a*4) ++ Alt true (9+a*8)); split.
  - unfold Entry2; eapply Pass_cat; [rewrite <- xorb_true_r; apply Pass_num10|].
    eapply Pass_cat with (b:=4+a*4).
    + applys_eq (Pass_odd_I_odd (1+a*2) (1+a)); flia.
    + eapply Pass_cat with (b:=8+a*8).
      * applys_eq (@Pass_even_positive false (4+a*4) (1+a*2)); flia.
      * applys_eq (@Pass_even_positive true (9+a*8) (3+a*4)); flia.
  - unfold retire, Entry3; replace (17+a*16) with (1+(8+a*8)*2) by lia.
    rewrite odd_1, <- !app_assoc; f_equal; f_equal; f_equal; f_equal; f_equal; lia.
Qed.

Fixpoint PairPrefix n a (tail:nat->list bool) := match n with
  | 0 => tail a
  | S n => Alt true (2+a*2) ++ Alt false (4+a*4) ++ PairPrefix n (3+a*4) tail end.

Lemma PairPrefix_pass f g :
  (forall a, exists A o, Pass (f a) (a+2) A o /\
    o++retire A=Alt (negb (Nat.odd a)) (1+a)++g a) ->
  forall n a, exists A o, Pass (PairPrefix n a f) (a+2) A o /\
    o++retire A=Alt (negb (Nat.odd a)) (1+a)++PairPrefix n a g.
Proof.
  intros HG n; induction n; intro a; [apply HG|].
  destruct (IHn (3+a*4)) as [A [o [HP HE]]].
  exists A,(Alt (negb (Nat.odd a)) (1+a)++Alt true (2+a*2)++o); split.
  - cbn[PairPrefix]; eapply Pass_cat; [rewrite <- xorb_true_r; apply Pass_num10|].
    eapply Pass_cat; [|exact HP].
    applys_eq (@Pass_even_odd false (2+a*2) (1+a)); flia.
  - rewrite <- !app_assoc, HE.
    replace (3+a*4) with (1+(1+a*2)*2) at 1 by lia; rewrite odd_1.
    cbn[PairPrefix negb]; f_equal; f_equal; f_equal; f_equal; lia.
Qed.

Lemma PairPrefix_PI n a f : (forall a, exists u, f a=true::false::u) ->
  exists u, PairPrefix n a f=true::false::u.
Proof. intro H; destruct n; [apply H|cbn[PairPrefix Nat.add Alt app]; eauto]. Qed.

Lemma PairPrefix_life n f g :
  (forall a, exists u, f a=true::false::u) ->
  (forall a, exists A o, Pass (f a) (a+2) A o /\
    o++retire A=Alt (negb (Nat.odd a)) (1+a)++g a) ->
  Life Edge retire (PairPrefix n 0 f) [0] (PairPrefix n 0 g) [0].
Proof.
  intros HH HP; destruct (@PairPrefix_pass f g HP n 0) as [A [o [H E]]].
  destruct (@PairPrefix_PI n 0 f HH) as [u HU]; rewrite HU in H |- *.
  eapply Pass_terminal2; eassumption.
Qed.

Lemma Entry_lives n : Lives Edge retire 3 (PairPrefix n 0 Entry0) [0] (PairPrefix n 0 Entry3) [0].
Proof.
  eapply Lives_cons; [eapply PairPrefix_life; [intro a; unfold Entry0; cbn[Nat.add Alt app]; eauto|apply Entry01]|].
  eapply Lives_cons; [eapply PairPrefix_life; [intro a; unfold Entry1; cbn[Nat.add Alt app]; eauto|apply Entry12]|].
  eapply Lives_cons; [eapply PairPrefix_life; [intro a; unfold Entry2; cbn[Nat.add Alt app]; eauto|apply Entry23]|].
  constructor.
Qed.

Fixpoint EntryBits n := match n with
  | 0 => [false;true;true] | S n => false::true::EntryBits n end.

Lemma EntryBits_length n : length (EntryBits n)=n*2+3.
Proof. induction n; cbn; lia. Qed.

Lemma Entry3_num n : forall a, Num true a (EntryBits n) (PairPrefix n a Entry3).
Proof.
  induction n; intro a.
  - cbn[EntryBits PairPrefix]; unfold Entry3; apply Num_10.
    replace (4+a*4) with (2+(1+a*2)*2) by lia; apply Num_01.
    replace (1+(1+a*2)*2) with (3+a*4) by lia.
    replace (9+a*8) with (3+(3+a*4)*2) by lia; apply Num_11.
    applys_eq (Num_nil1 (8+a*8)); flia.
  - cbn[EntryBits PairPrefix]; apply Num_10.
    replace (4+a*4) with (2+(1+a*2)*2) by lia; apply Num_01.
    applys_eq (IHn (3+a*4)); flia.
Qed.

Lemma Entry_shape n : forall a, PairPrefix n a Entry0 =
  Alt true (2+a*2) ++ Doubles (4+a*4) (n+1) ++ Alt false ((1+a)*4^(n+1)*4-3).
Proof.
  induction n; intro a.
  - cbn[PairPrefix Nat.add Nat.pow Doubles]; unfold Entry0; rewrite app_nil_r, <- !app_assoc.
    f_equal; f_equal; f_equal; f_equal; lia.
  - cbn[PairPrefix]; rewrite IHn.
    cbn[Nat.add Nat.pow Doubles].
    replace (4+(3+a*4)*4) with ((4+a*4)*4) by lia.
    replace (2+(3+a*4)*2) with ((4+a*4)*2) by lia.
    rewrite <- !app_assoc; f_equal; f_equal; f_equal; f_equal; f_equal; nia.
Qed.

Lemma SWord_entry n : exists w, Num true 0 (EntryBits n) w /\
  Lives Edge retire 3 (SWord (1+n)) [0] w [0].
Proof.
  exists (PairPrefix n 0 Entry3); split; [apply Entry3_num|].
  pose proof (Entry_lives n) as H; rewrite Entry_shape in H.
  replace (n+1) with (1+n) in H by lia; unfold SWord; applys_eq H; flia.
Qed.

Theorem SWord_exit n : exists t,
  Lives Edge retire (4+t) (SWord (1+n)) [0] (EWord (4+n*2)) [0].
Proof.
  destruct (SWord_entry n) as [w [HN HL]].
  destruct (Num_exit HN) as [t HT]; rewrite EntryBits_length in HT.
  exists t; applys_eq (Lives_app HL HT); flia.
Qed.

Corollary seed_to_E n : exists t, Lives Edge retire (1+t)
  (true::Word (repeat 0 (14+n*2)) (7+n)) [0] (EWord (16+n*2)) [0].
Proof.
  destruct (SWord_exit (6+n)) as [t HT].
  pose proof (Lives_app (seed_to_single n) HT) as H.
  exists ((Quarter (7+n)*6-(7+n))*2+3+t); applys_eq H; flia.
Qed.

Lemma Ladder_I_pass n : forall a,
  Pass (Ladder false (4+a*4) n) (1+a*2)
    ((1+a)*2^(n+1)-1) (Ladder true (2+a*2) n).
Proof.
  induction n; intro a.
  - cbn[Ladder Nat.add Nat.pow]; replace ((1+a)*(2*1)-1) with (1+a*2) by lia; constructor.
  - cbn[Ladder]; eapply Pass_cat with (b:=3+a*4).
    + applys_eq (Pass_odd_I_odd (2+a*2) a); flia.
    + pose proof (IHn (1+a*2)) as H.
      replace ((1+(1+a*2))*2^(n+1)-1) with ((1+a)*2^(S n+1)-1) in H
        by (cbn[Nat.add Nat.pow]; nia).
      applys_eq H; flia.
Qed.

Definition EBorn n := Ladder true 2 n ++ Alt true (2^(n+1)).

Lemma EWord_parent n : Life Edge retire (EWord n) [0] (EBorn n) [0;0].
Proof.
  assert (HP : 2^n<>0) by (apply Nat.pow_nonzero; lia).
  assert (HR : retire (2^(n+1)-1)=Alt true (2^(n+1))).
  { unfold retire; replace (2^(n+1)) with (2^n*2) by (rewrite Nat.pow_add_r; cbn; lia).
    replace (2^n*2-1) with (1+(2^n-1)*2) by lia.
    rewrite odd_1; f_equal; lia. }
  unfold EWord, EBorn; rewrite <- HR.
  change (Life Edge retire (repeat true 0++false::Ladder false 4 n)
    [0] (Ladder true 2 n++retire (2^(n+1)-1)) [0;0]).
  eapply Life_terminal; [exact (Edge_even 0)|].
  applys_eq (Ladder_I_pass n 0); flia.
Qed.

Fixpoint BirthBody m : list nat := match m with
  | 0 => [] | S m => 1::0::BirthBody m end.

Lemma pow_two_four m : 2^(m*2+1)=4^m*2.
Proof.
  rewrite Nat.pow_add_r; replace (m*2) with (2*m) by lia.
  rewrite Nat.pow_mul_r; reflexivity.
Qed.

Lemma BirthBody_word m : forall b, CWord true b 0 (BirthBody m) 0 =
  Ladder true b (m*2) ++ Alt true (b*4^m).
Proof.
  induction m; intro b.
  - change (Alt true (b+0+0*2)=Alt true (b*1)); f_equal; lia.
  - cbn[BirthBody CWord]; rewrite IHm.
    cbn[Nat.mul Nat.add Nat.pow Ladder]; rewrite <- !app_assoc.
    replace (b*2*2) with (b*4) by lia.
    f_equal; [f_equal; lia|]; f_equal; [f_equal; lia|].
    f_equal; f_equal; nia.
Qed.

Lemma BirthBody_split m : TailSplit true (0::BirthBody m) (repeat 0 (1+m*2)) m.
Proof.
  induction m.
  - exact (TailSplit_cons (Split_even true 0) TailSplit_nil).
  - pose proof (TailSplit_cons (Split_even true 0) (TailSplit_cons (Split_odd0 0) IHm)) as H.
    applys_eq H; flia.
Qed.

Lemma EBorn_word m : EBorn (m*2)=CWord true 2 0 (BirthBody m) 0.
Proof. unfold EBorn; rewrite BirthBody_word, pow_two_four; f_equal; f_equal; lia. Qed.

Lemma EWord_internal n : Life Edge retire (EBorn (2+n*2)) [0;0]
  (true::Word (repeat 0 (2+n*2)) (1+n)) [0].
Proof.
  destruct (@CWord_pass true (0::BirthBody n) (repeat 0 (1+n*2)) n
    (BirthBody_split n) 1 1 0 1 0 0 2 ltac:(lia) (Split_odd0 0) ltac:(lia))
    as [A [o [HP HE]]].
  replace (repeat 0 (1+n*2)++[0]) with (repeat 0 (2+n*2)) in HE.
  2: { change [0] with (repeat 0 1); rewrite <- repeat_app; f_equal; lia. }
  change (o++retire A=Word (repeat 0 (2+n*2)) (1+n)) in HE.
  rewrite <- HE.
  change (Life Edge retire (EBorn (2+n*2)) [0;0] (([true]++o)++retire A) [0]).
  eapply Life_internal; [discriminate|].
  replace (2+n*2) with ((1+n)*2) by lia; rewrite EBorn_word.
  change (Pass (Alt true 3++CWord false 4 1 (0::BirthBody n) 0) 0 A ([true]++o)).
  eapply Pass_cat; [exact (@Pass_alt_odd_P 1 0)|exact HP].
Qed.

Theorem EWord_seed n : Lives Edge retire 2 (EWord (2+n*2)) [0]
  (true::Word (repeat 0 (2+n*2)) (1+n)) [0].
Proof. econstructor; [apply EWord_parent|econstructor; [apply EWord_internal|constructor]]. Qed.

Theorem EWord_round n : exists t, Lives Edge retire (1+t)
  (EWord (14+n*2)) [0] (EWord (16+n*2)) [0].
Proof.
  destruct (seed_to_E n) as [t HT].
  pose proof (EWord_seed (6+n)) as H; cbn[Nat.add Nat.mul] in H.
  exists (2+t); applys_eq (Lives_app H HT); flia.
Qed.

Lemma EWord_suffix_infinite : forall n k w xs,
  Lives Edge retire k w xs (EWord (14+n*2)) [0] -> InfiniteLife Edge retire w xs.
Proof.
  cofix IH; intros n k w xs H; destruct k.
  - inversion H; subst. destruct (EWord_round n) as [t HT].
    inversion HT; subst. econstructor; [eassumption|].
    eapply (IH (1+n) t); replace (14+(1+n)*2) with (16+n*2) by lia; eassumption.
  - inversion H; subst. econstructor; [eassumption|eapply (IH n k); eassumption].
Qed.

Theorem EWord_infinite n : InfiniteLife Edge retire (EWord (14+n*2)) [0].
Proof. eapply (@EWord_suffix_infinite n 0); constructor. Qed.

Lemma initial_E2 : Lives Edge retire 7 [] [3;0;0] (EWord 2) [0].
Proof.
  do 2 (eapply Lives_cons;
    [eapply Life_internal; [discriminate|
      repeat first [apply Pass_nil | apply Pass_P | apply Pass_I; [lia|]]]|]).
  do 5 (eapply Lives_cons;
    [eapply Life_terminal with (k:=1) (b:=3); [exact (Edge_odd 0)|
      repeat first [apply Pass_nil | apply Pass_P | apply Pass_I; [lia|]]]|]).
  constructor.
Qed.

Definition small_seed_check m := CounterEval.check (Alt false (m*2)) true
  (Quarter m*6-1-m) (repeat 0 (m*2)) m (ExitBody m) (Quarter m*2-1).

Lemma small_seed_checked : forallb small_seed_check [1;2;3;4;5;6]=true.
Proof. vm_compute; reflexivity. Qed.

Lemma small_seed_ticks m : 1<=m<=6 ->
  Ticks (Alt false (m*2)) true (Quarter m*6-1-m)
    (repeat 0 (m*2)) m (ExitBody m) (Quarter m*2-1).
Proof.
  intro HM; apply CounterEval.check_spec.
  apply (proj1 (forallb_forall small_seed_check [1;2;3;4;5;6]) small_seed_checked).
  cbn; lia.
Qed.

Lemma EWord_small_round n : n<6 -> exists t,
  Lives Edge retire (1+t) (EWord (2+n*2)) [0] (EWord (4+n*2)) [0].
Proof.
  intro HN; pose proof (@small_seed_ticks (1+n) ltac:(lia)) as HT.
  pose proof (Ticks_lives (1+n) HT) as HL.
  destruct (SWord_exit n) as [t HS].
  pose proof (Lives_app (EWord_seed n) (Lives_app HL (Lives_app (exit_boundary n) HS))) as H.
  exists ((Quarter (1+n)*6-1-(1+n))*2+7+t); applys_eq H; flia.
Qed.

Lemma initial_E_prefix n : n<=6 -> exists t,
  Lives Edge retire t (EWord 2) [0] (EWord (2+n*2)) [0].
Proof.
  induction n; intro HN.
  - exists 0; constructor.
  - destruct (IHn ltac:(lia)) as [t HT].
    destruct (@EWord_small_round n ltac:(lia)) as [s HS].
    exists (t+(1+s)); applys_eq (Lives_app HT HS); flia.
Qed.

Lemma initial_infinite : InfiniteLife Edge retire [] [3;0;0].
Proof.
  eapply Lives_infinite; [apply initial_E2|].
  destruct (@initial_E_prefix 6 ltac:(lia)) as [t HT].
  eapply Lives_infinite; [exact HT|exact (EWord_infinite 0)].
Qed.

Lemma initial_macro : Flow_InfiniteMacro Edge retire [3;0;0].
Proof.
  eapply InfiniteLife_sound;
    eauto using Edge_size, Edge_functional, initial_infinite, Run_nil.
Qed.

Theorem nonhalt : ~halts tm c0.
Proof. apply nonhalt_from_lives, initial_infinite. Qed.

End TM2.

Module TM4.
Definition tm := Eval compute in (TM_from_str "1RB---_0RC1RF_0LD1RF_0LE1LD_1RA1LC_0RC0RA").
Notation "c -->* c'" := (c -[tm]->* c') (at level 40).
Notation "c -->+ c'" := (c -[tm]->+ c') (at level 40).
Open Scope sym.

Fixpoint LC (xs:list nat) :=
  match xs with [] => 0inf | a::xs => LC xs <* <[1;0]^^a <* <[1] end.
Definition S1 xs n := LC xs {{B}}> [1;0]^^n *> 0inf.
Definition QL (p:bool) := if p then C else D.
Notation LInc := (Flow_LInc TM2.Edge).
Notation Run := (Flow_Run TM2.Edge).

Lemma LInc_spec p xs ys : LInc p xs ys ->
  forall r, LC xs <{{QL p}} [1;0] *> r -->* LC ys {{B}}> r.
Proof.
  intro H; induction H; intros r.
  - cbn[LC QL]; es.
  - destruct (mod2 a) as [k E|k E]; subst a.
    + rewrite odd_0 in IHLInc. destruct k as [|k]; [lia|].
      replace (S k*2) with (2+k*2) by lia.
      cbn[LC QL] in *; es; er; follow IHLInc; es.
    + rewrite odd_1 in IHLInc. cbn[LC QL] in *; es; er; follow IHLInc; es.
  - destruct H; cbn[LC QL]; es.
Qed.

Lemma Inc_right n xs ys : LInc (negb (Nat.odd n)) xs ys ->
  S1 xs (1+n) -->* S1 ys n.
Proof.
  intro H; destruct (mod2 n) as [a E|a E]; subst n.
  - rewrite odd_0 in H. eapply LInc_spec in H. es; er; follow H; finish.
  - rewrite odd_1 in H. eapply LInc_spec in H. es; er; follow H; finish.
Qed.

Lemma Inc_zero a xs ys : LInc (negb (Nat.odd a)) xs ys ->
  S1 (a::xs) 0 -->+ S1 ys a.
Proof.
  intro H; destruct (mod2 a) as [k E|k E]; subst a.
  - rewrite odd_0 in H. eapply LInc_spec in H. unfold S1; cbn[LC].
    es; er; follow H; finish.
  - rewrite odd_1 in H. eapply LInc_spec in H. unfold S1; cbn[LC].
    es; er; follow H; finish.
Qed.

Lemma Run_right n xs ys : Run (Alt (Nat.odd n) n) xs ys -> S1 xs n -->* S1 ys 0.
Proof.
  revert xs; induction n; intros xs H.
  - inversion H; subst; apply evstep_refl.
  - cbn[Alt] in H; rewrite odd_S, negb_involutive in H.
    inversion H as [|p w source cut target HL HR]; subst.
    follow (Inc_right n HL); apply IHn; assumption.
Qed.

Lemma Macro_return a xs ys : Run (Alt (negb (Nat.odd a)) (1+a)) xs ys ->
  S1 (a::xs) 0 -->+ S1 ys 0.
Proof.
  intro H; cbn[Nat.add Alt] in H; rewrite negb_involutive in H.
  inversion H as [|p w source cut target HL HR]; subst.
  follow10 (Inc_zero a HL); apply Run_right; assumption.
Qed.

Lemma init : c0 -->* S1 [2] 2.
Proof. unfold S1; esx. Qed.

Lemma first_cut : c0 -->* S1 [4;0;0]%nat 0.
Proof.
  follow init. follow (@Inc_right 1 [2]%nat [3;0;0]%nat ltac:(apply LInc_edge, (TM2.Edge_even 1))).
  apply Inc_right, LInc_P.
Qed.

Close Scope sym.

Definition J (xs:list nat) := match xs with [] => [] | a::xs => 1+a::xs end.

Lemma retire_J a : Alt (negb (Nat.odd (1+a))) (1+(1+a))=TM2.retire a++[true].
Proof.
  unfold TM2.retire; change (1+a) with (S a).
  rewrite odd_S, negb_involutive.
  replace (1+S a) with (S a+1) by lia; rewrite Alt_snoc, odd_S.
  destruct (Nat.odd a); reflexivity.
Qed.

Lemma Run_J xs : xs<>[] -> Run [true] xs (J xs).
Proof. destruct xs; [contradiction|intros; econstructor; constructor]. Qed.

Lemma Macro_J xs ys : Flow_Macro TM2.Edge TM2.retire xs ys -> ys<>[] ->
  S1 (J xs) 0 -->+ S1 (J ys) 0.
Proof.
  intros H Hne; destruct H; cbn[J]; apply Macro_return; rewrite retire_J.
  apply Run_app; eexists; split; [eassumption|apply Run_J; exact Hne].
Qed.

Lemma InfiniteMacro_nonempty xs : Flow_InfiniteMacro TM2.Edge TM2.retire xs -> xs<>[].
Proof. intros H; destruct H as [xs ys H _]; destruct H; discriminate. Qed.

Lemma InfiniteMacro_nonhalt xs : Flow_InfiniteMacro TM2.Edge TM2.retire xs ->
  ~halts tm (S1 (J xs) 0).
Proof.
  intro HI; eapply progress_nonhalt with (P:=fun c => exists ys,
    Flow_InfiniteMacro TM2.Edge TM2.retire ys /\ c=S1 (J ys) 0).
  - intros c [ys [H ->]]; destruct H as [ys zs HM HI'].
    exists (S1 (J zs) 0); split; [exists zs; auto|].
    apply Macro_J; [exact HM|apply InfiniteMacro_nonempty; exact HI'].
  - exists xs; auto.
Qed.

Theorem nonhalt : ~halts tm c0.
Proof.
  eapply multistep_nonhalt; [apply first_cut|].
  exact (InfiniteMacro_nonhalt TM2.initial_macro).
Qed.

End TM4.

Module TM3.
Definition tm := Eval compute in (TM_from_str "1RB---_0LC1RF_1RA1LD_0LE1RF_0LC1LE_0RD0RA").
Notation "c -->* c'" := (c -[tm]->* c') (at level 40).
Notation "c -->+ c'" := (c -[tm]->+ c') (at level 40).
Open Scope sym.

Fixpoint LC (xs:list nat) :=
  match xs with [] => 0inf | a::xs => LC xs <* <[1;0]^^a <* <[1] end.
Definition S1 xs n := LC xs {{B}}> [1;0]^^n *> 0inf.
Definition QL (p:bool) := if p then D else E.

Inductive Edge : nat -> nat -> list nat -> Prop :=
| Edge_even a : Edge (a*2) (1+a*2) [0;0]%nat
| Edge_odd a : Edge (1+a*2) (2+a*2) [1]%nat.
Notation LInc := (Flow_LInc Edge).
Notation Run := (Flow_Run Edge).
Definition retire a := Alt (negb (Nat.odd a)) (1+a).

Lemma Edge_size a b kids : Edge a b kids -> length kids<=2.
Proof. intro H; destruct H; cbn; lia. Qed.

Lemma Edge_functional a b kids c kids' :
  Edge a b kids -> Edge a c kids' -> b=c /\ kids=kids'.
Proof. intros H H'; destruct H; inversion H'; subst; split; try reflexivity; f_equal; lia. Qed.

Lemma LInc_spec p xs ys : LInc p xs ys ->
  forall r, LC xs <{{QL p}} [1;0] *> r -->* LC ys {{B}}> r.
Proof.
  intro H; induction H; intros r.
  - cbn[LC QL]; es.
  - destruct (mod2 a) as [k E|k E]; subst a.
    + rewrite odd_0 in IHLInc. destruct k as [|k]; [lia|].
      replace (S k*2) with (2+k*2) by lia.
      cbn[LC QL] in *; es; er; follow IHLInc; es.
    + rewrite odd_1 in IHLInc. cbn[LC QL] in *; es; er; follow IHLInc; es.
  - destruct H; cbn[LC QL]; es.
Qed.

Lemma Inc_right n xs ys : LInc (negb (Nat.odd n)) xs ys ->
  S1 xs (1+n) -->* S1 ys n.
Proof.
  intro H; destruct (mod2 n) as [a E|a E]; subst n.
  - rewrite odd_0 in H. eapply LInc_spec in H. es; er; follow H; finish.
  - rewrite odd_1 in H. eapply LInc_spec in H. es; er; follow H; finish.
Qed.

Lemma Inc_zero a xs ys : LInc (negb (Nat.odd a)) xs ys ->
  S1 (a::xs) 0 -->+ S1 ys a.
Proof.
  intro H; destruct (mod2 a) as [k E|k E]; subst a.
  - rewrite odd_0 in H. eapply LInc_spec in H. unfold S1; cbn[LC].
    es; er; follow H; finish.
  - rewrite odd_1 in H. eapply LInc_spec in H. unfold S1; cbn[LC].
    es; er; follow H; finish.
Qed.

Lemma Run_right n xs ys : Run (Alt (Nat.odd n) n) xs ys -> S1 xs n -->* S1 ys 0.
Proof.
  revert xs; induction n; intros xs H.
  - inversion H; subst; apply evstep_refl.
  - cbn[Alt] in H; rewrite odd_S, negb_involutive in H.
    inversion H as [|p w source cut target HL HR]; subst.
    follow (Inc_right n HL); apply IHn; assumption.
Qed.

Lemma Macro_spec xs ys : Flow_Macro Edge retire xs ys -> S1 xs 0 -->+ S1 ys 0.
Proof.
  intro H; destruct H; cbn[retire Nat.add Alt] in H; rewrite negb_involutive in H.
  inversion H as [|p w source cut target HL HR]; subst.
  follow10 (Inc_zero a HL); apply Run_right; assumption.
Qed.

Lemma init : c0 -->* S1 [2] 2.
Proof. unfold S1; esx. Qed.

Lemma first_cut : c0 -->* S1 [4;0;0]%nat 0.
Proof.
  follow init. follow (@Inc_right 1 [2]%nat [3;0;0]%nat ltac:(apply LInc_edge, (Edge_even 1))).
  apply Inc_right, LInc_P.
Qed.

Lemma InfiniteMacro_nonhalt xs :
  Flow_InfiniteMacro Edge retire xs -> ~halts tm (S1 xs 0).
Proof.
  intro HI. eapply progress_nonhalt with
    (P:=fun c => exists ys, Flow_InfiniteMacro Edge retire ys /\ c=S1 ys 0).
  - intros c [ys [H ->]]. destruct H as [ys zs HM HI'].
    exists (S1 zs 0); split; [exists zs; auto|apply Macro_spec; assumption].
  - exists xs; auto.
Qed.

Lemma nonhalt_from_lives :
  Flow_InfiniteLife Edge retire [] [4;0;0]%nat -> ~halts tm c0.
Proof.
  intro H; eapply multistep_nonhalt; [apply first_cut|].
  apply InfiniteMacro_nonhalt. eapply InfiniteLife_sound;
    eauto using Edge_size, Edge_functional, Run_nil.
Qed.

Close Scope sym.

(* A synthetic internal column at 2 emits one extra I at the first input.
   The real terminal 1 instead creates its child and resumes at the same 2. *)
Lemma Pass_terminal_I u A o w : Pass (false::u) 2 A o ->
  o++retire A=false::w -> Life Edge retire (false::u) [1] w [1].
Proof.
  intros H E; inversion H; subst.
  cbn in E; injection E as E; subst w.
  change (Life Edge retire (repeat true 0++false::u) [1] (o0++retire A) [1]).
  eapply Life_terminal; [exact (Edge_odd 0)|assumption].
Qed.

Lemma FlatWord_life N xs u ys v : Half (repeat false N) 1 xs u ys v 0 ->
  Life Edge retire (FlatWord 0 xs u) [1] (FlatWord 0 ys v) [1].
Proof.
  intro H; inversion H as [body root q qs r HS]; subst.
  assert (EL : length xs=N) by (apply Scatter_length in HS; rewrite repeat_length in HS; tauto).
  rewrite <- EL in HS.
  destruct (@FlatWord_pass xs (0::qs) r HS 0 0 0 1 u 2 (Split_even false 0) ltac:(lia) ltac:(lia))
    as [A [o [HP HE]]].
  change (o++retire A=false::FlatWord 0 (qs++[u]) (1+r)) in HE.
  destruct (FlatWord_I xs u) as [w EW]; rewrite EW in HP |- *.
  eapply Pass_terminal_I; eassumption.
Qed.

Lemma FlatSteps_lives N n xs ys : FlatSteps N n xs ys ->
  Lives Edge retire n (FlatWord 0 (tl xs) (hd 0 xs)) [1]
    (FlatWord 0 (tl ys) (hd 0 ys)) [1].
Proof.
  intro H; induction H; [constructor|].
  destruct H0; cbn[tl hd] in *; replace (1+n) with (n+1) by lia.
  eapply Lives_app; [exact IHFlatSteps|].
  econstructor; [eapply FlatWord_life; eassumption|constructor].
Qed.

Lemma initial_flat : Lives Edge retire 4 [] [4;0;0] (FlatWord 0 [1] 2) [1].
Proof.
  do 2 (eapply Lives_cons;
    [eapply Life_internal; [discriminate|
      repeat first [apply Pass_nil | apply Pass_P | apply Pass_I; [lia|]]]|]).
  eapply Lives_cons;
    [eapply Life_terminal with (k:=1) (b:=2); [exact (Edge_odd 0)|
      repeat first [apply Pass_nil | apply Pass_P | apply Pass_I; [lia|]]]|].
  eapply Lives_cons;
    [eapply Life_terminal with (k:=0) (b:=2); [exact (Edge_odd 0)|
      repeat first [apply Pass_nil | apply Pass_P | apply Pass_I; [lia|]]]|].
  constructor.
Qed.

Lemma Ladder_snoc n : forall p b,
  Ladder p b (n+1)=Ladder p b n++Alt p (1+b*2^n).
Proof.
  induction n; intros p b; cbn[Nat.add Ladder Nat.pow].
  - rewrite Nat.mul_1_r, app_nil_r; reflexivity.
  - rewrite IHn, <- app_assoc; f_equal; f_equal; f_equal; lia.
Qed.

Lemma Pass_ladder_tail n : forall t, t<>0 ->
  Pass (Ladder false (t*2) n++Alt false (2+t*2*2^n)) t (1+t*2*2^n)
    (Alt (Nat.odd t) (1+t)++Ladder false (t*2) n).
Proof.
  induction n; intros t HT.
  - cbn[Ladder Nat.pow app]; rewrite Nat.mul_1_r, app_nil_r.
    pose proof (@Pass_alt_even false (1+t) t (or_introl HT)) as H.
    rewrite xorb_false_r in H. applys_eq H; flia.
  - cbn[Ladder Nat.pow].
    pose proof (@Pass_alt_odd_I t t HT) as H.
    replace (t+t) with (t*2) in H by lia.
    pose proof (IHn (t*2) ltac:(lia)) as HR; rewrite odd_0 in HR.
    rewrite <- app_assoc. applys_eq (Pass_cat H HR); flia.
Qed.

Lemma Pass_ladder_tail_low n : forall t, t<>0 -> Nat.odd t=false ->
  Pass (Ladder false (t*2) n++Alt false (2+t*2*2^n)) (t-1) (t*2*2^n)
    (Ladder true t (1+n)).
Proof.
  induction n; intros t HT ET;
    assert (EO : Nat.odd (t-1)=true) by
      (pose proof (odd_S (t-1)) as E; replace (S (t-1)) with t in E by lia;
       rewrite ET in E; destruct (Nat.odd (t-1)); cbn in E; congruence);
    assert (HP : t-1<>0) by (intro E; rewrite E in EO; discriminate).
  - cbn[Ladder Nat.pow app Nat.add]; rewrite Nat.mul_1_r, app_nil_r.
    pose proof (@Pass_alt_even false (1+t) (t-1) (or_introl HP)) as H.
    rewrite EO in H; cbn[xorb] in H. applys_eq H; flia.
  - cbn[Ladder Nat.pow Nat.add].
    pose proof (@Pass_alt_odd_I t (t-1) HP) as H; rewrite EO in H.
    pose proof (IHn (t*2) ltac:(lia) (odd_0 t)) as HR.
    replace (t-1+t) with (t*2-1) in H by lia.
    rewrite <- app_assoc. applys_eq (Pass_cat H HR); flia.
Qed.

(* RWord k is the paper's R_(k+2). Its first two columns preserve a
   geometric tail, then turn it into a pure P-starting ladder. *)
Definition RTail n := Ladder false 6 (1+n)++Alt false (2+12*2^n).
Definition RWord n := Alt true 2++RTail n.
Definition RMid n := Alt true 2++Alt false 4++Ladder true 6 (2+n).

Lemma RWord_parent n : Life Edge retire (RWord n) [1] (Alt true 4++RTail n) [0;0].
Proof.
  pose proof (@Pass_ladder_tail (1+n) 3 ltac:(lia)) as H.
  change (Pass (Ladder false 6 (1+n)++Alt false (2+6*(2*2^n))) 3
    (1+6*(2*2^n)) (Alt true 4++Ladder false 6 (1+n))) in H.
  replace (6*(2*2^n)) with (12*2^n) in H by lia.
  assert (EO : Nat.odd (1+12*2^n)=true).
  { replace (1+12*2^n) with (1+(6*2^n)*2) by lia; apply odd_1. }
  pose proof (@Life_terminal Edge retire 1 _ 1 3 _ _ [0;0] (Edge_even 1) H) as HL.
  unfold retire in HL; rewrite EO in HL; cbn[negb] in HL.
  rewrite <- !app_assoc in HL. exact HL.
Qed.

Lemma RWord_internal n : Life Edge retire (Alt true 4++RTail n) [0;0] (RMid n) [0].
Proof.
  pose proof (@Pass_ladder_tail_low n 6 ltac:(lia) eq_refl) as HR.
  change (Pass (Ladder false 12 n++Alt false (2+12*2^n)) 5 (12*2^n)
    (Ladder true 6 (1+n))) in HR.
  assert (H : Pass (Alt true 4++RTail n) 0 (12*2^n)
    (Alt true 2++Alt false 4++Ladder true 6 (1+n))).
  { unfold RTail; cbn[Ladder Nat.add]; rewrite <- app_assoc.
    eapply Pass_cat; [exact (@Pass_alt_even true 2 0 (or_intror eq_refl))|].
    eapply Pass_cat; [exact (@Pass_alt_odd_I 3 2 ltac:(lia))|exact HR]. }
  assert (EO : Nat.odd (12*2^n)=false).
  { replace (12*2^n) with ((6*2^n)*2) by lia; apply odd_0. }
  unfold RMid. replace (2+n) with ((1+n)+1) by lia.
  rewrite Ladder_snoc.
  replace (Alt true (1+6*2^(1+n))) with (retire (12*2^n))
    by (unfold retire; rewrite EO; cbn[Nat.add Nat.pow]; f_equal; lia).
  rewrite !app_assoc; apply Life_internal; [discriminate|].
  rewrite <- !app_assoc; exact H.
Qed.

Lemma Pass_ladder_P_pairs n : forall b a, Nat.odd b=false -> Nat.odd a=true ->
  Pass (Ladder true (b*2) (n*2)) a (a+n*2+b*(4^n-1)) (Doubles b n).
Proof.
  induction n; intros b a EB EA.
  - cbn[Ladder Doubles Nat.pow Nat.sub]; rewrite Nat.mul_0_r, !Nat.add_0_r; constructor.
  - pose proof (@Pass_alt_odd_P b a) as H1; rewrite EA in H1; cbn[negb] in H1.
    assert (E2 : Nat.odd (1+a+b)=false).
    { rewrite !Nat.odd_add, EA, EB; reflexivity. }
    pose proof (@Pass_alt_odd_P (b*2) (1+a+b)) as H2.
    rewrite E2 in H2; cbn[negb] in H2.
    assert (E3 : Nat.odd (1+(1+a+b)+b*2)=true).
    { rewrite !Nat.odd_add, EA, EB, odd_0; reflexivity. }
    pose proof (IHn (b*4) (1+(1+a+b)+b*2)
      ltac:(rewrite Nat.odd_mul, EB; reflexivity) E3) as H3.
    replace (S n*2) with (2+n*2) by lia; cbn[Ladder Doubles Nat.add Nat.pow].
    pose proof (Nat.pow_nonzero 4 n ltac:(lia)) as HP.
    replace (a+S (S (n*2))+b*(4*4^n-1)) with
      (1+(1+a+b)+b*2+n*2+b*4*(4^n-1)) by (destruct (4^n); [contradiction|cbn; nia]).
    applys_eq (Pass_cat H1 (Pass_cat H2 H3)); flia.
Qed.

Definition RSeedWord n := Alt false 2++Alt true 3++Alt true 6++Doubles 12 n++
  Alt false (4+n*2+12*4^n).

Lemma RWord_terminal n : Life Edge retire (RMid (n*2)) [0] (RSeedWord n) [1].
Proof.
  pose proof (@Pass_ladder_P_pairs n 12 15 eq_refl eq_refl) as H.
  pose proof (Nat.pow_nonzero 4 n ltac:(lia)) as HP.
  replace (15+n*2+12*(4^n-1)) with (3+n*2+12*4^n) in H
    by (destruct (4^n); [contradiction|cbn; lia]).
  assert (Htail : Pass (Alt false 4++Ladder true 6 (2+n*2)) 2 (3+n*2+12*4^n)
    (Alt false 2++Alt true 3++Alt true 6++Doubles 12 n)).
  { cbn[Ladder Nat.add].
    eapply Pass_cat; [exact (@Pass_alt_even false 2 2 ltac:(left; lia))|].
    eapply Pass_cat; [exact (@Pass_alt_odd_P 3 4)|].
    eapply Pass_cat; [exact (@Pass_alt_odd_P 6 8)|exact H]. }
  assert (EO : Nat.odd (3+n*2+12*4^n)=true).
  { replace (3+n*2+12*4^n) with (1+(1+n+6*4^n)*2) by lia; apply odd_1. }
  pose proof (@Life_terminal Edge retire 1 _ 0 2 _ _ [1] (Edge_odd 0) Htail) as HL.
  unfold retire in HL; rewrite EO in HL; cbn[negb] in HL.
  rewrite <- !app_assoc in HL. unfold RMid, RSeedWord; applys_eq HL; flia.
Qed.

Lemma RWord_entry n : Lives Edge retire 3 (RWord (n*2)) [1] (RSeedWord n) [1].
Proof.
  eapply Lives_cons; [apply RWord_parent|].
  eapply Lives_cons; [apply RWord_internal|].
  eapply Lives_cons; [apply RWord_terminal|constructor].
Qed.

(* RSeed n has body dimension 3+2n. Odd body positions are powers of
   two; even positions are one below them. This is an exact word encoding. *)
Fixpoint RNums k n := match n with
  | 0 => [4^k] | S n => 4^k::(4^k*2-1)::RNums (1+k) n end.
Definition RSeed n := (4^(1+n)+(1+n))::RNums 0 (1+n).

Lemma FlatWord_RNums n : forall k x u,
  FlatWord x (RNums (1+k) n) u = Alt (Nat.odd x) (1+x+4^(1+k))++
    Doubles (4^(1+k)*3) n++Alt false (2+4^(1+k+n)+u*2).
Proof.
  induction n; intros k x u;
    assert (EP : 4^(1+k)<>0) by (apply Nat.pow_nonzero; lia);
    assert (EO : Nat.odd (4^(1+k))=false) by
      (replace (4^(1+k)) with ((4^k*2)*2) by (cbn[Nat.add Nat.pow]; lia); apply odd_0).
  - cbn[RNums FlatWord Doubles]; rewrite EO, Nat.add_0_r; reflexivity.
  - change (RNums (1+k) (S n)) with (4^(1+k)::(4^(1+k)*2-1)::RNums (1+(1+k)) n).
    cbn[FlatWord]; rewrite EO, IHn.
    assert (E : Nat.odd (4^(1+k)*2-1)=true).
    { replace (4^(1+k)*2-1) with (1+(4^(1+k)-1)*2) by lia; apply odd_1. }
    rewrite E; cbn[Doubles].
    replace (1+4^(1+k)+(4^(1+k)*2-1)) with (4^(1+k)*3) by lia.
    replace (1+(4^(1+k)*2-1)+4^(1+(1+k))) with (4^(1+k)*3*2)
      by (cbn[Nat.add Nat.pow] in EP |- *; lia).
    replace (4^(1+(1+k))*3) with (4^(1+k)*3*4) by (cbn[Nat.add Nat.pow]; lia).
    replace (1+(1+k)+n) with (1+k+S n) by lia; rewrite <- !app_assoc; reflexivity.
Qed.

Lemma RSeed_word n : FlatWord 0 (tl (RSeed n)) (hd 0 (RSeed n))=RSeedWord n.
Proof.
  unfold RSeed, RSeedWord; cbn[tl hd RNums Nat.add Nat.pow FlatWord].
  change (Alt false 2++Alt true 3++FlatWord 1 (RNums 1 n) (4^(1+n)+(1+n))=
    Alt false 2++Alt true 3++Alt true 6++Doubles 12 n++Alt false (4+n*2+12*4^n)).
  rewrite (@FlatWord_RNums n 0 1); cbn[Nat.add Nat.pow].
  f_equal; f_equal; f_equal; f_equal; f_equal; lia.
Qed.

Lemma RWord_flat_entry n : Lives Edge retire 3 (RWord (n*2)) [1]
  (FlatWord 0 (tl (RSeed n)) (hd 0 (RSeed n))) [1].
Proof. rewrite RSeed_word; apply RWord_entry. Qed.

Lemma RNums_mass n : forall k, total (RNums k n)+n=4^k*(4^n*2-1).
Proof.
  induction n; intro k; cbn[RNums total Nat.pow].
  - lia.
  - pose proof (Nat.pow_nonzero 4 k ltac:(lia)) as HP.
    pose proof (Nat.pow_nonzero 4 n ltac:(lia)) as HQ.
    pose proof (IHn (1+k)) as H; change (total (RNums (1+k) n)+n=4*4^k*(4^n*2-1)) in H.
    nia.
Qed.

Lemma RSeed_mass n : total (RSeed n)+1=4^(1+n)*3.
Proof.
  unfold RSeed; cbn[total]. pose proof (@RNums_mass (1+n) 0) as H.
  rewrite Nat.pow_0_r, Nat.mul_1_l in H.
  pose proof (Nat.pow_nonzero 4 (1+n) ltac:(lia)); lia.
Qed.

Fixpoint BinaryCaps k n := match n with
  | 0 => [] | S n => (2^k-1)::BinaryCaps (1+k) n end.

Lemma BinaryCaps_app n : forall k m,
  BinaryCaps k (n+m)=BinaryCaps k n++BinaryCaps (k+n) m.
Proof.
  induction n; intros k m; cbn[BinaryCaps Nat.add app].
  - rewrite Nat.add_0_r; reflexivity.
  - rewrite IHn; flia.
Qed.

Lemma BinaryCaps_box n : FlatBox (1+n) (BinaryCaps 1 (1+n)) (2^(1+n)-1).
Proof.
  induction n; [exact FlatBox_base|].
  replace (1+S n) with ((1+n)+1) at 2 by lia.
  rewrite BinaryCaps_app; cbn[BinaryCaps].
  replace (2^(1+S n)-1) with (1+(2^(1+n)-1)*2)
    by (pose proof (Nat.pow_nonzero 2 (1+n) ltac:(lia));
      change (1+(2^(1+n)-1)*2=2*2^(1+n)-1); lia).
  replace (1+(1+n)) with (1+S n) by lia.
  replace (2^(1+S n)-1) with (1+(2^(1+n)-1)*2)
    by (pose proof (Nat.pow_nonzero 2 (1+n) ltac:(lia));
      change (1+(2^(1+n)-1)*2=2*2^(1+n)-1); lia).
  exact (FlatBox_next IHn).
Qed.

Lemma power4 k : 2^(k*2)=4^k.
Proof. replace (k*2) with (2*k) by lia; rewrite Nat.pow_mul_r; reflexivity. Qed.

Lemma RNums_bounds n : forall k,
  Forall2 le (BinaryCaps (k*2) (n*2)++[4^(k+n)]) (RNums k n) /\
  Forall2 le (RNums k n) (BinaryCaps (1+k*2) (1+n*2)).
Proof.
  induction n; intro k; pose proof (Nat.pow_nonzero 4 k ltac:(lia)) as HP.
  - cbn[RNums BinaryCaps Nat.add Nat.pow]; rewrite power4, Nat.add_0_r.
    change (Forall2 le [4^k] [4^k] /\ Forall2 le [4^k] [2*4^k-1]).
    split; (constructor; [lia|constructor]).
  - destruct (IHn (1+k)) as [HL HU].
    replace (S n*2) with (2+n*2) by lia.
    cbn[RNums BinaryCaps Nat.add Nat.pow]; rewrite power4.
    replace (1+(1+(k*2))) with ((1+k)*2) by lia.
    replace (1+(1+(1+(k*2)))) with (1+(1+k)*2) by lia.
    replace (k+S n) with (1+k+n) by lia.
    split.
    + constructor; [lia|constructor; [lia|]]. applys_eq HL; flia.
    + constructor; [lia|constructor; [lia|]].
      replace (1+(1+k)*2) with (3+k*2) in HU by lia.
      cbn[BinaryCaps Nat.add Nat.pow] in HU; rewrite power4 in HU. exact HU.
Qed.

Definition RBound n := BinaryCaps 1 (1+n*2).
Definition RHeight n := 2^(1+n*2)-1.

Lemma RSeed_box n : FlatBox (1+n*2) (RBound n) (RHeight n).
Proof. apply BinaryCaps_box. Qed.

Lemma RSeed_bounds n :
  Forall2 le (FlatLower (RBound n) (RHeight n)) (RSeed n) /\
  Forall2 le (tl (RSeed n)) (FlatUpper (RBound n) (RHeight n)).
Proof.
  destruct (@RNums_bounds (1+n) 0) as [HL HU].
  assert (EP : 2^(1+n*2)<>0) by (apply Nat.pow_nonzero; lia).
  assert (EQ : 4^(1+n)=2^(1+n*2)*2).
  { rewrite <- power4; replace ((1+n)*2) with (1+(1+n*2)) by lia.
    change (2*2^(1+n*2)=2^(1+n*2)*2); lia. }
  split.
  - unfold RSeed, FlatLower, RBound, RHeight; constructor; [lia|].
    replace (2+(2^(1+n*2)-1)*2) with (4^(1+n)) by lia.
    change (Forall2 le ((0::BinaryCaps 1 (1+n*2))++[4^(1+n)]) (RNums 0 (1+n))).
    replace (1+n*2) with ((1+n)*2-1) by lia.
    change (Forall2 le (BinaryCaps 0 (1+((1+n)*2-1))++[4^(1+n)]) (RNums 0 (1+n))).
    replace (1+((1+n)*2-1)) with ((1+n)*2) by lia.
    exact HL.
  - unfold RSeed, FlatUpper, RBound, RHeight; cbn[tl].
    change (Forall2 le (RNums 0 (1+n)) (BinaryCaps 1 (1+(1+n)*2))) in HU.
    replace (1+(1+n)*2) with ((1+n*2)+2) in HU by lia.
    rewrite BinaryCaps_app in HU; cbn[BinaryCaps] in HU.
    cbn[Nat.add Nat.pow] in EP, HU |- *; applys_eq HU; flia.
Qed.

Lemma RSeed_excess n : total (RSeed n)=total (FlatLower (RBound n) (RHeight n))+(2+n*2).
Proof.
  pose proof (RSeed_mass n) as HM.
  destruct (FlatLower_capacity (RSeed_box n)) as [HP HB].
  replace (1+(1+n*2)) with ((1+n)*2) in HP by lia; rewrite power4 in HP.
  change (total (RSeed n)=2+(RHeight n)*2+total (tl (FlatLower (RBound n) (RHeight n)))+(2+n*2)).
  lia.
Qed.

(* At m=10+2n the seed has excess N-1 and an independently safe
   window of (4N+12)(N-1)+2 complete column lifetimes. *)
Lemma RSeed_window n t : t<=((11+n*2)*4+12)*(10+n*2)+2 -> exists ys,
  FlatSteps (11+n*2) t (RSeed (4+n)) ys /\
  Forall2 le (FlatLower (RBound (4+n)) (RHeight (4+n))) ys /\
  Forall2 le (tl ys) (FlatUpper (RBound (4+n)) (RHeight (4+n))) /\
  total ys=total (RSeed (4+n))+t.
Proof.
  intro HT; destruct (RSeed_bounds (4+n)) as [HL HU].
  eapply (@FlatLower_large_window n (RBound (4+n)) (RHeight (4+n)) (10+n*2) t (RSeed (4+n))).
  - applys_eq (RSeed_box (4+n)); flia.
  - exact HL.
  - exact HU.
  - rewrite RSeed_excess; lia.
  - lia.
Qed.

Lemma RSeed_absorption n : exists ys,
  FlatSteps (11+n*2) (((11+n*2)*4+12)*(10+n*2)) (RSeed (4+n)) ys /\
  FlatAligned (11+n*2) (FlatLower (RBound (4+n)) (RHeight (4+n)))
    (((11+n*2)*4+12)*(10+n*2)+(10+n*2)) ys.
Proof.
  set (N:=11+n*2); set (K:=10+n*2); set (C:=N*4+12).
  assert (Hbox : FlatBox (9+n*2) (RBound (4+n)) (RHeight (4+n))).
  { applys_eq (RSeed_box (4+n)); flia. }
  destruct (RSeed_window n (t:=C*K) ltac:(unfold C,N,K; lia)) as [ys [Hrun _]].
  destruct (RSeed_bounds (4+n)) as [HL HU].
  destruct (@FlatLower_large_window n (RBound (4+n)) (RHeight (4+n)) 0 (C*K+K+1)
    (FlatLower (RBound (4+n)) (RHeight (4+n))) Hbox (le_refl_list _)
    (FlatLower_bounds Hbox) ltac:(lia) ltac:(unfold C,N,K; lia)) as [endc [Hmain _]].
  destruct (FlatLower_step Hbox) as [next [HS [HB HC]]].
  replace (2+(9+n*2)) with N in HS by (unfold N; lia).
  exists ys; split; [exact Hrun|].
  eapply Flat_many_absorbs; [unfold N; lia|unfold C; lia|exact HS|exact HB|exact HC|exact HL| |exact Hmain|exact Hrun].
  rewrite RSeed_excess; unfold K; lia.
Qed.

Lemma RWord_absorption n : exists ys,
  Lives Edge retire (3+((11+n*2)*4+12)*(10+n*2)) (RWord ((4+n)*2)) [1]
    (FlatWord 0 (tl ys) (hd 0 ys)) [1] /\
  FlatAligned (11+n*2) (FlatLower (RBound (4+n)) (RHeight (4+n)))
    (((11+n*2)*4+12)*(10+n*2)+(10+n*2)) ys.
Proof.
  destruct (RSeed_absorption n) as [ys [HS HA]].
  exists ys; split; [|exact HA].
  eapply Lives_app; [apply RWord_flat_entry|eapply FlatSteps_lives; exact HS].
Qed.

(* Exact first long phase: a single geometric output or its one-unit
   early variant, without predicting which branch the seed selects. *)
Fixpoint PowBody k n := match n with 0=>[] | S n=>2^k::PowBody (1+k) n end.

Lemma PowBody_app n : forall k m, PowBody k (n+m)=PowBody k n++PowBody (k+n) m.
Proof.
  induction n; intros k m; cbn[PowBody Nat.add app].
  - rewrite Nat.add_0_r; reflexivity.
  - rewrite IHn; flia.
Qed.

Lemma FlatRowsBody_values sink n : map (@length nat) (FlatRowsBody sink n)=PowBody 1 n.
Proof.
  induction n; [reflexivity|].
  cbn[FlatRowsBody]; rewrite map_app; cbn[map]; rewrite FlatRow_length, IHn.
  replace (S n) with (n+1) by lia; rewrite PowBody_app; cbn[PowBody Nat.add Nat.pow]; flia.
Qed.

Lemma FlatExitRows_values N : map (@length nat) (FlatExitRows N)=2^N::PowBody 1 N.
Proof.
  unfold FlatExitRows; cbn[map]; rewrite Cycles_length, FlatRowsBody_values; cbn[length]; flia.
Qed.

Lemma LowRows_values n : map (@length nat) (LowRows n)=BinaryCaps 1 n.
Proof.
  induction n; [reflexivity|].
  cbn[LowRows]; rewrite map_app; cbn[map]; rewrite LowRow_length, IHn.
  replace (S n) with (n+1) by lia; rewrite BinaryCaps_app; reflexivity.
Qed.

Lemma FlatLowerRows_values n : map (@length nat) (FlatLowerRows n)=
  FlatLower (BinaryCaps 1 (1+n)) (2^(1+n)-1).
Proof.
  unfold FlatLowerRows, FlatLower; cbn[map length].
  rewrite map_app, LowRows_values; cbn[map]; rewrite !Cycles_length; cbn[length].
  pose proof (Nat.pow_nonzero 2 n ltac:(lia)); cbn[Nat.add Nat.pow]; flia.
Qed.

Lemma FlatWord_powers n : forall k u,
  FlatWord (2^(1+k)) (PowBody (2+k) n) u = Ladder false (2^(1+k)*3) n++
    Alt false (2+2^(1+k+n)+u*2).
Proof.
  induction n; intros k u;
    assert (EO : Nat.odd (2^(1+k))=false) by
      (replace (2^(1+k)) with (2^k*2) by (cbn[Nat.add Nat.pow]; lia); apply odd_0).
  - cbn[PowBody FlatWord Ladder app]; rewrite EO, Nat.add_0_r; reflexivity.
  - change (PowBody (2+k) (S n)) with (2^(2+k)::PowBody (2+(1+k)) n).
    cbn[FlatWord]; rewrite EO.
    change (2^(2+k)) with (2^(1+(1+k))).
    rewrite (IHn (1+k) u); cbn[Ladder].
    replace (2^(2+k)) with (2*2^(1+k)) by reflexivity.
    replace (2^(1+(1+k))*3) with (2^(1+k)*3*2) by (cbn[Nat.add Nat.pow]; lia).
    replace (1+(1+k)+n) with (1+k+S n) by lia.
    rewrite <- app_assoc; cbn[Nat.add Nat.pow]; flia.
Qed.

Lemma FlatExit_word n : FlatWord 0 (PowBody 1 (2+n)) (2^(2+n))=Alt false 3++RTail n.
Proof.
  change (Alt false 3++FlatWord 2 (PowBody 2 (1+n)) (2^(2+n))=Alt false 3++RTail n).
  rewrite (@FlatWord_powers (1+n) 0); unfold RTail.
  cbn[Nat.add Nat.pow]; flia.
Qed.

Theorem FlatLower_exit n : FlatSteps (3+n) (2^(2+n)*3+(1+n))
  (FlatLower (BinaryCaps 1 (1+n)) (2^(1+n)-1)) (2^(3+n)::PowBody 1 (3+n)).
Proof.
  pose proof (Flat_zero_lower n) as HP; rewrite FlatLowerRows_values in HP.
  pose proof (@Flat_zero_exit (3+n) ltac:(lia)) as HE; rewrite FlatExitRows_values in HE.
  eapply FlatSteps_cancel; [exact HP|exact HE|].
  pose proof (LowRows_budget (1+n)) as HB; cbn[Nat.add Nat.pow] in HB |- *; lia.
Qed.

Lemma RLower_exit n : FlatSteps (11+n*2) (4^(5+n)*3+(9+n*2))
  (FlatLower (RBound (4+n)) (RHeight (4+n))) (2^(11+n*2)::PowBody 1 (11+n*2)).
Proof.
  pose proof (FlatLower_exit (8+n*2)) as H.
  replace (3+(8+n*2)) with (11+n*2) in H by lia.
  replace (2+(8+n*2)) with ((5+n)*2) in H by lia; rewrite power4 in H.
  unfold RBound, RHeight; applys_eq H; flia.
Qed.

Definition FlatEarlyWord n := Alt false 3++Alt false 6++Alt true 12++Ladder false 24 n++
  Alt false (2+24*2^n).

Lemma FlatEarly_word n :
  FlatWord 0 (2::3::PowBody 3 (1+n)) (2^(3+n))=FlatEarlyWord n.
Proof.
  change (Alt false 3++Alt false 6++Alt true 12++FlatWord 8 (PowBody 4 n) (2^(3+n))=FlatEarlyWord n).
  rewrite (@FlatWord_powers n 2); unfold FlatEarlyWord; cbn[Nat.add Nat.pow]; flia.
Qed.

Theorem RWord_first_exit n :
  Lives Edge retire (4^(5+n)*3+2) (RWord ((4+n)*2)) [1] (Alt false 3++RTail (9+n*2)) [1] \/
  Lives Edge retire (4^(5+n)*3+1) (RWord ((4+n)*2)) [1] (FlatEarlyWord (8+n*2)) [1].
Proof.
  set (N:=11+n*2); set (K:=10+n*2); set (C:=N*4+12); set (P:=4^(5+n)).
  set (root:=FlatLower (RBound (4+n)) (RHeight (4+n))).
  set (J:=C*K+K); set (T:=P*3-2-C*K); set (L:=P*3+(9+n*2)).
  assert (HBudget : C*K+K+3<P).
  { pose proof (FlatLower_budget n) as H.
    replace (2^(10+n*2)) with (4^(5+n)) in H by (rewrite <- power4; f_equal; lia).
    unfold C,N,K,P; lia. }
  assert (ET : J+T+1=L) by (unfold J,T,L,K; lia).
  assert (ET' : 3+C*K+T=P*3+1) by (unfold T; lia).
  destruct (RWord_absorption n) as [cut [Hentry HA]].
  change (FlatAligned N root J cut) in HA.
  pose proof (RLower_exit n) as Hfull.
  change (FlatSteps N L root (2^N::PowBody 1 N)) in Hfull.
  assert (Href : FlatSteps N (J+T+1) root (2^N::PowBody 1 N)) by (rewrite ET; exact Hfull).
  destruct (@FlatAligned_continue N root J cut ltac:(unfold N; lia) HA T _ Href) as [out [Hout HAligned]].
  assert (Htrace : Lives Edge retire (P*3+1) (RWord ((4+n)*2)) [1]
    (FlatWord 0 (tl out) (hd 0 out)) [1]).
  { rewrite <- ET'; eapply Lives_app; [exact Hentry|eapply FlatSteps_lives; exact Hout]. }
  destruct (FlatLower_step (RSeed_box (4+n))) as [next [Hstep [Hbump Hcarry]]].
  replace (2+(1+(4+n)*2)) with N in Hstep by (unfold N; lia).
  change (FlatStep N root next) in Hstep.
  assert (HL : L=2+(P*3+(7+n*2))) by (unfold L; lia).
  rewrite HL in Hfull.
  assert (HJ : J+T=1+(P*3+(7+n*2))) by lia; rewrite HJ in HAligned.
  change (FlatSteps N (2+(P*3+(7+n*2))) root
    (2^N::2::4::PowBody 3 (9+n*2))) in Hfull.
  destruct (FlatAligned_final (N:=N) ltac:(unfold N; lia) Hstep Hbump Hcarry Hfull HAligned)
    as [[-> Hlast] | ->].
  - left.
    assert (Hone : FlatSteps N 1 (2^N::1::4::PowBody 3 (9+n*2)) (2^N::2::4::PowBody 3 (9+n*2)))
      by (econstructor; [constructor|exact Hlast]).
    pose proof (FlatSteps_lives Hone) as HF; cbn[hd tl] in HF.
    change (2::4::PowBody 3 (9+n*2)) with (PowBody 1 (2+(9+n*2))) in HF.
    unfold N in HF; replace (11+n*2) with (2+(9+n*2)) in HF by lia; rewrite FlatExit_word in HF.
    change (Lives Edge retire (P*3+2) (RWord ((4+n)*2)) [1] (Alt false 3++RTail (9+n*2)) [1]).
    replace (P*3+2) with ((P*3+1)+1) by lia; eapply Lives_app; [exact Htrace|exact HF].
  - right; cbn[hd tl] in Htrace.
    replace (9+n*2) with (1+(8+n*2)) in Htrace by lia.
    unfold N in Htrace; replace (11+n*2) with (3+(8+n*2)) in Htrace by lia.
    rewrite FlatEarly_word in Htrace; exact Htrace.
Qed.

(* A fixed geometric translation reuses the same FlatSteps for the second
   single-column phase, including its early branch. *)
Lemma Pass_terminal_PP u A o w : Pass (true::false::u) 3 A o ->
  o++retire A=false::w ->
  Life Edge retire (true::true::false::u) [1] w [1].
Proof.
  intros H E; inversion H as [|w0 a b o0 HP|]; subst; inversion HP; subst.
  cbn in E; injection E as E.
  change (o0++retire A=w) in E.
  change (Life Edge retire (repeat true 2++false::u) [1] w [1]).
  rewrite <- E; eapply Life_terminal; [exact (Edge_odd 1)|assumption].
Qed.

Lemma FlatWord_I_overflow N xs u ys v : Half (repeat false N) 1 xs u ys v 1 ->
  Life Edge retire (FlatWord 0 xs u) [1] (true::FlatWord 1 ys v) [1].
Proof.
  intro H; inversion H as [body root q qs r HS]; subst.
  assert (EL : length xs=N) by (apply Scatter_length in HS; rewrite repeat_length in HS; tauto).
  rewrite <- EL in HS.
  destruct (@FlatWord_pass xs (1::qs) r HS 0 0 0 1 u 2 (Split_even false 0) ltac:(lia) ltac:(lia))
    as [A [o [HP HE]]].
  change (o++retire A=false::true::FlatWord 1 (qs++[u]) (1+r)) in HE.
  destruct (FlatWord_I xs u) as [w EW]; rewrite EW in HP |- *.
  eapply Pass_terminal_I; eassumption.
Qed.

Lemma FlatWord_P_reset N xs u ys v : Half (repeat false N) 2 xs u ys v 0 ->
  Life Edge retire (true::FlatWord 1 xs u) [1] (FlatWord 0 ys v) [1].
Proof.
  intro H; inversion H as [body root q qs r HS]; subst.
  assert (EL : length xs=N) by (apply Scatter_length in HS; rewrite repeat_length in HS; tauto).
  rewrite <- EL in HS.
  destruct (@FlatWord_pass xs (0::qs) r HS 1 0 1 1 u 3 (Split_odd0 0) ltac:(lia) ltac:(lia))
    as [A [o [HP HE]]].
  change (o++retire A=false::FlatWord 0 (qs++[u]) (2+r)) in HE.
  destruct xs as [|a xs]; [inversion HS|].
  change (FlatWord 1 (a::xs) u) with (true::false::(Alt true a++FlatWord a xs u)) in HP |- *.
  eapply Pass_terminal_PP; eassumption.
Qed.

Lemma FlatWord_P_life N xs u ys v : Half (repeat false N) 2 xs u ys v 1 ->
  Life Edge retire (true::FlatWord 1 xs u) [1] (true::FlatWord 1 ys v) [1].
Proof.
  intro H; inversion H as [body root q qs r HS]; subst.
  assert (EL : length xs=N) by (apply Scatter_length in HS; rewrite repeat_length in HS; tauto).
  rewrite <- EL in HS.
  destruct (@FlatWord_pass xs (1::qs) r HS 1 0 1 1 u 3 (Split_odd0 0) ltac:(lia) ltac:(lia))
    as [A [o [HP HE]]].
  change (o++retire A=false::true::FlatWord 1 (qs++[u]) (2+r)) in HE.
  destruct xs as [|a xs]; [inversion HS|].
  change (FlatWord 1 (a::xs) u) with (true::false::(Alt true a++FlatWord a xs u)) in HP |- *.
  eapply Pass_terminal_PP; eassumption.
Qed.

Definition SecondWord N xs := true::FlatWord 1 (Raise 2 (tl xs)) (hd 0 xs+2^N).

Lemma SecondSteps_lives N n xs ys : FlatSteps N n xs ys ->
  Lives Edge retire n (SecondWord N xs) [1] (SecondWord N ys) [1].
Proof.
  intro H; induction H; [constructor|].
  destruct H0; unfold SecondWord in *; cbn[hd tl] in *.
  replace (1+n) with (n+1) by lia; eapply Lives_app; [exact IHFlatSteps|].
  econstructor; [eapply FlatWord_P_life; exact (Half_raise H0)|constructor].
Qed.

Lemma Raise_zeros n : forall k, Raise (2^k) (repeat 0 n)=PowBody k n.
Proof.
  induction n; intro k; cbn[Raise repeat PowBody]; [reflexivity|].
  rewrite Nat.add_0_r; replace (2^k*2) with (2^(1+k)) by (cbn[Nat.add Nat.pow]; lia).
  rewrite IHn; reflexivity.
Qed.

Lemma Raise_powers n : forall k, Raise (2^k) (PowBody k n)=PowBody (1+k) n.
Proof.
  induction n; intro k; cbn[Raise PowBody]; [reflexivity|].
  replace (2^k*2) with (2^(1+k)) by (cbn[Nat.add Nat.pow]; lia).
  rewrite IHn; f_equal; cbn[Nat.add Nat.pow]; lia.
Qed.

Lemma SecondWord_zero n : SecondWord (2+n) (0::repeat 0 (2+n))=
  true::(Alt true 4++RTail n).
Proof.
  unfold SecondWord; cbn[hd tl]; rewrite Nat.add_0_l.
  replace (Raise 2 (repeat 0 (2+n))) with (PowBody 1 (2+n))
    by (symmetry; exact (@Raise_zeros (2+n) 1)).
  change (FlatWord 1 (PowBody 1 (2+n)) (2^(2+n))) with
    (Alt true 4++FlatWord 2 (PowBody 2 (1+n)) (2^(2+n))).
  rewrite (@FlatWord_powers (1+n) 0); unfold RTail; cbn[Nat.add Nat.pow]; flia.
Qed.

Lemma SecondWord_exit n : SecondWord (2+n) (2^(2+n)::PowBody 1 (2+n))=
  true::(Alt true 6++Ladder false 12 (1+n)++Alt false (2+24*2^n)).
Proof.
  unfold SecondWord; cbn[hd tl].
  replace (Raise 2 (PowBody 1 (2+n))) with (PowBody 2 (2+n))
    by (symmetry; exact (@Raise_powers (2+n) 1)).
  change (FlatWord 1 (PowBody 2 (2+n)) (2^(2+n)+2^(2+n))) with
    (Alt true 6++FlatWord 4 (PowBody 3 (1+n)) (2^(2+n)+2^(2+n))).
  rewrite (@FlatWord_powers (1+n) 1); cbn[Nat.add Nat.pow]; flia.
Qed.

Lemma First_exit_boundary n : Life Edge retire (Alt false 3++RTail n) [1]
  (SecondWord (2+n) (0::repeat 0 (2+n))) [1].
Proof.
  rewrite SecondWord_zero.
  pose proof (@Pass_ladder_tail (1+n) 3 ltac:(lia)) as H.
  change (Pass (Ladder false 6 (1+n)++Alt false (2+6*(2*2^n))) 3
    (1+6*(2*2^n)) (Alt true 4++Ladder false 6 (1+n))) in H.
  replace (6*(2*2^n)) with (12*2^n) in H by lia.
  assert (EO : Nat.odd (1+12*2^n)=true).
  { replace (1+12*2^n) with (1+(6*2^n)*2) by lia; apply odd_1. }
  assert (HP : Pass (true::false::RTail n) 2 (1+12*2^n)
    (true::(Alt true 4++Ladder false 6 (1+n)))) by
    (apply Pass_P, Pass_I; [lia|exact H]).
  pose proof (@Life_terminal Edge retire 0 _ 1 2 _ _ [1] (Edge_odd 0) HP) as HL.
  unfold retire in HL; rewrite EO in HL; cbn[negb] in HL.
  unfold RTail; exact HL.
Qed.

Lemma Second_exit_boundary n : Life Edge retire
  (true::(Alt true 6++Ladder false 12 (1+n)++Alt false (2+24*2^n))) [1]
  (RWord (1+n)) [1].
Proof.
  pose proof (@Pass_ladder_tail (1+n) 6 ltac:(lia)) as H.
  change (Pass (Ladder false 12 (1+n)++Alt false (2+12*(2*2^n))) 6
    (1+12*(2*2^n)) (Alt false 7++Ladder false 12 (1+n))) in H.
  replace (12*(2*2^n)) with (24*2^n) in H by lia.
  assert (EO : Nat.odd (1+24*2^n)=true).
  { replace (1+24*2^n) with (1+(12*2^n)*2) by lia; apply odd_1. }
  assert (HP : Pass (true::false::true::false::
    (Ladder false 12 (1+n)++Alt false (2+24*2^n))) 4 (1+24*2^n)
    (Alt true 2++Alt false 7++Ladder false 12 (1+n))).
  { apply Pass_P, Pass_I; [lia|]. apply Pass_P, Pass_I; [lia|exact H]. }
  pose proof (@Life_terminal Edge retire 2 _ 1 4 _ _ [1] (Edge_odd 1) HP) as HL.
  unfold retire in HL; rewrite EO in HL; cbn[negb] in HL.
  change (Life Edge retire
    (true::(Alt true 6++Ladder false 12 (1+n)++Alt false (2+24*2^n))) [1]
    (Alt true 2++Alt false 7++Ladder false 12 (1+n)++Alt false (2+12*2^(1+n))) [1]).
  replace (12*2^(1+n)) with (24*2^n) by (cbn[Nat.add Nat.pow]; lia).
  rewrite <- !app_assoc in HL; exact HL.
Qed.

Theorem First_ordinary_round n : Lives Edge retire (2^(2+n)*3)
  (Alt false 3++RTail n) [1] (RWord (1+n)) [1].
Proof.
  pose proof (@Flat_zero_exit (2+n) ltac:(lia)) as HF.
  rewrite FlatExitRows_values in HF.
  pose proof (SecondSteps_lives HF) as HS; rewrite SecondWord_exit in HS.
  replace (2^(2+n)*3) with (1+((2^(2+n)*3-2)+1)) by
    (pose proof (Nat.pow_nonzero 2 n ltac:(lia)); cbn[Nat.add Nat.pow]; lia).
  eapply Lives_cons; [apply First_exit_boundary|].
  eapply Lives_app; [exact HS|].
  econstructor; [apply Second_exit_boundary|constructor].
Qed.

Lemma Scatter_powers n : forall k, Scatter (repeat false n)
  (PowBody (1+k) n) (PowBody k n) (2^k*(2^n-1)).
Proof.
  induction n; intro k; cbn[PowBody repeat].
  - rewrite Nat.mul_0_r; constructor.
  - pose proof (Nat.pow_nonzero 2 n ltac:(lia)).
    replace (2^k*(2^S n-1)) with (2^k+2^(1+k)*(2^n-1))
      by (cbn[Nat.pow Nat.add]; nia).
    constructor; [apply Split_even_eq; cbn[Nat.pow Nat.add]; lia|apply IHn].
Qed.

Lemma Early_first_half n : Half (repeat false (3+n)) 1
  (2::3::PowBody 3 (1+n)) (2^(3+n)) (1::PowBody 2 (2+n)) (2^(3+n)) 1.
Proof.
  pose proof (@Scatter_powers (1+n) 2) as HT.
  assert (HP : Scatter (repeat false (3+n)) (2::3::PowBody 3 (1+n))
    (1::1::PowBody 2 (1+n)) (2^(3+n)-1)).
  { replace (2^(3+n)-1) with (1+(2+2^2*(2^(1+n)-1))) by
      (pose proof (Nat.pow_nonzero 2 n ltac:(lia)); cbn[Nat.pow Nat.add]; lia).
    apply Scatter_cons; [exact (Split_even false 1)|].
    apply Scatter_cons; [exact (Split_odd0 1)|exact HT]. }
  pose proof (Half_make 1 (2^(3+n)) HP) as H.
  replace (1+(2^(3+n)-1)) with (2^(3+n)) in H by
    (pose proof (Nat.pow_nonzero 2 n ltac:(lia)); cbn[Nat.pow Nat.add]; lia).
  replace (2+n) with ((1+n)+1) by lia; rewrite (@PowBody_app (1+n) 2 1).
  change (PowBody (2+(1+n)) 1) with [2^(2+(1+n))].
  replace (2+(1+n)) with (3+n) by lia; exact H.
Qed.

Lemma Early_second_half n : Half (repeat false (3+n)) 2
  (1::PowBody 2 (2+n)) (2^(3+n)) (PowBody 1 (3+n)) (1+2^(3+n)) 0.
Proof.
  pose proof (@Scatter_powers (2+n) 1) as HT.
  assert (HP : Scatter (repeat false (3+n)) (1::PowBody 2 (2+n))
    (0::PowBody 1 (2+n)) (2^(3+n)-1)).
  { replace (2^(3+n)-1) with (1+2^1*(2^(2+n)-1)) by
      (pose proof (Nat.pow_nonzero 2 n ltac:(lia)); cbn[Nat.pow Nat.add]; lia).
    apply Scatter_cons; [exact (Split_odd0 0)|exact HT]. }
  pose proof (Half_make 2 (2^(3+n)) HP) as H.
  replace (2+(2^(3+n)-1)) with (1+2^(3+n)) in H by
    (pose proof (Nat.pow_nonzero 2 n ltac:(lia)); cbn[Nat.pow Nat.add]; lia).
  replace (PowBody 1 (3+n)) with (PowBody 1 ((2+n)+1)) by (f_equal; lia).
  rewrite (@PowBody_app (2+n) 1 1).
  change (PowBody (1+(2+n)) 1) with [2^(1+(2+n))].
  replace (1+(2+n)) with (3+n) by lia; exact H.
Qed.

Lemma Early_third_half N : 0<N -> Half (repeat false N) 1
  (PowBody 1 N) (1+2^N) (Raise 2 (repeat 0 (N-1)++[1])) (2^N) 1.
Proof.
  destruct N as [|n]; [lia|intros _].
  pose proof (@Scatter_powers (S n) 0) as HS.
  cbn[PowBody] in HS; rewrite Nat.mul_1_l in HS.
  pose proof (Half_make 1 (1+2^S n) HS) as H.
  replace (1+(2^S n-1)) with (2^S n) in H by
    (pose proof (Nat.pow_nonzero 2 n ltac:(lia)); cbn[Nat.pow]; lia).
  replace (S n-1) with n by lia; rewrite Raise_app.
  replace (Raise 2 (repeat 0 n)) with (PowBody 1 n)
    by (symmetry; exact (@Raise_zeros n 1)).
  rewrite repeat_length; cbn[Raise].
  replace (2*2^n+1) with (1+2^S n) by (cbn[Nat.pow]; lia); exact H.
Qed.

Theorem First_early_entry n : Lives Edge retire 3 (FlatEarlyWord n) [1]
  (SecondWord (3+n) (0::(repeat 0 (2+n)++[1]))) [1].
Proof.
  rewrite <- FlatEarly_word.
  eapply Lives_cons; [apply FlatWord_I_overflow with (N:=3+n); apply Early_first_half|].
  eapply Lives_cons; [apply FlatWord_P_reset with (N:=3+n); apply Early_second_half|].
  unfold SecondWord; cbn[hd tl]; rewrite Nat.add_0_l.
  replace (2+n) with (3+n-1) by lia.
  econstructor; [apply FlatWord_I_overflow with (N:=3+n), Early_third_half; lia|constructor].
Qed.

Lemma SecondWord_early n : SecondWord (3+n) (2^(3+n)::2::3::PowBody 3 (1+n))=
  true::(Alt true 6++Alt false 12++Alt true 24++Ladder false 48 n++Alt false (2+48*2^n)).
Proof.
  unfold SecondWord; cbn[hd tl].
  change (Raise 2 (2::3::PowBody 3 (1+n))) with (4::7::Raise 8 (PowBody 3 (1+n))).
  replace (Raise 8 (PowBody 3 (1+n))) with (PowBody 4 (1+n))
    by (symmetry; exact (@Raise_powers (1+n) 3)).
  change (FlatWord 1 (4::7::PowBody 4 (1+n)) (2^(3+n)+2^(3+n))) with
    (Alt true 6++Alt false 12++Alt true 24++FlatWord 16 (PowBody 5 n) (2^(3+n)+2^(3+n))).
  rewrite (@FlatWord_powers n 3); cbn[Nat.pow Nat.add]; flia.
Qed.

(* RPrimeWord k is the paper's R'_(k+3). *)
Definition RPrimeWord n := Alt true 2++Alt false 6++Alt true 12++Ladder false 24 n++
  Alt false (2+24*2^n).

Lemma Second_early_boundary n : Life Edge retire
  (true::(Alt true 6++Alt false 12++Alt true 24++Ladder false 48 n++Alt false (2+48*2^n))) [1]
  (RPrimeWord (1+n)) [1].
Proof.
  pose proof (@Pass_ladder_tail n 24 ltac:(lia)) as HT.
  change (Pass (Ladder false 48 n++Alt false (2+48*2^n)) 24
    (1+48*2^n) (Alt false 25++Ladder false 48 n)) in HT.
  assert (HP : Pass (Alt true 6++Alt false 12++Alt true 24++Ladder false 48 n++Alt false (2+48*2^n))
    3 (1+48*2^n) (Alt false 3++Alt false 6++Alt true 12++Alt false 25++Ladder false 48 n)).
  { eapply Pass_cat; [exact (@Pass_alt_even true 3 3 ltac:(right; reflexivity))|].
    eapply Pass_cat; [exact (@Pass_alt_even false 6 6 ltac:(left; lia))|].
    eapply Pass_cat; [exact (@Pass_alt_even true 12 12 ltac:(right; reflexivity))|exact HT]. }
  assert (EO : Nat.odd (1+48*2^n)=true).
  { replace (1+48*2^n) with (1+(24*2^n)*2) by lia; apply odd_1. }
  change (Life Edge retire
    (true::true::false::(Alt true 4++Alt false 12++Alt true 24++Ladder false 48 n++Alt false (2+48*2^n)))
    [1] (RPrimeWord (1+n)) [1]).
  eapply Pass_terminal_PP; [exact HP|].
  unfold retire, RPrimeWord; rewrite EO; cbn[negb].
  change (Ladder false 24 (1+n)) with (Alt false 25++Ladder false 48 n).
  replace (24*2^(1+n)) with (48*2^n) by (cbn[Nat.pow Nat.add]; lia).
  rewrite <- !app_assoc; reflexivity.
Qed.

Theorem First_early_round n : Lives Edge retire (2^(3+n)*3)
  (FlatEarlyWord n) [1] (RPrimeWord (1+n)) [1].
Proof.
  set (N:=3+n); set (T:=2^N*3-4).
  assert (ET : 2^N*3-2=2+T) by
    (unfold T, N; pose proof (Nat.pow_nonzero 2 n ltac:(lia)); cbn[Nat.pow Nat.add]; lia).
  pose proof (@Flat_zero_exit N ltac:(unfold N; lia)) as HF.
  rewrite FlatExitRows_values, ET in HF.
  change (FlatSteps N (2+T) (0::repeat 0 N) (2^N::2::4::PowBody 3 (1+n))) in HF.
  assert (HS : FlatStep N (0::repeat 0 N) (1::repeat 0 N)) by (apply FlatStep_zero; unfold N; lia).
  pose proof (@FlatEarly_zero (2+n)) as HE.
  change (FlatEarly N (0::repeat 0 N) (1::repeat 0 N) (0::(repeat 0 (2+n)++[1]))) in HE.
  pose proof (FlatEarly_final_run (N:=N) ltac:(unfold N; lia) HS
    (Bump_here 0 (repeat 0 N)) ltac:(left; reflexivity) HE HF) as HA.
  pose proof (SecondSteps_lives HA) as HL; unfold N in HL; rewrite SecondWord_early in HL.
  replace (2^N*3) with (3+(T+1)) by
    (unfold T, N; pose proof (Nat.pow_nonzero 2 n ltac:(lia)); cbn[Nat.pow Nat.add]; lia).
  eapply Lives_app; [apply First_early_entry|].
  eapply Lives_app; [exact HL|].
  econstructor; [apply Second_early_boundary|constructor].
Qed.

Theorem RWord_round n :
  Lives Edge retire (4^(5+n)*9+2) (RWord ((4+n)*2)) [1] (RWord ((5+n)*2)) [1] \/
  Lives Edge retire (4^(5+n)*9+1) (RWord ((4+n)*2)) [1] (RPrimeWord (9+n*2)) [1].
Proof.
  destruct (RWord_first_exit n) as [HO|HE].
  - left; pose proof (First_ordinary_round (9+n*2)) as H.
    replace (2^(2+(9+n*2))) with (4^(5+n)*2) in H by
      (rewrite <- power4; replace (2+(9+n*2)) with (1+(5+n)*2) by lia; cbn[Nat.pow Nat.add]; lia).
    replace (1+(9+n*2)) with ((5+n)*2) in H by lia.
    replace (4^(5+n)*9+2) with ((4^(5+n)*3+2)+4^(5+n)*2*3) by lia.
    eapply Lives_app; eassumption.
  - right; pose proof (First_early_round (8+n*2)) as H.
    replace (2^(3+(8+n*2))) with (4^(5+n)*2) in H by
      (rewrite <- power4; replace (3+(8+n*2)) with (1+(5+n)*2) by lia; cbn[Nat.pow Nat.add]; lia).
    replace (1+(8+n*2)) with (9+n*2) in H by lia.
    replace (4^(5+n)*9+1) with ((4^(5+n)*3+1)+4^(5+n)*2*3) by lia.
    eapply Lives_app; eassumption.
Qed.

(* Paired-column stage: internal zero, then its new double-birth parent. *)
Definition PairWord xs u := match xs with []=>[] |
  x::xs=>Alt true (3+x)++CWord true 6 x xs u end.

Lemma Pass_pair_first x q r s : Split false x q r ->
  Pass (Alt true (6+x)) (2+s*2) (5+r+s*2) (Alt true (3+q)).
Proof.
  intro H.
  pose proof (@Split_adjacent true 0 0 0 x q r 3 (Split_even true 0) H) as HS.
  pose proof (@Pass_alt_split true (6+x) (3+r) (3+q) (2+s*2) HS ltac:(right; reflexivity)) as HP.
  replace (2+s*2) with ((1+s)*2) in HP by lia; rewrite odd_0 in HP.
  applys_eq HP; flia.
Qed.

Lemma Pair_pass n xs qs R s u : Scatter (Alt true (2+n*2)) xs (0::qs) R ->
  exists A o, Pass (PairWord xs u) (s*2) A (true::o) /\
    o++retire A=PairWord (qs++[u]) (s+R).
Proof.
  intro H; cbn[Alt Nat.add] in H; inversion H; subst.
  match goal with HS : Split true _ 0 _ |- _ => inversion HS; subst end.
  match goal with HS : Scatter (false::_) _ _ _ |- _ => inversion HS; subst end.
  match goal with HT : Scatter (Alt true (n*2)) ?tail ?out ?rest |- _ =>
    pose proof (Scatter_length HT) as [EL _]; rewrite Alt_length in EL;
    assert (HT' : Scatter (Alt true (length tail)) tail out rest) by (rewrite EL; exact HT)
  end.
  match goal with HS : Split false ?x ?q ?r, HT : Scatter _ ?tail ?out ?rest |- _ =>
    destruct (@CWord_pass_mask tail true out rest HT' 3 x q r s u (5+r+s*2)
      ltac:(lia) HS ltac:(lia)) as [A [o [HP HE]]]
  end.
  rewrite EL, odd_0 in HE; cbn[xorb] in HE; fold (negb (Nat.odd A)) in HE; fold (retire A) in HE.
  exists A,(Alt true (3+q)++o); split.
  - change (Pass (Alt true 3++Alt true (6+a)++CWord false 12 a xs u)
      (s*2) A ([true]++Alt true (3+q)++o)).
    pose proof (@Pass_alt_odd_P 1 (s*2)) as HF; rewrite odd_0 in HF.
    replace (1+s*2+1) with (2+s*2) in HF by lia.
    eapply Pass_cat; [exact HF|].
    eapply Pass_cat; [apply Pass_pair_first; eassumption|exact HP].
  - rewrite <- app_assoc, HE; cbn[PairWord app]; f_equal; f_equal; lia.
Qed.

Lemma Pair_internal n xs qs r u : Scatter (Alt true (2+n*2)) xs (0::qs) r ->
  Life Edge retire (PairWord xs u) [0;0] (true::PairWord (qs++[u]) r) [0].
Proof.
  intro H; destruct (@Pair_pass n xs qs r 0 u H) as [A [o [HP HE]]].
  cbn[Nat.add] in HE; rewrite <- HE.
  change (Life Edge retire (PairWord xs u) [0;0] ((true::o)++retire A) [0]).
  apply Life_internal; [discriminate|exact HP].
Qed.

Lemma Pair_parent n xs qs r u : Scatter (Alt true (2+n*2)) xs (0::qs) r ->
  Life Edge retire (true::PairWord xs u) [0] (PairWord (qs++[u]) (1+r)) [0;0].
Proof.
  intro H; destruct (@Pair_pass n xs qs r 1 u H) as [A [o [HP HE]]].
  assert (HF : exists tail, xs=0::tail).
  { cbn[Alt Nat.add] in H; inversion H; subst.
    match goal with HS : Split true _ 0 _ |- _ => inversion HS; subst end; eauto. }
  rewrite <- HE; destruct HF as [tail ->]; cbn[PairWord Nat.add Alt app] in HP |- *.
  inversion HP; subst; match goal with HP : Pass (false::_) _ _ _ |- _ => inversion HP; subst end.
  change (Life Edge retire (repeat true 2++false::true::CWord true 6 0 tail u) [0]
    (o++retire A) [0;0]).
  eapply Life_terminal; [exact (Edge_even 1)|assumption].
Qed.

Lemma Pair_tick_lives n xs u ys v : Tick (Alt true (2+n*2)) false xs u ys v 0 ->
  Lives Edge retire 2 (PairWord xs u) [0;0] (PairWord ys v) [0;0].
Proof.
  intro H; inversion H as [xs0 u0 mid root ys0 v0 a b H1 H2]; subst.
  assert (a=0 /\ b=0) as [-> ->] by lia.
  inversion H1; subst; inversion H2; subst.
  eapply Lives_cons; [eapply Pair_internal; eassumption|].
  eapply Lives_cons; [eapply Pair_parent; eassumption|constructor].
Qed.

Lemma Pair_ticks_lives n t xs u ys v : Ticks (Alt true (2+n*2)) false t xs u ys v ->
  Lives Edge retire (t*2) (PairWord xs u) [0;0] (PairWord ys v) [0;0].
Proof.
  intro H; induction H; [constructor|].
  replace ((1+n0)*2) with (2+n0*2) by lia.
  eapply Lives_app; [eapply Pair_tick_lives; eassumption|assumption].
Qed.

Inductive PairBox : nat -> list nat -> nat -> Prop :=
| PairBox_base : PairBox 0 [0;0] 0
| PairBox_next n xs h : PairBox n xs h ->
    PairBox (1+n) (xs++[h*2;1+h*4]) (1+h*4).

Lemma PairBox_total n : exists xs h, PairBox n xs h.
Proof. induction n as [|n [xs [h H]]]; eauto using PairBox_base, PairBox_next. Qed.

Lemma PairBox_spec n xs h : PairBox n xs h ->
  length xs=2+n*2 /\ Half (Alt true (2+n*2)) 0 xs h xs h 0 /\
  exists tail, xs=0::0::tail.
Proof.
  intro H; induction H as [|n xs h H [EL [HB [tail ->]]]].
  - split; [reflexivity|split; [|exists (@nil nat); reflexivity]].
    change (Half ([true]++[false]) 0 ([0]++[0]) 0 ([0]++[0]) 0 0).
    eapply Half_box_extend; [apply Half_box_base; apply (Split_even true 0)|].
    apply (Split_even false 0).
  - split; [rewrite length_app; cbn in *; lia|split; [|exists (tail++[h*2;1+h*4]); reflexivity]].
    replace (2+(1+n)*2) with ((1+n)*2+2) by lia; rewrite Alt_app_even.
    replace ((1+n)*2) with (2+n*2) by lia.
    change (Half (Alt true (2+n*2)++[true;false]) 0
      ((0::0::tail)++[h*2;1+h*4]) (1+h*4)
      ((0::0::tail)++[h*2;1+h*4]) (1+h*4) 0).
    rewrite (app_assoc _ [true] [false]), (app_assoc _ [h*2] [1+h*4]).
    eapply Half_box_extend; [eapply Half_box_extend; [exact HB|constructor]|].
    replace (1+h*4) with (1+(h*2)*2) by lia; constructor.
Qed.

Lemma PairBox_capacity n xs h : PairBox n xs h -> h*3+1=4^n.
Proof. intro H; induction H; [reflexivity|]; change ((1+h*4)*3+1=4*4^n); rewrite <- IHPairBox; lia. Qed.

Lemma PairBox_budget n : forall xs h, PairBox (7+n) xs h ->
  (193+n*16)*(9+n)+1<=h.
Proof.
  induction n; intros xs h H.
  - repeat match goal with H : PairBox _ _ _ |- _ => inversion H; subst; clear H end; cbn; lia.
  - inversion H as [|j ys r HS]; subst; apply IHn in HS; nia.
Qed.

Definition RPrimeMiddle n := Alt true 3++Alt true 6++Ladder false 12 (1+n)++
  Alt false (2+24*2^n).

Lemma RPrime_parent n : Life Edge retire (RPrimeWord n) [1] (RPrimeMiddle n) [0;0].
Proof.
  pose proof (@Pass_ladder_tail n 12 ltac:(lia)) as HT.
  change (Pass (Ladder false 24 n++Alt false (2+24*2^n)) 12 (1+24*2^n)
    (Alt false 13++Ladder false 24 n)) in HT.
  assert (HP : Pass (Alt false 6++Alt true 12++Ladder false 24 n++Alt false (2+24*2^n))
    3 (1+24*2^n) (Alt true 3++Alt true 6++Ladder false 12 (1+n))).
  { eapply Pass_cat; [exact (@Pass_alt_even false 3 3 ltac:(left; lia))|].
    eapply Pass_cat; [exact (@Pass_alt_even true 6 6 ltac:(right; reflexivity))|exact HT]. }
  assert (EO : Nat.odd (1+24*2^n)=true).
  { replace (1+24*2^n) with (1+(12*2^n)*2) by lia; apply odd_1. }
  pose proof (@Life_terminal Edge retire 1 _ 1 3 _ _ [0;0] (Edge_even 1) HP) as HL.
  unfold retire in HL; rewrite EO in HL; cbn[negb] in HL.
  unfold RPrimeWord, RPrimeMiddle; rewrite <- !app_assoc in HL; exact HL.
Qed.

Lemma RPrime_internal n : Life Edge retire (RPrimeMiddle n) [0;0]
  (true::(Alt true 3++Ladder true 6 (3+n))) [0].
Proof.
  pose proof (@Pass_ladder_tail_low (1+n) 6 ltac:(lia) eq_refl) as HT.
  change (Pass (Ladder false 12 (1+n)++Alt false (2+12*(2*2^n))) 5
    (12*(2*2^n)) (Ladder true 6 (2+n))) in HT.
  replace (12*(2*2^n)) with (24*2^n) in HT by lia.
  assert (HP : Pass (RPrimeMiddle n) 0 (24*2^n)
    (true::(Alt true 3++Ladder true 6 (2+n)))).
  { unfold RPrimeMiddle; change (true::(Alt true 3++Ladder true 6 (2+n))) with
      ([true]++Alt true 3++Ladder true 6 (2+n)).
    eapply Pass_cat; [exact (@Pass_alt_odd_P 1 0)|].
    eapply Pass_cat; [exact (@Pass_alt_even true 3 2 ltac:(right; reflexivity))|exact HT]. }
  assert (EO : Nat.odd (24*2^n)=false).
  { replace (24*2^n) with ((12*2^n)*2) by lia; apply odd_0. }
  pose proof (@Life_internal Edge retire _ 0 [0] _ _ ltac:(discriminate) HP) as HL.
  unfold retire in HL; rewrite EO in HL; cbn[negb] in HL.
  replace (3+n) with ((2+n)+1) by lia; rewrite Ladder_snoc.
  replace (6*2^(2+n)) with (24*2^n) by (cbn[Nat.pow Nat.add]; lia).
  exact HL.
Qed.

Lemma CWord_zero_pairs n : forall b u,
  CWord false b 0 (repeat 0 (n*2)) u=Doubles b n++Alt false (b*4^n+u*2).
Proof.
  induction n; intros b u.
  - cbn[CWord repeat Doubles Nat.pow Nat.mul xorb app]; f_equal; lia.
  - replace (S n*2) with (2+n*2) by lia; cbn[repeat CWord Doubles Nat.add xorb negb].
    replace (b*2*2) with (b*4) by lia; rewrite IHn.
    rewrite <- !app_assoc; cbn[Nat.pow]; flia.
Qed.

Lemma PairWord_zero n u : PairWord (repeat 0 (4+n*2)) u=
  Alt true 3++Alt true 6++Doubles 12 (1+n)++Alt false (12*4^(1+n)+u*2).
Proof.
  change (PairWord (repeat 0 (4+n*2)) u) with
    (Alt true 3++Alt true 6++CWord false 12 0 (repeat 0 (2+n*2)) u).
  replace (2+n*2) with ((1+n)*2) by lia; rewrite CWord_zero_pairs; reflexivity.
Qed.

Lemma RPrime_terminal n : Life Edge retire (true::(Alt true 3++Ladder true 6 (4+n*2))) [0]
  (PairWord (repeat 0 (4+n*2)) (3+n)) [0;0].
Proof.
  pose proof (@Pass_ladder_P_pairs (1+n) 12 15 eq_refl eq_refl) as HT.
  replace (15+(1+n)*2+12*(4^(1+n)-1)) with (5+n*2+12*4^(1+n)) in HT by
    (pose proof (Nat.pow_nonzero 4 (1+n) ltac:(lia)); nia).
  assert (HP : Pass (true::Ladder true 6 (4+n*2)) 3 (5+n*2+12*4^(1+n))
    (Alt true 3++Alt true 6++Doubles 12 (1+n))).
  { apply Pass_P; change (Ladder true 6 (4+n*2)) with
      (Alt true 7++Alt true 13++Ladder true 24 (2+n*2)).
    eapply Pass_cat; [exact (@Pass_alt_odd_P 3 4)|].
    eapply Pass_cat; [exact (@Pass_alt_odd_P 6 8)|].
    replace (2+n*2) with ((1+n)*2) by lia; exact HT. }
  assert (EO : Nat.odd (5+n*2+12*4^(1+n))=true).
  { replace (5+n*2+12*4^(1+n)) with (1+(2+n+6*4^(1+n))*2) by lia; apply odd_1. }
  pose proof (@Life_terminal Edge retire 2 _ 0 3 _ _ [0;0] (Edge_even 1) HP) as HL.
  unfold retire in HL; rewrite EO in HL; cbn[negb] in HL.
  rewrite PairWord_zero; rewrite <- !app_assoc in HL; applys_eq HL; flia.
Qed.

Theorem RPrime_entry n : Lives Edge retire 3 (RPrimeWord (1+n*2)) [1]
  (PairWord (repeat 0 (4+n*2)) (3+n)) [0;0].
Proof.
  eapply Lives_cons; [apply RPrime_parent|].
  eapply Lives_cons; [apply RPrime_internal|].
  econstructor; [apply RPrime_terminal|constructor].
Qed.

(* This shift transports the unit-routing table, not the full Tick map. *)
Fixpoint RouteShift (p:bool) (xs:list nat) := match xs with []=>[] |
  a::xs => ((if p then 3 else 1)+a)::RouteShift (negb p) xs end.
Definition RouteOffset i := if Nat.odd i then 3 else 1.
Definition PairMove N i a j := TM2.Move N i (RouteOffset i+a) j.

Lemma RouteShift_nth xs : forall p i, i<length xs ->
  nth i (RouteShift p xs) 0=(if xorb p (Nat.odd i) then 3 else 1)+nth i xs 0.
Proof.
  induction xs; intros p [|i] HI; cbn[RouteShift nth length] in *; try lia.
  - rewrite xorb_false_r; reflexivity.
  - rewrite IHxs by lia; rewrite odd_S.
    destruct p, (Nat.odd i); reflexivity.
Qed.

Lemma RouteShift_bump i a xs ys : Bump i a xs ys -> forall p,
  Bump i ((if xorb p (Nat.odd i) then 3 else 1)+a) (RouteShift p xs) (RouteShift p ys).
Proof.
  intro H; induction H; intro p; cbn[RouteShift].
  - rewrite xorb_false_r.
    replace ((if p then 3 else 1)+(1+a)) with (1+((if p then 3 else 1)+a)) by lia; constructor.
  - rewrite odd_S; replace (xorb p (negb (Nat.odd i))) with
      (xorb (negb p) (Nat.odd i)) by (destruct p, (Nat.odd i); reflexivity).
    constructor; apply IHBump.
Qed.

Lemma PairMove_forward N i a q r flag : 1<i -> (flag=true -> 2<i) ->
  Split (Nat.odd i) a q r -> xorb (Nat.odd i) (Nat.odd a)=true ->
  xorb (negb (Nat.odd i)) (Nat.odd q)=flag ->
  PairMove N i a (if flag then i-2 else 0).
Proof.
  intros HI HF HS HE HQ; pose proof (Split_forward HS HE) as E.
  unfold PairMove, RouteOffset.
  destruct (mod2 q) as [b EQ|b EQ]; subst q; rewrite ?odd_0, ?odd_1 in HQ;
    destruct (Nat.odd i) eqn:EI; destruct flag; cbn in HQ, E; try discriminate.
  - replace (3+a) with (3+b*4) by lia; constructor; auto.
  - replace (1+a) with (2+b*4) by lia; constructor; auto.
  - replace (3+a) with (1+(1+b)*4) by lia; constructor; auto.
  - replace (1+a) with ((1+b)*4) by lia; constructor; auto.
Qed.

Lemma Pair_alt_route N root out i a j b k c : 1<N -> Nat.odd N=false ->
  AltMove true N root i a j b -> AltMove true N out j b k c -> PairMove N i a k.
Proof.
  intros HN EN H1 H2.
  destruct H1 as [a0|i0 a0 HI HE|i0 a0 q0 r0 HI HS HE];
    inversion H2 as [a1|i1 a1 HI1 HE1|i1 a1 q1 r1 HI1 HS1 HE1]; subst;
    cbn[xorb] in *; try lia.
  - unfold PairMove, RouteOffset; cbn; apply TM2.Move_root.
    rewrite odd_S, EN in *; cbn in HE1; apply negb_true_iff in HE1; rewrite HE1; reflexivity.
  - unfold PairMove, RouteOffset; cbn; apply TM2.Move_root.
    rewrite odd_S, EN in *; cbn in HE1; rewrite HE1; reflexivity.
  - unfold PairMove; apply TM2.Move_return; [exact HI|].
    unfold RouteOffset; rewrite Nat.odd_add.
    destruct (Nat.odd i0), (Nat.odd a0); cbn in *; congruence.
  - eapply PairMove_forward with (flag:=false); [exact HI|discriminate| | |].
    + destruct (Nat.odd i0); exact HS.
    + destruct (Nat.odd i0); exact HE.
    + rewrite odd_pred in HE1 by lia.
      destruct (Nat.odd i0), (Nat.odd q0); cbn in *; congruence.
  - replace (i0-1-1) with (i0-2) by lia.
    eapply PairMove_forward with (flag:=true); [exact HI|lia| | |].
    + destruct (Nat.odd i0); exact HS.
    + destruct (Nat.odd i0); exact HE.
    + rewrite odd_pred in HE1 by lia.
      destruct (Nat.odd i0), (Nat.odd q0); cbn in *; congruence.
Qed.

Lemma Pair_tick_route n xs u ys v xs' u' ys' v' i a :
  Tick (Alt true (2+n*2)) false xs u ys v 0 ->
  Tick (Alt true (2+n*2)) false xs' u' ys' v' 0 ->
  Bump i a (u::xs) (u'::xs') -> exists j b,
  PairMove (2+n*2) i a j /\ Bump j b (v::ys) (v'::ys').
Proof.
  intros H H' HU. destruct (Tick_length H) as [EL _]; rewrite Alt_length in EL.
  destruct (Bump_length HU) as [_ IL]; cbn in IL.
  destruct (Tick_bump H H' HU) as [root [j [b [k [c [HM [HM' HB]]]]]]].
  assert (HJ : j<=2+n*2).
  { eapply HalfMove_bound in HM; [rewrite Alt_length in HM; exact HM|rewrite Alt_length; lia]. }
  exists k,c; split; [|exact HB].
  eapply Pair_alt_route; [lia|change (Nat.odd ((1+n)*2)=false); apply odd_0| |].
  - apply HalfMove_alt; [exact HM|lia].
  - apply HalfMove_alt; [exact HM'|exact HJ].
Qed.

Lemma PairMove_waiting N xs ys i a j : 1<N -> Nat.odd N=false ->
  Bump i a xs ys -> PairMove N i a j ->
  Waiting 0 (RouteShift false xs) i -> Waiting N (RouteShift false xs) i ->
  Waiting 0 (RouteShift false ys) j /\ Waiting N (RouteShift false ys) j.
Proof.
  intros HN EN HB HM; eapply TM2.Move_waiting; [exact HN|exact EN| |exact HM].
  exact (RouteShift_bump HB false).
Qed.

Lemma PairApart_shift N n xs i k ys j l : Apart (PairMove N) n xs i k ys j l ->
  length xs=1+N -> i<=N -> k<=N ->
  Apart (TM2.Move N) n (RouteShift false xs) i k (RouteShift false ys) j l.
Proof.
  intro H; induction H; intros EL HI HK; [constructor; assumption|].
  assert (HJ : j<=N) by (eapply TM2.Move_bound; eassumption).
  assert (HL : l<=N) by (eapply TM2.Move_bound; eassumption).
  econstructor; [exact H|exact (RouteShift_bump H0 false)|exact H1| |].
  - rewrite RouteShift_nth by lia; exact H2.
  - apply IHApart; [pose proof (Bump_length H0); lia|exact HJ|exact HL].
Qed.

Theorem PairApart_bound m n xs i k ys j l : 2<=m ->
  Apart (PairMove (m*2)) n xs i k ys j l -> length xs=1+m*2 -> i<=m*2 -> k<=m*2 ->
  Waiting 0 (RouteShift false xs) i -> Waiting (m*2) (RouteShift false xs) i ->
  n<=m*12+20.
Proof.
  intros HM H EL HI HK H0 HN.
  eapply TM2.Apart_bound; [exact HM|eapply PairApart_shift; eassumption|exact HI|exact HK|exact H0|exact HN].
Qed.

Lemma Pair_tick_route_even m xs u ys v xs' u' ys' v' i a : 0<m ->
  Tick (Alt true (m*2)) false xs u ys v 0 ->
  Tick (Alt true (m*2)) false xs' u' ys' v' 0 ->
  Bump i a (u::xs) (u'::xs') -> exists j b,
  PairMove (m*2) i a j /\ Bump j b (v::ys) (v'::ys').
Proof. destruct m; [lia|intros _; apply Pair_tick_route]. Qed.

Lemma Pair_initial_bump m xs u : 0<m ->
  Tick (Alt true (m*2)) false (repeat 0 (m*2)) 0 xs u 0 ->
  Bump 0 0 (0::repeat 0 (m*2)) (u::xs).
Proof.
  destruct m; [lia|intros _ HT].
  pose proof (Tick_late_zeros true (Alt false (1+m*2))) as H.
  rewrite Alt_length in H.
  destruct (Tick_functional HT H) as [-> [-> _]]; constructor.
Qed.

Lemma Pair_canonical_waiting m n : 2<=m -> forall xs u ys v i a,
  Ticks (Alt true (m*2)) false n (repeat 0 (m*2)) 0 xs u ->
  Tick (Alt true (m*2)) false xs u ys v 0 -> Bump i a (u::xs) (v::ys) ->
  Waiting 0 (RouteShift false (u::xs)) i /\
  Waiting (m*2) (RouteShift false (u::xs)) i.
Proof.
  intro HM; induction n; intros xs u ys v i a HP HT HB.
  - inversion HP; subst.
    destruct (Bump_position HB (Pair_initial_bump (m:=m) ltac:(lia) HT)) as [-> ->].
    split; [left; reflexivity|right].
    rewrite RouteShift_nth by (cbn[length]; rewrite repeat_length; lia).
    rewrite odd_0; cbn[xorb]; change (Nat.odd (1+nth (m*2) (repeat 0 (1+m*2)) 0)=true).
    rewrite nth_repeat; reflexivity.
  - destruct (Ticks_unsnoc HP) as [prev [root [HR HS]]].
    assert (HU : One (root::prev) (u::xs)).
    { eapply (@Ticks_zero_unit (Alt true (m*2)) false n); rewrite Alt_length; eassumption. }
    destruct (One_bump HU) as [p [b Hprev]].
    destruct (IHn _ _ _ _ _ _ HR HS Hprev) as [HW0 HWN].
    destruct (Pair_tick_route_even (m:=m) ltac:(lia) HS HT Hprev) as [j [c [HD Hnext]]].
    destruct (Bump_position Hnext HB) as [-> _].
    eapply PairMove_waiting; [lia|apply odd_0|exact Hprev|exact HD|exact HW0|exact HWN].
Qed.

Lemma Pair_couple_ticks m j t xs u noise z endc w endn q : 2<=m -> m*12+20<t ->
  Ticks (Alt true (m*2)) false j (repeat 0 (m*2)) 0 xs u ->
  Ticks (Alt true (m*2)) false (1+t) xs u endc w ->
  Ticks (Alt true (m*2)) false t noise z endn q ->
  One (u::xs) (z::noise) -> exists s ys root,
  s<=t /\ Ticks (Alt true (m*2)) false s noise z ys root /\
  Ticks (Alt true (m*2)) false (1+s) xs u ys root.
Proof.
  intros HM Ht HP HC HN HU.
  inversion HC as [|n0 xs0 u0 next v endc0 w0 HT HR]; subst.
  assert (HV : One (u::xs) (v::next)).
  { eapply (@Ticks_zero_unit (Alt true (m*2)) false j); rewrite Alt_length;
      [exact HP|eapply Ticks_snoc; eassumption]. }
  destruct (One_bump HV) as [i [a HB]]; destruct (One_bump HU) as [k [b HK]].
  destruct (Pair_canonical_waiting (m:=m) HM HP HT HB) as [HW0 HWN].
  destruct (@Ticks_couple_or_apart (Alt true (m*2)) false (PairMove (m*2))
    (fun _ _ _ _ _ _ _ _ _ _ => @Pair_tick_route_even m _ _ _ _ _ _ _ _ _ _ ltac:(lia))
    t _ _ _ _ _ _ _ _ _ _ _ _ _ _ HT HR HN HB HK) as [HJ|[last [l [r HA]]]]; [exact HJ|].
  destruct (Tick_length HT) as [EL _]; rewrite Alt_length in EL.
  destruct (Bump_length HB) as [_ HI]; destruct (Bump_length HK) as [_ Hk]; cbn in HI, Hk.
  pose proof (@PairApart_bound m t (u::xs) i k last l r HM HA ltac:(cbn; lia)
    ltac:(lia) ltac:(lia) HW0 HWN); lia.
Qed.

Lemma Pair_seed_absorbs m bounds h C : 2<=m -> m*12+20<C ->
  Half (Alt true (m*2)) 0 bounds h bounds h 0 -> forall k, k*(C+1)+1<=h ->
  exists t xs u, t<=k*C /\
  Ticks (Alt true (m*2)) false t (repeat 0 (m*2)) k xs u /\
  Ticks (Alt true (m*2)) false (t+k) (repeat 0 (m*2)) 0 xs u /\ Forall2 le xs bounds.
Proof.
  intros HM HC HB.
  pose proof (@Ticks_seed_absorbs (Alt true (m*2)) false bounds h C HB) as H.
  rewrite Alt_length in H; apply H; intros.
  eapply Pair_couple_ticks; eassumption.
Qed.

Theorem Pair_seed_absorption n : exists t xs u,
  t<=(9+n)*(192+n*16) /\
  Ticks (Alt true (16+n*2)) false t (repeat 0 (16+n*2)) (9+n) xs u /\
  Ticks (Alt true (16+n*2)) false (t+(9+n)) (repeat 0 (16+n*2)) 0 xs u /\
  Lives Edge retire (t*2) (PairWord (repeat 0 (16+n*2)) (9+n)) [0;0]
    (PairWord xs u) [0;0].
Proof.
  destruct (PairBox_total (7+n)) as [bounds [h HB]].
  destruct (PairBox_spec HB) as [_ [HC _]]; pose proof (PairBox_budget HB) as HM.
  replace (2+(7+n)*2) with ((8+n)*2) in HC by lia.
  destruct (@Pair_seed_absorbs (8+n) bounds h (192+n*16) ltac:(lia) ltac:(lia) HC (9+n) ltac:(nia))
    as [t [xs [u [Ht [HR [HP HX]]]]]].
  replace ((8+n)*2) with (16+n*2) in HR, HP by lia.
  exists t,xs,u; repeat split; try assumption.
  apply (Pair_ticks_lives (7+n)); applys_eq HR; flia.
Qed.

Import TM2 (Quarter, Quarter_positive, Quarter_power, OddRow, EvenRow, OddRow_length, EvenRow_length, OddRow_count, EvenRow_count).

(* Positions 2,...,2n+1; their alternating rows reuse TM2's two row words,
   but the first and last vertices and their visit counts are different. *)
Fixpoint PairCertBody N n : list (list nat) := match n with
  | 0=>[] | S k=>PairCertBody N k++
    [OddRow N (k*2) (Quarter k); EvenRow N (1+k*2) (Quarter k)] end.
Definition PairRoot N n := Cycles [0;N-1] (1+Quarter n*2).
Definition PairLast N n := Cycles [N;N-2;N;0] (Quarter n).
Definition PairRows n := PairRoot (2+n*2) n :: [3+n*2] ::
  (PairCertBody (2+n*2) n++[PairLast (2+n*2) n]).

Lemma PairCertBody_length N n : length (PairCertBody N n)=n*2.
Proof. induction n; cbn[PairCertBody]; rewrite ?length_app, ?IHn; cbn[length]; lia. Qed.

Lemma PairRoot_length N n : length (PairRoot N n)=2+Quarter n*4.
Proof. unfold PairRoot; rewrite Cycles_length; cbn[length]; lia. Qed.

Lemma PairLast_length N n : length (PairLast N n)=Quarter n*4.
Proof. unfold PairLast; rewrite Cycles_length; reflexivity. Qed.

Lemma PairRoot_count N n v : count_occ Nat.eq_dec (PairRoot N n) v=
  (1+Quarter n*2)*mark 0 v+(1+Quarter n*2)*mark (N-1) v.
Proof. unfold PairRoot; rewrite Cycles_count, !count_cons; cbn[count_occ]; nia. Qed.

Lemma PairLast_count N n v : count_occ Nat.eq_dec (PairLast N n) v=
  Quarter n*2*mark N v+Quarter n*mark (N-2) v+Quarter n*mark 0 v.
Proof. unfold PairLast; rewrite Cycles_count, !count_cons; cbn[count_occ]; nia. Qed.

Lemma PairCertBody_balance N n v : incoming (PairCertBody N n) v +
  Quarter n*mark (n*2) v+(1+Quarter n*2)*mark (1+n*2) v =
  weighted (PairCertBody N n) 2 v+Quarter n*2*mark N v+Quarter n*mark 0 v+mark 1 v.
Proof.
  induction n as [|n IH]; [cbn[Quarter PairCertBody incoming weighted concat count_occ Nat.add Nat.mul]; lia|].
  change (incoming (PairCertBody N n++[OddRow N (n*2) (Quarter n);EvenRow N (1+n*2) (Quarter n)]) v+
    (1+Quarter n*4)*mark (2+n*2) v+(1+(1+Quarter n*4)*2)*mark (3+n*2) v=
    weighted (PairCertBody N n++[OddRow N (n*2) (Quarter n);EvenRow N (1+n*2) (Quarter n)]) 2 v+
    (1+Quarter n*4)*2*mark N v+(1+Quarter n*4)*mark 0 v+mark 1 v).
  unfold incoming in *; rewrite concat_app, count_occ_app, weighted_app, PairCertBody_length.
  cbn[concat weighted]; rewrite !count_occ_app, OddRow_count, EvenRow_count, OddRow_length, EvenRow_length.
  cbn[count_occ]; replace (n*2+2) with (2+n*2) by lia.
  cbn[Nat.add] in *; ring_simplify in IH; ring_simplify; lia.
Qed.

Lemma PairRows_length n : length (PairRows n)=3+n*2.
Proof. unfold PairRows; cbn[length]; rewrite length_app, PairCertBody_length; cbn; lia. Qed.

Theorem PairRows_balance n : Balance (PairRows n) 0 (3+n*2).
Proof.
  intro v; pose proof (PairCertBody_balance (2+n*2) n v) as HB.
  unfold PairRows, incoming; cbn[concat]; rewrite concat_app; cbn[concat].
  rewrite !count_occ_app, PairRoot_count, count_cons,
    PairLast_count; cbn[count_occ].
  rewrite <- weighted_outgoing; cbn[weighted].
  rewrite PairRoot_length, weighted_app, PairCertBody_length; cbn[weighted]; rewrite PairLast_length.
  replace (2+n*2-1) with (1+n*2) by lia; replace (2+n*2-2) with (n*2) by lia.
  replace (n*2+2) with (2+n*2) by lia.
  unfold incoming in HB; cbn[length Nat.add] in *; ring_simplify in HB; ring_simplify.
  replace (n*2+2) with (2+n*2) by lia; cbn[Nat.add] in *; lia.
Qed.

Lemma PairCertBody_at N n : forall k, k<n ->
  nth (k*2) (PairCertBody N n) []=OddRow N (k*2) (Quarter k) /\
  nth (1+k*2) (PairCertBody N n) []=EvenRow N (1+k*2) (Quarter k).
Proof.
  induction n as [|n IH]; intros k HK; [lia|].
  destruct (Nat.eq_dec k n) as [->|Hne]; cbn[PairCertBody].
  - rewrite !app_nth2 by (rewrite PairCertBody_length; lia).
    rewrite PairCertBody_length, Nat.sub_diag.
    replace (1+n*2-n*2) with 1 by lia; split; reflexivity.
  - rewrite !app_nth1 by (rewrite PairCertBody_length; lia); apply IH; lia.
Qed.

Definition PairExitRank n i := if i=?3+n*2 then 0 else
  if Nat.odd i then (1+i)/2 else if i=?0 then n+2 else
  if i=?2+n*2 then n+3 else n+4.

Lemma PairExitRank_root n : PairExitRank n 0=n+2.
Proof. unfold PairExitRank; reflexivity. Qed.

Lemma PairExitRank_sink n : PairExitRank n (3+n*2)=0.
Proof. unfold PairExitRank; rewrite Nat.eqb_refl; reflexivity. Qed.

Lemma PairExitRank_odd n k : k<=n -> PairExitRank n (1+k*2)=1+k.
Proof.
  intro H; unfold PairExitRank; rewrite odd_1.
  assert (E : (1+k*2=?3+n*2)=false) by (apply Nat.eqb_neq; lia).
  rewrite E; replace (1+(1+k*2)) with ((1+k)*2) by lia; rewrite Nat.div_mul by lia; reflexivity.
Qed.

Lemma PairExitRank_even n k : 0<k -> k<=1+n ->
  PairExitRank n (k*2)=if k=?1+n then n+3 else n+4.
Proof.
  intros H K; unfold PairExitRank; rewrite odd_0.
  assert (E : (k*2=?3+n*2)=false) by (apply Nat.eqb_neq; lia).
  assert (F : (k*2=?0)=false) by (apply Nat.eqb_neq; lia).
  rewrite E,F; destruct (k=?1+n) eqn:G; destruct (k*2=?2+n*2) eqn:J;
    try reflexivity; apply Nat.eqb_eq in G || apply Nat.eqb_neq in G;
    apply Nat.eqb_eq in J || apply Nat.eqb_neq in J; lia.
Qed.

Theorem PairRows_forest n : LastForest (PairExitRank n) (PairRows n).
Proof.
  intros i Hne; assert (HI : i<3+n*2).
  { destruct (Nat.lt_ge_cases i (length (PairRows n))) as [HL|HL].
    - rewrite PairRows_length in HL; exact HL.
    - rewrite nth_overflow in Hne by lia; contradiction. }
  destruct i as [|[|i]].
  - change (PairExitRank n (last (PairRoot (2+n*2) n) 0)<PairExitRank n 0).
    unfold PairRoot; rewrite Cycles_last by discriminate; cbn[last].
    replace (2+n*2-1) with (1+n*2) by lia.
    rewrite PairExitRank_odd, PairExitRank_root by lia; lia.
  - change (PairExitRank n (3+n*2)<PairExitRank n 1).
    rewrite PairExitRank_sink, (PairExitRank_odd (k:=0)) by lia; lia.
  - change (PairExitRank n (last (nth i (PairCertBody (2+n*2) n++[PairLast (2+n*2) n]) []) 0)
      <PairExitRank n (2+i)).
    destruct (Nat.eq_dec i (n*2)) as [->|Hlast].
    + rewrite app_nth2 by (rewrite PairCertBody_length; lia).
      rewrite PairCertBody_length, Nat.sub_diag; cbn[nth].
      destruct n; [contradiction|].
      unfold PairLast; rewrite Cycles_last; [|discriminate|cbn[Quarter]; lia].
      cbn[last]; rewrite PairExitRank_root.
      replace (2+S n*2) with ((1+S n)*2) by lia.
      rewrite PairExitRank_even, Nat.eqb_refl by lia; lia.
    + rewrite app_nth1 by (rewrite PairCertBody_length; lia).
      destruct (mod2 i) as [k E|k E]; subst i.
      * rewrite (proj1 (PairCertBody_at (2+n*2) (n:=n) (k:=k) ltac:(lia))).
        unfold OddRow; rewrite last_suffix by discriminate; cbn[last].
        replace (2+n*2) with ((1+n)*2) by lia.
        replace (2+k*2) with ((1+k)*2) by lia.
        rewrite !PairExitRank_even, Nat.eqb_refl by lia.
        assert (E : (1+k=?1+n)=false) by (apply Nat.eqb_neq; lia); rewrite E; lia.
      * rewrite (proj2 (PairCertBody_at (2+n*2) (n:=n) (k:=k) ltac:(lia))).
        unfold EvenRow; rewrite last_suffix by discriminate; cbn[last].
        replace (2+(1+k*2)) with (1+(1+k)*2) by lia.
        rewrite !PairExitRank_odd by lia; lia.
Qed.

Lemma PairCertBody_budget N n : length (concat (PairCertBody N n))=Quarter n*4.
Proof.
  induction n; [reflexivity|].
  cbn[PairCertBody]; rewrite concat_app, length_app, IHn.
  cbn[concat]; rewrite !length_app, OddRow_length, EvenRow_length.
  cbn[length Quarter]; lia.
Qed.

Lemma PairRows_budget n : length (concat (PairRows n))=Quarter (1+n)*3.
Proof.
  unfold PairRows; cbn[concat].
  rewrite !length_app, concat_app, length_app, PairRoot_length, PairCertBody_budget.
  cbn[concat]; rewrite length_app, PairLast_length; cbn[length Quarter Nat.add]; lia.
Qed.

Theorem Pair_stack_exit n : exists rows',
  StackWalk 0 (PairRows n) (3+n*2) rows' (Quarter (1+n)*3) /\
  forall i, nth i rows' []=[].
Proof.
  pose proof (stack_certificate (PairRows_balance n) (PairRows_forest n)) as H.
  rewrite PairRows_budget in H; exact H.
Qed.

Definition PairExitMove N i a j := PairMove N i a j \/ (i=1 /\ a=0 /\ j=1+N).

Lemma PairRoot_rules N n : Indexed (PairMove N 0) 0 (PairRoot N n).
Proof.
  unfold PairRoot; rewrite <- (app_nil_r (Cycles _ _)).
  change (Indexed (PairMove N 0) (0*length [0;N-1]) (Cycles [0;N-1] (1+Quarter n*2)++[])).
  apply Indexed_cycles; [|exact (fun _=>I)].
  intro a; cbn[length Indexed]; unfold PairMove, RouteOffset; cbn.
  split; [constructor|split; [|exact I]].
  change (TM2.Move N 0 (2+a*2) (N-1)).
  replace (2+a*2) with ((1+a)*2) by lia; constructor.
Qed.

Lemma PairEven_rules N i q : 2<i -> Nat.odd i=false ->
  Indexed (PairMove N i) 0 (OddRow N (i-2) q).
Proof.
  intros HI HE; unfold OddRow.
  change (Indexed (PairMove N i) (0*length [N;i-2;N;0]) (Cycles [N;i-2;N;0] q++[N])).
  apply Indexed_cycles; intro a; cbn[length Indexed]; unfold PairMove, RouteOffset; rewrite HE; repeat split.
  - replace (1+a*4) with (1+(a*2)*2) by lia; constructor; auto; lia.
  - replace (1+(1+a*4)) with (2+a*4) by lia; constructor; auto.
  - replace (1+(1+(1+a*4))) with (1+(1+a*2)*2) by lia; constructor; auto; lia.
  - replace (1+(1+(1+(1+a*4)))) with ((1+a)*4) by lia; constructor; auto; lia.
  - replace (1+a*4) with (1+(a*2)*2) by lia; constructor; auto; lia.
Qed.

Lemma PairOdd_rules N i q : 2<i -> Nat.odd i=true ->
  Indexed (PairMove N i) 0 (EvenRow N (i-2) q).
Proof.
  intros HI HE; unfold EvenRow.
  change (Indexed (PairMove N i) (0*length [0;N;i-2;N])
    (Cycles [0;N;i-2;N] (q*2)++[0;N;i-2])).
  apply Indexed_cycles; intro a; cbn[length Indexed]; unfold PairMove, RouteOffset; rewrite HE; repeat split.
  - constructor; auto; lia.
  - replace (3+(1+a*4)) with ((2+a*2)*2) by lia; constructor; auto; lia.
  - replace (3+(1+(1+a*4))) with (1+(1+a)*4) by lia; constructor; auto.
  - replace (3+(1+(1+(1+a*4)))) with ((3+a*2)*2) by lia; constructor; auto; lia.
  - constructor; auto; lia.
  - replace (3+(1+a*4)) with ((2+a*2)*2) by lia; constructor; auto; lia.
  - replace (3+(1+(1+a*4))) with (1+(1+a)*4) by lia; constructor; auto.
Qed.

Lemma PairLast_rules n : Indexed (PairMove (2+n*2) (2+n*2)) 0 (PairLast (2+n*2) n).
Proof.
  destruct n; [exact I|].
  pose proof (@PairEven_rules (2+S n*2) (2+S n*2) (Quarter (S n)) ltac:(lia)
    ltac:(change (Nat.odd ((2+n)*2)=false); apply odd_0)) as H.
  unfold OddRow in H; rewrite Indexed_app in H; exact (proj1 H).
Qed.

Lemma PairRows_rules n : RowRules (PairExitMove (2+n*2)) (PairRows n) (repeat 0 (3+n*2)).
Proof.
  rewrite <- PairRows_length; apply RowRules_initial; intro i.
  destruct (Nat.lt_ge_cases i (length (PairRows n))) as [HI|HI];
    [rewrite PairRows_length in HI|rewrite nth_overflow by lia; exact I].
  destruct i as [|[|i]].
  - change (Indexed (PairExitMove (2+n*2) 0) 0 (PairRoot (2+n*2) n)).
    eapply Indexed_mono; [intros; left; eassumption|apply PairRoot_rules].
  - change (PairExitMove (2+n*2) 1 0 (3+n*2) /\ True); split; [right; auto|exact I].
  - change (Indexed (PairExitMove (2+n*2) (2+i)) 0
      (nth i (PairCertBody (2+n*2) n++[PairLast (2+n*2) n]) [])).
    destruct (Nat.eq_dec i (n*2)) as [->|Hlast].
    + rewrite app_nth2 by (rewrite PairCertBody_length; lia).
      rewrite PairCertBody_length, Nat.sub_diag; cbn[nth].
      eapply Indexed_mono; [intros; left; eassumption|apply PairLast_rules].
    + rewrite app_nth1 by (rewrite PairCertBody_length; lia).
      destruct (mod2 i) as [k E|k E]; subst i.
      * rewrite (proj1 (PairCertBody_at (2+n*2) (n:=n) (k:=k) ltac:(lia))).
        destruct k as [|k].
        -- change (PairExitMove (2+n*2) 2 0 (2+n*2) /\ True); split; [|exact I].
           left; unfold PairMove, RouteOffset; change (TM2.Move (2+n*2) 2 (1+0*2) (2+n*2)).
           constructor; reflexivity || lia.
        -- replace (S k*2) with (2+S k*2-2) at 2 by lia.
           eapply Indexed_mono; [intros; left; eassumption|apply PairEven_rules; [lia|]].
           change (Nat.odd ((2+k)*2)=false); apply odd_0.
      * rewrite (proj2 (PairCertBody_at (2+n*2) (n:=n) (k:=k) ltac:(lia))).
        replace (1+k*2) with (2+(1+k*2)-2) at 2 by lia.
        eapply Indexed_mono; [intros; left; eassumption|apply PairOdd_rules; [lia|]].
        change (Nat.odd (1+(1+k)*2)=true); apply odd_1.
Qed.

Lemma PairRows_front n : nth 1 (PairRows n) []=[3+n*2] /\
  length (nth 2 (PairRows n) [])<=1.
Proof.
  split; [reflexivity|].
  destruct n; [change (0<=1); lia|].
  change (length (nth 0 (PairCertBody (2+S n*2) (S n)++[PairLast (2+S n*2) (S n)]) [])<=1).
  rewrite app_nth1 by (rewrite PairCertBody_length; lia).
  pose proof (proj1 (PairCertBody_at (2+S n*2) (n:=S n) (k:=0) ltac:(lia))) as E.
  change (nth 0 (PairCertBody (2+S n*2) (S n)) []=[2+S n*2]) in E.
  rewrite E; reflexivity.
Qed.

Lemma PairRows_sink n rows xs : RowRules (PairExitMove (2+n*2)) rows xs ->
  VisitBudget (PairRows n) rows xs -> nth (3+n*2) rows []=[].
Proof.
  intros [EL HR] [ES HV]; apply nth_overflow; rewrite PairRows_length in ES; lia.
Qed.

Lemma PairRows_safe n rows xs i : RowRules (PairExitMove (2+n*2)) rows xs ->
  VisitBudget (PairRows n) rows xs -> Balance rows i (3+n*2) -> i<>3+n*2 ->
  nth 1 xs 0=0 /\ nth 2 xs 0<=1.
Proof.
  intros HR HV HF HI; split.
  - pose proof (PairRows_sink HR HV) as HE.
    specialize (HF (3+n*2)); unfold outgoing in HF; rewrite HE, mark_self, mark_other in HF by assumption.
    cbn[length] in HF.
    destruct (incoming_witness rows (3+n*2) ltac:(lia)) as [j [HJ HJ']].
    destruct HR as [EL HR]; destruct HV as [ES HV].
    destruct (Indexed_in (HR j) HJ') as [a [HA [HD|[-> [-> _]]]]]; [|lia].
    unfold PairMove in HD.
    pose proof (TM2.Move_bound HD ltac:(rewrite PairRows_length in ES; lia)); lia.
  - pose proof (VisitBudget_bound 2 HV) as HB.
    pose proof (proj2 (PairRows_front n)); unfold outgoing in HB; lia.
Qed.

Lemma Pair_tick_available n xs u : length xs=2+n*2 ->
  nth 0 xs 0=0 -> nth 1 xs 0<=1 ->
  exists ys v, Tick (Alt true (2+n*2)) false xs u ys v 0.
Proof.
  intros EL H1 H2; destruct xs as [|a [|b xs]]; cbn[length] in EL; try lia.
  change (a=0) in H1; subst a; change (b<=1) in H2.
  destruct (Split_total false b) as [q [r HQ]].
  assert (Hq : q=0) by (inversion HQ; subst; lia); subst q.
  destruct (Scatter_total (Alt true (n*2)) xs ltac:(rewrite Alt_length; lia)) as [qs [s HS]].
  assert (HA : Half (Alt true (2+n*2)) 0 (0::b::xs) u (0::(qs++[u])) (r+s) 0).
  { apply (Half_make 0 u (qs:=0::qs) (r:=r+s)).
    exact (Scatter_cons (Split_even true 0) (Scatter_cons HQ HS)). }
  destruct (@Half_front_total true (Alt false (1+n*2)) 0 (qs++[u]) (r+s) 1)
    as [ys [v HB]]; [pose proof (Scatter_length HS); rewrite Alt_length in *; rewrite length_app; cbn[length]; lia|
      apply (Split_even true 0)|].
  exists ys,v; exact (Tick_make false HA HB).
Qed.

Lemma Pair_stack_ticks n i rows j rows' t : StackWalk i rows j rows' t ->
  forall xs u next v a, RowRules (PairExitMove (2+n*2)) rows (u::xs) ->
  VisitBudget (PairRows n) rows (u::xs) -> Balance rows i (3+n*2) ->
  Tick (Alt true (2+n*2)) false xs u next v 0 -> Bump i a (u::xs) (v::next) ->
  exists ys w, Ticks (Alt true (2+n*2)) false t xs u ys w /\ VisitBudget (PairRows n) rows' (w::ys).
Proof.
  intro HW; induction HW as [i rows|i j k rows rows' rows'' t HP HW IH];
    intros xs u next v a HR HV HF HT HB.
  - exists xs,u; split; [constructor|assumption].
  - destruct (RowRules_pop HR HP HB) as [HD HR']; pose proof (VisitBudget_pop HV HP HB) as HV'.
    pose proof (Pop_balance HP HF) as HF'.
    destruct (Nat.eq_dec j (3+n*2)) as [HJ|HJ].
    + pose proof (PairRows_sink HR' HV') as HE; rewrite <- HJ in HE.
      destruct (StackWalk_stuck HW HE) as [EJ [EN ER]]; subst.
      exists next,v; split; [eapply Ticks_cons; [exact HT|constructor]|exact HV'].
    + destruct (PairRows_safe HR' HV' HF' HJ) as [H1 H2].
      destruct (Tick_length HT) as [EL EN]; rewrite Alt_length in EL.
      destruct (@Pair_tick_available n next v ltac:(lia) H1 H2) as [next' [v' HT']].
      destruct (Pair_tick_route n HT HT' HB) as [j' [a' [HD' HB']]].
      destruct HD as [HD|[_ [_ HE]]]; [|contradiction].
      pose proof (TM2.Move_functional HD HD') as ->.
      destruct (IH next v next' v' a' HR' HV' HF' HT' HB') as [ys [w [HX HY]]].
      exists ys,w; split; [eapply Ticks_cons; eassumption|assumption].
Qed.

Theorem Pair_canonical_exit n : exists xs u,
  Ticks (Alt true (2+n*2)) false (Quarter (1+n)*3) (repeat 0 (2+n*2)) 0 xs u /\
  u::xs=map (@length nat) (PairRows n) /\
  Lives Edge retire (Quarter (1+n)*3*2) (PairWord (repeat 0 (2+n*2)) 0) [0;0]
    (PairWord xs u) [0;0].
Proof.
  destruct (Pair_stack_exit n) as [rows' [HW HE]].
  destruct (@Pair_tick_available n (repeat 0 (2+n*2)) 0 ltac:(rewrite repeat_length; reflexivity)
    ltac:(rewrite nth_repeat; reflexivity) ltac:(rewrite nth_repeat; lia)) as [next [v HT]].
  pose proof (Pair_initial_bump (m:=1+n) ltac:(lia) HT) as HB.
  pose proof (PairRows_rules n) as HR.
  pose proof (VisitBudget_initial (PairRows n)) as HV; rewrite PairRows_length in HV.
  destruct (@Pair_stack_ticks n 0 (PairRows n) (3+n*2) rows' (Quarter (1+n)*3)
    HW (repeat 0 (2+n*2)) 0 next v 0 HR HV (PairRows_balance n) HT HB) as [xs [u [HX HY]]].
  exists xs,u; split; [exact HX|split; [eapply VisitBudget_done; eassumption|]].
  apply (Pair_ticks_lives n); exact HX.
Qed.

Definition PairExitBody n := 1::(TM2.ExitBody n++[Quarter n*4]).
Definition PairExitWord n := PairWord (PairExitBody n) (2+Quarter n*4).

Lemma PairCertBody_visits N n : map (@length nat) (PairCertBody N n)=TM2.ExitBody n.
Proof.
  induction n; [reflexivity|].
  cbn[PairCertBody TM2.ExitBody]; rewrite map_app, IHn.
  cbn[map]; rewrite OddRow_length, EvenRow_length; reflexivity.
Qed.

Lemma PairRows_visits n : map (@length nat) (PairRows n)=(2+Quarter n*4)::PairExitBody n.
Proof.
  unfold PairRows, PairExitBody; cbn[map]; rewrite map_app, PairCertBody_visits.
  cbn[map length]; rewrite PairRoot_length, PairLast_length; reflexivity.
Qed.

Theorem Pair_canonical_endpoint n :
  Ticks (Alt true (2+n*2)) false (Quarter (1+n)*3) (repeat 0 (2+n*2)) 0
    (PairExitBody n) (2+Quarter n*4).
Proof.
  destruct (Pair_canonical_exit n) as [xs [u [HT [HE HL]]]].
  rewrite PairRows_visits in HE; injection HE as -> ->; exact HT.
Qed.

Theorem Pair_seed_exit n :
  Ticks (Alt true (16+n*2)) false (Quarter (8+n)*3-(9+n))
    (repeat 0 (16+n*2)) (9+n) (PairExitBody (7+n)) (2+Quarter (7+n)*4).
Proof.
  destruct (Pair_seed_absorption n) as [t [mid [root [Ht [HR [HP HL]]]]]].
  pose proof (Pair_canonical_endpoint (7+n)) as HC.
  replace (2+(7+n)*2) with (16+n*2) in HC by lia.
  destruct (PairBox_total (7+n)) as [bounds [h HB]].
  pose proof (PairBox_capacity HB) as EC; pose proof (PairBox_budget HB) as EB.
  pose proof (Quarter_power (8+n)) as EQ.
  change (4^(8+n)) with (4*4^(7+n)) in EQ; rewrite <- EC in EQ.
  assert (Ht' : t+(9+n)<=Quarter (8+n)*3) by nia.
  eapply Ticks_suffix with (k:=t+(9+n)) in HC; [|exact Ht'|exact HP].
  replace (Quarter (8+n)*3-(9+n)) with (t+(Quarter (8+n)*3-(t+(9+n)))) by lia.
  eapply Ticks_app; eassumption.
Qed.

Theorem RPrime_paired_exit n :
  Lives Edge retire (3+(Quarter (8+n)*3-(9+n))*2) (RPrimeWord (13+n*2)) [1]
    (PairExitWord (7+n)) [0;0].
Proof.
  eapply Lives_app.
  - pose proof (RPrime_entry (6+n)) as H; applys_eq H; flia.
  - unfold PairExitWord; apply (Pair_ticks_lives (7+n)); applys_eq (Pair_seed_exit n); flia.
Qed.

Import TM2 (Quarter_odd, PairNums, ExitBody_pairs).

Lemma CWord_pair_exit n : forall k u,
  CWord true (4^k*6) (1+Quarter k*2) (PairNums k n++[Quarter (k+n)*4]) u =
  Doubles (4^k*8) n++Alt false (4^(k+n)*8-1)++
    Alt false (4^(k+n)*12+Quarter (k+n)*4+u*2).
Proof.
  induction n; intros k u.
  - cbn[PairNums app CWord Doubles]; rewrite odd_1; cbn[xorb negb app].
    rewrite odd_four, Nat.add_0_r; cbn[xorb].
    pose proof (Quarter_power k); pose proof (Nat.pow_nonzero 4 k ltac:(lia)).
    f_equal; [f_equal; lia|f_equal; lia].
  - cbn[PairNums app CWord]; rewrite !odd_1, Quarter_odd; cbn[xorb negb].
    replace (4^k*6*2*2) with (4^(1+k)*6) by (cbn[Nat.add Nat.pow]; lia).
    replace (k+S n) with (1+k+n) by lia; rewrite IHn; cbn[Doubles].
    replace (4^k*8*4) with (4^(1+k)*8) by (cbn[Nat.add Nat.pow]; lia).
    pose proof (Quarter_power k) as E.
    replace (4^k*6+(1+Quarter k*2)+Quarter (1+k)) with (4^k*8)
      by (cbn[Nat.add Quarter]; lia).
    replace (4^k*6*2+Quarter (1+k)+(1+Quarter (1+k)*2)) with (4^k*8*2)
      by (cbn[Nat.add Quarter]; lia).
    rewrite !app_assoc; reflexivity.
Qed.

Lemma PairExitWord_shape n : PairExitWord n =
  Alt true 4++Doubles 8 n++Alt false (4^n*8-1)++Alt false (4^n*16).
Proof.
  unfold PairExitWord, PairExitBody, PairWord; rewrite ExitBody_pairs.
  change (Alt true 4++CWord true (4^0*6) (1+Quarter 0*2)
    (PairNums 0 n++[Quarter (0+n)*4]) (2+Quarter n*4)=
    Alt true 4++Doubles 8 n++Alt false (4^n*8-1)++Alt false (4^n*16)).
  rewrite CWord_pair_exit; cbn[Nat.pow Nat.add].
  pose proof (Quarter_power n); f_equal; f_equal; f_equal; f_equal; lia.
Qed.

Definition QInternal n := Alt true 2++Doubles 4 (1+n)++Alt false (4^n*16-2).
Definition QParent n := Doubles 2 (1+n)++Alt false (4^n*8-1)++Alt false (4^n*16).
Definition LWord n := Alt false 2++map negb (Doubles 4 (1+n))++Alt true (4^n*16+1).

Lemma PairExitWord_pass n : Pass (PairExitWord n) 0 (4^n*16-3)
  (Alt true 2++Doubles 4 (1+n)).
Proof.
  pose proof (Nat.pow_nonzero 4 n ltac:(lia)) as Hpos.
  rewrite PairExitWord_shape; replace (1+n) with (n+1) by lia; rewrite Doubles_snoc.
  replace (4*4^n) with (4^n*4) by lia; replace (4^n*4*2) with (4^n*8) by lia.
  eapply Pass_cat; [exact (@Pass_alt_even true 2 0 ltac:(auto))|].
  eapply Pass_cat with (b:=4^n*4-2).
  - applys_eq (@Pass_Doubles n 4 2 ltac:(lia) ltac:(lia) eq_refl eq_refl); flia.
  - eapply Pass_cat with (b:=4^n*8-3).
    + pose proof (@Pass_alt_odd_I (4^n*4-1) (4^n*4-2) ltac:(lia)) as H.
      assert (E : Nat.odd (4^n*4-2)=false).
      { replace (4^n*4-2) with ((4^n*2-1)*2) by lia; apply odd_0. }
      rewrite E in H; applys_eq H; flia.
    + pose proof (@Pass_alt_even false (4^n*8) (4^n*8-3) ltac:(left; lia)) as H.
      assert (E : Nat.odd (4^n*8-3)=true).
      { replace (4^n*8-3) with (1+(4^n*4-2)*2) by lia; apply odd_1. }
      rewrite E in H; applys_eq H; flia.
Qed.

Lemma Q_internal n : Life Edge retire (PairExitWord n) [0;0] (QInternal n) [0].
Proof.
  pose proof (Nat.pow_nonzero 4 n ltac:(lia)) as Hpos.
  pose proof (@Life_internal Edge retire _ 0 [0] _ _ ltac:(discriminate) (PairExitWord_pass n)) as HL.
  unfold retire in HL.
  replace (4^n*16-3) with (1+(4^n*8-2)*2) in HL by lia; rewrite odd_1 in HL; cbn[negb] in HL.
  unfold QInternal; rewrite <- !app_assoc in HL; applys_eq HL; flia.
Qed.

Lemma Q_parent n : Life Edge retire (QInternal n) [0] (QParent n) [1].
Proof.
  pose proof (Nat.pow_nonzero 4 n ltac:(lia)) as Hpos.
  assert (HP : Pass (Doubles 4 (1+n)++Alt false (4^n*16-2)) 2 (4^n*16-1)
    (Doubles 2 (1+n)++Alt false (4^n*8-1))).
  { eapply Pass_cat with (b:=4^n*8).
    - pose proof (@Pass_Doubles (1+n) 2 2 ltac:(lia) ltac:(lia) eq_refl eq_refl) as H.
      cbn[Nat.pow Nat.add] in H; applys_eq H; flia.
    - pose proof (@Pass_alt_even false (4^n*8-1) (4^n*8) ltac:(left; lia)) as H.
      replace (4^n*8) with ((4^n*4)*2) in H by lia.
      rewrite odd_0 in H; applys_eq H; flia. }
  pose proof (@Life_terminal Edge retire 1 _ 0 2 _ _ [1] (Edge_odd 0) HP) as HL.
  unfold retire in HL; replace (4^n*16-1) with (1+(4^n*8-1)*2) in HL by lia.
  rewrite odd_1 in HL; cbn[negb] in HL.
  unfold QInternal,QParent; rewrite <- !app_assoc in HL; applys_eq HL; flia.
Qed.

Lemma Q_terminal n : Life Edge retire (QParent n) [1] (LWord n) [1].
Proof.
  pose proof (Nat.pow_nonzero 4 n ltac:(lia)) as Hpos.
  assert (HP : Pass (true::(Alt true 4++Doubles 8 n++Alt false (4^n*8-1)++Alt false (4^n*16)))
    2 (4^n*16) (Alt false 2++map negb (Doubles 4 (1+n)))).
  { apply Pass_P.
    replace (1+n) with (n+1) by lia; rewrite Doubles_snoc, !map_app, !Alt_flip; cbn[negb].
    replace (4*4^n) with (4^n*4) by lia; replace (4^n*4*2) with (4^n*8) by lia.
    eapply Pass_cat; [exact (@Pass_alt_even true 2 3 ltac:(auto))|].
    eapply Pass_cat with (b:=4^n*4+1).
    - applys_eq (@Pass_Doubles_odd n 4 5 ltac:(lia) ltac:(lia) eq_refl eq_refl); flia.
    - eapply Pass_cat with (b:=4^n*8).
      + pose proof (@Pass_alt_odd_I (4^n*4-1) (4^n*4+1) ltac:(lia)) as H.
        assert (E : Nat.odd (4^n*4+1)=true).
        { replace (4^n*4+1) with (1+(4^n*2)*2) by lia; apply odd_1. }
        rewrite E in H; applys_eq H; flia.
      + pose proof (@Pass_alt_even false (4^n*8) (4^n*8) ltac:(left; lia)) as H.
        assert (E : Nat.odd (4^n*8)=false) by (rewrite Nat.odd_mul; apply andb_false_r).
        rewrite E in H; applys_eq H; flia. }
  pose proof (@Life_terminal Edge retire 0 _ 1 2 _ _ [1] (Edge_odd 0) HP) as HL.
  unfold retire in HL; replace (4^n*16) with ((4^n*8)*2) in HL by lia.
  rewrite odd_0 in HL; cbn[negb] in HL.
  unfold QParent,LWord; change (Doubles 2 (1+n)) with (Alt false 2++Alt true 4++Doubles 8 n).
  rewrite <- !app_assoc in HL |- *; cbn[repeat app] in HL.
  change (Life Edge retire (false::true::(Alt true 4++Doubles 8 n++
    Alt false (4^n*8-1)++Alt false (4^n*16))) [1]
    (Alt false 2++map negb (Doubles 4 (1+n))++Alt true (4^n*16+1)) [1]).
  applys_eq HL; flia.
Qed.

Theorem Q_to_L n : Lives Edge retire 3 (PairExitWord n) [0;0] (LWord n) [1].
Proof.
  eapply Lives_cons; [apply Q_internal|].
  eapply Lives_cons; [apply Q_parent|].
  econstructor; [apply Q_terminal|constructor].
Qed.

Fixpoint LNums k n := match n with
  | 0=>[Quarter (1+k)]
  | S n=>Quarter (1+k)::(Quarter (1+k)*2)::LNums (1+k) n end.

Lemma LNums_snoc n : forall k, LNums k (n+1)=LNums k n++
  [Quarter (1+k+n)*2;Quarter (2+k+n)].
Proof.
  induction n; intro k; cbn[Nat.add LNums]; [rewrite !Nat.add_0_r; reflexivity|].
  rewrite IHn; cbn[Nat.add app]; rewrite !Nat.add_succ_r; reflexivity.
Qed.

Lemma LNums_anchor n : FlatAnchor (1+n*2) (LNums 0 n) (Quarter (1+n)).
Proof.
  induction n; [exact FlatAnchor_base|].
  replace (S n) with (n+1) by lia; rewrite LNums_snoc.
  change (Quarter (1+0+n)) with (Quarter (1+n)).
  change (Quarter (2+0+n)) with (Quarter (2+n)).
  replace (1+(n+1)*2) with (1+(1+(1+n*2))) by lia.
  replace (Quarter (1+(n+1))) with (Quarter (2+n)) by (f_equal; lia).
  replace (Quarter (2+n)) with (1+(Quarter (1+n)*2)*2) by
    (change (1+(Quarter (1+n)*2)*2=1+Quarter (1+n)*4); lia).
  pose proof (FlatAnchor_odd (FlatAnchor_even IHn)) as H; rewrite <- app_assoc in H; exact H.
Qed.

Lemma LNums_mass n : forall k, total (LNums k n)+n+Quarter (1+k)=Quarter (1+k+n)*2.
Proof.
  induction n; intro k.
  - cbn[LNums total]; rewrite !Nat.add_0_r; lia.
  - cbn[LNums total]; specialize (IHn (1+k)).
    replace (1+k+S n) with (1+(1+k)+n) by lia.
    change (Quarter (1+(1+k))) with (1+Quarter (1+k)*4) in IHn; lia.
Qed.

Lemma FlatWord_LNums n : forall k x u, FlatWord x (LNums k n) u =
  Alt (Nat.odd x) (1+x+Quarter (1+k))++map negb (Doubles (4^(1+k)) n)++
  Alt true (2+Quarter (1+k+n)+u*2).
Proof.
  induction n; intros k x u; cbn[LNums FlatWord]; rewrite Quarter_odd.
  - cbn[Doubles map app]; rewrite Nat.add_0_r; reflexivity.
  - rewrite IHn, odd_0; cbn[Doubles]; rewrite !map_app, !Alt_flip; cbn[negb].
    pose proof (Quarter_power (1+k)) as E.
    replace (1+Quarter (1+k)+Quarter (1+k)*2) with (4^(1+k)) by lia.
    replace (1+Quarter (1+k)*2+Quarter (1+(1+k))) with (4^(1+k)*2)
      by (change (Quarter (1+(1+k))) with (1+Quarter (1+k)*4); lia).
    replace (4^(1+k)*4) with (4^(1+(1+k))) by (cbn[Nat.pow Nat.add]; lia).
    replace (1+k+S n) with (1+(1+k)+n) by lia.
    rewrite <- !app_assoc; reflexivity.
Qed.

Lemma LWord_flat n : LWord n=FlatWord 0 (LNums 0 (1+n)) (Quarter (2+n)).
Proof.
  rewrite FlatWord_LNums; unfold LWord.
  change (Alt false 2++map negb (Doubles 4 (1+n))++Alt true (4^n*16+1)=
    Alt false 2++map negb (Doubles 4 (1+n))++Alt true (2+Quarter (2+n)+Quarter (2+n)*2)).
  pose proof (Quarter_power (2+n)) as E; change (Quarter (2+n)*3+1=4*(4*4^n)) in E.
  f_equal; f_equal; f_equal; lia.
Qed.

Lemma LNums_prefix n : FlatSteps (3+n*2) (4^n*16-3-n) (0::repeat 0 (3+n*2))
  (Quarter (2+n)::LNums 0 (1+n)).
Proof.
  pose proof (FlatAnchor_reachable (LNums_anchor (1+n))) as H.
  pose proof (LNums_mass (1+n) 0) as EM.
  pose proof (Quarter_power (2+n)) as EQ.
  change (total (LNums 0 (1+n))+(1+n)+1=Quarter (2+n)*2) in EM.
  change (Quarter (2+n)*3+1=4*(4*4^n)) in EQ.
  replace (1+(1+n)*2) with (3+n*2) in H by lia.
  change (Quarter (1+(1+n))) with (Quarter (2+n)) in H.
  replace (Quarter (2+n)+total (LNums 0 (1+n))) with (4^n*16-3-n) in H by lia.
  exact H.
Qed.

Lemma LNums_exit n : FlatSteps (3+n*2) (4^n*8+1+n)
  (Quarter (2+n)::LNums 0 (1+n)) (2^(3+n*2)::PowBody 1 (3+n*2)).
Proof.
  pose proof (@Flat_zero_exit (3+n*2) ltac:(lia)) as H; rewrite FlatExitRows_values in H.
  eapply FlatSteps_cancel; [apply LNums_prefix|exact H|].
  pose proof (LNums_mass (1+n) 0) as EM; pose proof (Quarter_power (2+n)) as EQ.
  assert (EP : 2^(3+n*2)=4^n*8).
  { rewrite Nat.pow_add_r, <- power4; cbn; lia. }
  rewrite EP; cbn[Nat.add Nat.pow Quarter] in EM, EQ; lia.
Qed.

Theorem LWord_exit n : Lives Edge retire (4^n*8+1+n) (LWord n) [1]
  (Alt false 3++RTail (1+n*2)) [1].
Proof.
  pose proof (FlatSteps_lives (LNums_exit n)) as H.
  cbn[hd tl] in H; rewrite <- LWord_flat in H.
  replace (3+n*2) with (2+(1+n*2)) in H by lia; rewrite FlatExit_word in H; exact H.
Qed.

Theorem QWord_round n : Lives Edge retire (4^n*32+4+n)
  (PairExitWord n) [0;0] (RWord (2+n*2)) [1].
Proof.
  pose proof (First_ordinary_round (1+n*2)) as H.
  assert (EP : 2^(2+(1+n*2))=4^n*8).
  { replace (2+(1+n*2)) with (3+n*2) by lia; rewrite Nat.pow_add_r, <- power4; cbn; lia. }
  rewrite EP in H.
  replace (4^n*32+4+n) with (3+((4^n*8+1+n)+(4^n*8*3))) by lia.
  eapply Lives_app; [apply Q_to_L|].
  eapply Lives_app; [apply LWord_exit|exact H].
Qed.

Definition RoundWord (prime:bool) n := if prime then RPrimeWord (13+n*2) else RWord (12+n*2).

Lemma RoundWord_progress prime n : exists t prime' n',
  Lives Edge retire (1+t) (RoundWord prime n) [1] (RoundWord prime' n') [1].
Proof.
  destruct prime; unfold RoundWord.
  - pose proof (Lives_app (RPrime_paired_exit n) (QWord_round (7+n))) as H.
    exists (2+(Quarter (8+n)*3-(9+n))*2+(4^(7+n)*32+4+(7+n))),false,(2+n).
    applys_eq H; flia.
  - destruct (RWord_round (2+n)) as [H|H].
    + exists (4^(5+(2+n))*9+1),false,(1+n); applys_eq H; flia.
    + exists (4^(5+(2+n))*9),true,n; applys_eq H; flia.
Qed.

Lemma RoundWord_suffix_infinite : forall prime n t w xs,
  Lives Edge retire t w xs (RoundWord prime n) [1] -> InfiniteLife Edge retire w xs.
Proof.
  cofix IH; intros prime n t w xs H; destruct t.
  - inversion H; subst. destruct (RoundWord_progress prime n) as [t [p [k HT]]].
    inversion HT; subst; econstructor; [eassumption|eapply (IH p k t); eassumption].
  - inversion H; subst; econstructor; [eassumption|eapply (IH prime n t); eassumption].
Qed.

Theorem RWord_infinite n : InfiniteLife Edge retire (RWord (12+n*2)) [1].
Proof. eapply (@RoundWord_suffix_infinite false n 0); constructor. Qed.

Lemma flat_to_R2 : Lives Edge retire 7 (FlatWord 0 [1] 2) [1] (RWord 0) [1].
Proof.
  do 2 (eapply Lives_cons;
    [eapply Life_terminal with (k:=0) (b:=2); [exact (Edge_odd 0)|
      repeat first [apply Pass_nil | apply Pass_P | apply Pass_I; [lia|]]]|]).
  do 5 (eapply Lives_cons;
    [eapply Life_terminal with (k:=2) (b:=4); [exact (Edge_odd 1)|
      repeat first [apply Pass_nil | apply Pass_P | apply Pass_I; [lia|]]]|]).
  constructor.
Qed.

Lemma initial_R2 : Lives Edge retire 11 [] [4;0;0] (RWord 0) [1].
Proof. exact (Lives_app initial_flat flat_to_R2). Qed.

Definition small_first_check (c:nat*bool) := let '(n,early):=c in
  FlatEval.check (3+n*2) (4^(1+n)*3-(if early then 2 else 1))
    (tl (RSeed n)) (hd 0 (RSeed n))
    (if early then 2::3::PowBody 3 (1+n*2) else PowBody 1 (3+n*2)) (2^(3+n*2)).

Lemma small_first_checked : forallb small_first_check [(0,false);(1,false);(2,true);(4,true)]=true.
Proof. vm_compute; reflexivity. Qed.

Definition small_pair_check n := CounterEval.check (Alt true (2+n*2)) false
  (Quarter (1+n)*3-(2+n)) (repeat 0 (2+n*2)) (2+n)
  (PairExitBody n) (2+Quarter n*4).

Lemma small_pair_checked : forallb small_pair_check [3;5]=true.
Proof. vm_compute; reflexivity. Qed.

Lemma small_first_steps n early : In (n,early) [(0,false);(1,false);(2,true);(4,true)] ->
  FlatSteps (3+n*2) (4^(1+n)*3-(if early then 2 else 1)) (RSeed n)
    (2^(3+n*2)::(if early then 2::3::PowBody 3 (1+n*2) else PowBody 1 (3+n*2))).
Proof.
  intro H; pose proof (proj1 (forallb_forall _ _) small_first_checked (n,early) H) as HC.
  apply FlatEval.check_spec in HC; exact HC.
Qed.

Lemma small_RWord_round n early : In (n,early) [(0,false);(1,false);(2,true);(4,true)] ->
  Lives Edge retire (3+(4^(1+n)*3-(if early then 2 else 1))+2^(3+n*2)*3)
    (RWord (n*2)) [1] (if early then RPrimeWord (1+n*2) else RWord (2+n*2)) [1].
Proof.
  intro H; pose proof (FlatSteps_lives (small_first_steps H)) as HL; cbn[hd tl] in HL.
  destruct early.
  - rewrite FlatEarly_word in HL.
    eapply Lives_app; [eapply Lives_app; [apply RWord_flat_entry|exact HL]|apply First_early_round].
  - replace (3+n*2) with (2+(1+n*2)) in HL by lia; rewrite FlatExit_word in HL.
    eapply Lives_app; [eapply Lives_app; [apply RWord_flat_entry|exact HL]|].
    applys_eq (First_ordinary_round (1+n*2)); flia.
Qed.

Lemma small_pair_ticks n : In n [3;5] ->
  Ticks (Alt true (2+n*2)) false (Quarter (1+n)*3-(2+n))
    (repeat 0 (2+n*2)) (2+n) (PairExitBody n) (2+Quarter n*4).
Proof.
  intro H; apply CounterEval.check_spec.
  exact (proj1 (forallb_forall _ _) small_pair_checked n H).
Qed.

Lemma small_RPrime_round n : In (1+n) [3;5] ->
  Lives Edge retire (3+(Quarter (2+n)*3-(3+n))*2+(4^(1+n)*32+4+(1+n)))
    (RPrimeWord (1+n*2)) [1] (RWord (4+n*2)) [1].
Proof.
  intro H; pose proof (Pair_ticks_lives (1+n) (small_pair_ticks H)) as HL.
  eapply Lives_app; [eapply Lives_app; [apply RPrime_entry|]|].
  - unfold PairExitWord; applys_eq HL; flia.
  - applys_eq (QWord_round (1+n)); flia.
Qed.

Lemma R2_to_R14 : Lives Edge retire 53492 (RWord 0) [1] (RWord 12) [1].
Proof.
  exact (Lives_app (@small_RWord_round 0 false ltac:(cbn; auto))
    (Lives_app (@small_RWord_round 1 false ltac:(cbn; auto))
    (Lives_app (@small_RWord_round 2 true ltac:(cbn; auto))
    (Lives_app (@small_RPrime_round 2 ltac:(cbn; auto))
    (Lives_app (@small_RWord_round 4 true ltac:(cbn; auto))
               (@small_RPrime_round 4 ltac:(cbn; auto))))))).
Qed.

Lemma initial_R14 : Lives Edge retire 53503 [] [4;0;0] (RWord 12) [1].
Proof. exact (Lives_app initial_R2 R2_to_R14). Qed.

Lemma flat_infinite : InfiniteLife Edge retire (FlatWord 0 [1] 2) [1].
Proof.
  eapply Lives_infinite; [exact (Lives_app flat_to_R2 R2_to_R14)|exact (RWord_infinite 0)].
Qed.

Lemma initial_infinite : InfiniteLife Edge retire [] [4;0;0].
Proof. eapply Lives_infinite; [apply initial_R14|exact (RWord_infinite 0)]. Qed.

Theorem nonhalt : ~halts tm c0.
Proof. apply nonhalt_from_lives, initial_infinite. Qed.

End TM3.

Module TM6.
Definition tm := Eval compute in (TM_from_str "1RB---_0LC1RF_0LD1LC_1RE1LB_0RE1LA_0RB0RA").
Notation "c -->* c'" := (c -[tm]->* c') (at level 40).
Notation "c -->+ c'" := (c -[tm]->+ c') (at level 40).
Open Scope sym.

Fixpoint LC (xs:list nat) :=
  match xs with [] => 0inf | a::xs => LC xs <* <[1;0]^^a <* <[1] end.
Definition S1 xs n := LC xs {{B}}> [1;0]^^n *> 0inf.
Definition QL (p:bool) := if p then B else C.

Import TM3 (Edge, Edge_even, Edge_odd, Edge_size, Edge_functional).
Notation LInc := (Flow_LInc Edge).
Notation Run := (Flow_Run Edge).
Definition retire a := Nat.odd a::Alt (Nat.odd a) a.

Lemma LInc_spec p xs ys : LInc p xs ys ->
  forall r, LC xs <{{QL p}} [1;0] *> r -->* LC ys {{B}}> r.
Proof.
  intro H; induction H; intros r.
  - cbn[LC QL]; es.
  - destruct (mod2 a) as [k E|k E]; subst a.
    + rewrite odd_0 in IHLInc. destruct k as [|k]; [lia|].
      replace (S k*2) with (2+k*2) by lia.
      cbn[LC QL] in *; es; er; follow IHLInc; es.
    + rewrite odd_1 in IHLInc. cbn[LC QL] in *; es; er; follow IHLInc; es.
  - destruct H; cbn[LC QL]; es.
Qed.

Lemma Inc_right n xs ys : LInc (negb (Nat.odd n)) xs ys ->
  S1 xs (1+n) -->* S1 ys n.
Proof.
  intro H; destruct (mod2 n) as [a E|a E]; subst n.
  - rewrite odd_0 in H. eapply LInc_spec in H. es; er; follow H; finish.
  - rewrite odd_1 in H. eapply LInc_spec in H. es; er; follow H; finish.
Qed.

Lemma Inc_zero a xs ys : LInc (Nat.odd a) xs ys ->
  S1 (a::xs) 0 -->+ S1 ys a.
Proof.
  intro H; destruct (mod2 a) as [k E|k E]; subst a.
  - rewrite odd_0 in H. eapply LInc_spec in H. unfold S1; cbn[LC].
    es; er; follow H; finish.
  - rewrite odd_1 in H. eapply LInc_spec in H. unfold S1; cbn[LC].
    es; er; follow H; finish.
Qed.

Lemma Run_right n xs ys : Run (Alt (Nat.odd n) n) xs ys -> S1 xs n -->* S1 ys 0.
Proof.
  revert xs; induction n; intros xs H.
  - inversion H; subst; apply evstep_refl.
  - cbn[Alt] in H; rewrite odd_S, negb_involutive in H.
    inversion H as [|p w source cut target HL HR]; subst.
    follow (Inc_right n HL); apply IHn; assumption.
Qed.

Lemma Macro_spec xs ys : Flow_Macro Edge retire xs ys -> S1 xs 0 -->+ S1 ys 0.
Proof.
  intro H; destruct H; cbn[retire] in H.
  inversion H as [|p w source cut target HL HR]; subst.
  follow10 (Inc_zero a HL); apply Run_right; assumption.
Qed.

Lemma init : c0 -->* S1 [2;1]%nat 2.
Proof. unfold S1; esx. Qed.

Lemma first_cut : c0 -->* S1 [3;2;1]%nat 0.
Proof.
  follow init. follow (@Inc_right 1 [2;1]%nat [2;2;1]%nat
    ltac:(apply LInc_I; [lia|apply LInc_edge, (Edge_odd 0)])).
  apply Inc_right, LInc_P.
Qed.

Lemma InfiniteMacro_nonhalt xs :
  Flow_InfiniteMacro Edge retire xs -> ~halts tm (S1 xs 0).
Proof.
  intro HI. eapply progress_nonhalt with
    (P:=fun c => exists ys, Flow_InfiniteMacro Edge retire ys /\ c=S1 ys 0).
  - intros c [ys [H ->]]. destruct H as [ys zs HM HI'].
    exists (S1 zs 0); split; [exists zs; auto|apply Macro_spec; assumption].
  - exists xs; auto.
Qed.

Lemma nonhalt_from_lives :
  Flow_InfiniteLife Edge retire [] [3;2;1]%nat -> ~halts tm c0.
Proof.
  intro H; eapply multistep_nonhalt; [apply first_cut|].
  apply InfiniteMacro_nonhalt. eapply InfiniteLife_sound;
    eauto using Edge_size, Edge_functional, Run_nil.
Qed.

Close Scope sym.

Inductive Trim : list bool -> list bool -> Prop :=
| Trim_make w : Trim (w++[false;true;false;true]) (w++[false;true]).

Lemma Trim_app p w v : Trim w v -> Trim (p++w) (p++v).
Proof. intro H; destruct H; rewrite !app_assoc; constructor. Qed.

Lemma Alt_own_tail k : Alt (Nat.odd k) (k+2)=Alt (Nat.odd k) k++[false;true].
Proof.
  replace (k+2) with ((k+1)+1) by lia; rewrite !Alt_snoc.
  rewrite Nat.add_1_r, odd_S; destruct (Nat.odd k); cbn; rewrite <- app_assoc; reflexivity.
Qed.

Lemma retire_trim c : 2<=c -> Trim ([Nat.odd c]++TM3.retire (1+c)) (retire c).
Proof.
  intro HC; destruct c as [|[|k]]; try lia.
  unfold TM3.retire, retire; rewrite !odd_S, !negb_involutive.
  replace (1+(1+S (S k))) with ((k+2)+2) by lia.
  replace (S (S k)) with (k+2) by lia.
  change (Trim ([Nat.odd k]++Alt (Nat.odd k) ((k+2)+2))
    ([Nat.odd k]++Alt (Nat.odd k) (k+2))).
  assert (EO : Nat.odd (k+2)=Nat.odd k).
  { replace (k+2) with (S (S k)) by lia; rewrite !odd_S, negb_involutive; reflexivity. }
  pose proof (Alt_own_tail (k+2)) as H; rewrite EO in H.
  rewrite H, !Alt_own_tail.
  rewrite <- !app_assoc; apply Trim_app, Trim_make.
Qed.

Lemma Pass_trim4 w a b o : Pass (w++[false;true;false;true]) a b o -> exists c p,
  2<=c /\ b=1+c /\ Pass (w++[false;true]) a c p /\ o=p++[Nat.odd c].
Proof.
  intro H; destruct (Pass_app w [false;true;false;true] H) as [x [p [q [HP [HT ->]]]]].
  repeat match goal with
  | H : Pass (_::_) _ _ _ |- _ => inversion H; subst; clear H
  | H : Pass [] _ _ _ |- _ => inversion H; subst; clear H end.
  exists (1+x),(p++[Nat.odd x]); repeat split; try lia.
  - eapply Pass_cat; [exact HP|apply Pass_I; [assumption|apply Pass_P, Pass_nil]].
  - rewrite <- app_assoc; reflexivity.
Qed.
Arguments Pass_trim4 {w a b o} _.

Lemma terminal_unique k : forall j u v,
  repeat true k++false::u=repeat true j++false::v -> k=j /\ u=v.
Proof.
  induction k; intros [|j] u v H; cbn in H; try discriminate.
  - inversion H; auto.
  - injection H as H; destruct (IHk _ _ _ H); subst; auto.
Qed.

Section PositiveBirth.
Variable E : nat -> nat -> list nat -> Prop.
Hypothesis E_positive : forall a b kids, E a b kids -> b<>0.

Lemma Life_trim4 w xs z zs : Life E TM3.retire (w++[false;true;false;true]) xs z zs ->
  exists v, Life E retire (w++[false;true]) xs v zs /\ Trim z v.
Proof.
  remember (w++[false;true;false;true]) as input eqn:EI.
  intro H; destruct H as [input a xs b o Hne HP|k u a b c o kids HE HP].
  - subst input; destruct (Pass_trim4 HP) as [c [p [HC [-> [HT ->]]]]].
    exists (p++retire c); split; [apply Life_internal; assumption|].
    rewrite <- app_assoc; apply Trim_app, retire_trim; assumption.
  - destruct (terminal_prefix k u w [false;true;false;true] EI)
      as [[j ->]|[v [tail [HU HW]]]].
    + destruct (terminal_unique k j u [true;false;true] EI) as [-> ->].
      assert (HB : b<>0) by (eapply E_positive; exact HE).
      repeat match goal with
      | H : Pass (_::_) _ _ _ |- _ => inversion H; subst; clear H
      | H : Pass [] _ _ _ |- _ => inversion H; subst; clear H end.
      exists (retire (1+b)); split.
      * eapply Life_terminal with (k:=j) (b:=b) (c:=1+b) (o:=[]);
          [exact HE|apply Pass_P, Pass_nil].
      * apply retire_trim; lia.
    + assert (ET : tail=[false;true;false;true]).
      { rewrite HU, HW in EI; rewrite <- app_assoc in EI; apply app_inv_head in EI.
        cbn in EI; injection EI as EI; exact (app_inv_head v tail _ EI). }
      subst tail u w; destruct (Pass_trim4 HP) as [d [p [HD [-> [HT ->]]]]].
      exists (p++retire d); split.
      * rewrite <- app_assoc; cbn[app]; eapply Life_terminal; eassumption.
      * rewrite <- app_assoc; apply Trim_app, retire_trim; assumption.
Qed.
Arguments Life_trim4 {w xs z zs} _.

Lemma InfiniteLife_trim : forall w xs, InfiniteLife E TM3.retire w xs ->
  forall v, Trim w v -> InfiniteLife E retire v xs.
Proof.
  cofix IH; intros w xs H v HT; destruct H as [w xs z zs HL HI']; destruct HT.
  destruct (Life_trim4 HL) as [v [HV HT]].
  econstructor; [exact HV|eapply IH; eassumption].
Qed.

End PositiveBirth.

Lemma initial_flow : Lives Edge retire 2 [] [3;2;1] (Alt false 2++Alt true 5) [1].
Proof.
  do 2 (eapply Lives_cons;
    [eapply Life_internal; [discriminate|
      repeat first [apply Pass_nil | apply Pass_P | apply Pass_I; [lia|]]]|]).
  constructor.
Qed.

Lemma initial_infinite : InfiniteLife Edge retire [] [3;2;1].
Proof.
  eapply Lives_infinite; [apply initial_flow|].
  eapply InfiniteLife_trim; [intros; match goal with H : Edge _ _ _ |- _ => destruct H; lia end|exact TM3.flat_infinite|].
  exact (Trim_make [false;true;true;false;true]).
Qed.

Theorem nonhalt : ~halts tm c0.
Proof. apply nonhalt_from_lives, initial_infinite. Qed.

End TM6.

Module TM7.
Definition tm := Eval compute in (TM_from_str "1RB---_0LC1RF_0LD1LC_1RE1LB_1RD0LD_0RB0RA").
Notation "c -->* c'" := (c -[tm]->* c') (at level 40).
Notation "c -->+ c'" := (c -[tm]->+ c') (at level 40).
Open Scope sym.

Fixpoint LC (xs:list nat) :=
  match xs with [] => 0inf | a::xs => LC xs <* <[1;0]^^a <* <[1] end.
Definition S1 xs n := LC xs {{B}}> [1;0]^^n *> 0inf.
Definition QL (p:bool) := if p then B else C.

Inductive Edge : nat -> nat -> list nat -> Prop :=
| Edge_even a : Edge (2+a*2) (2+a*2) [1;0]%nat
| Edge_odd a : Edge (1+a*2) (2+a*2) [1]%nat.

Lemma Edge_size a b kids : Edge a b kids -> length kids<=2.
Proof. intro H; destruct H; cbn; lia. Qed.

Lemma Edge_functional a b kids c kids' :
  Edge a b kids -> Edge a c kids' -> b=c /\ kids=kids'.
Proof. intros H H'; destruct H; inversion H'; subst; split; try reflexivity; f_equal; lia. Qed.

Lemma Edge_positive a b kids : Edge a b kids -> b<>0%nat.
Proof. intro H; destruct H; lia. Qed.
Notation LInc := (Flow_LInc Edge).
Notation Run := (Flow_Run Edge).
Definition retire := TM6.retire.

Lemma LInc_spec p xs ys : LInc p xs ys ->
  forall r, LC xs <{{QL p}} [1;0] *> r -->* LC ys {{B}}> r.
Proof.
  intro H; induction H; intros r.
  - cbn[LC QL]; es.
  - destruct (mod2 a) as [k E|k E]; subst a.
    + rewrite odd_0 in IHLInc. destruct k as [|k]; [lia|].
      replace (S k*2) with (2+k*2) by lia.
      cbn[LC QL] in *; es; er; follow IHLInc; es.
    + rewrite odd_1 in IHLInc. cbn[LC QL] in *; es; er; follow IHLInc; es.
  - destruct H; cbn[LC QL]; es.
Qed.

Lemma Inc_right n xs ys : LInc (negb (Nat.odd n)) xs ys ->
  S1 xs (1+n) -->* S1 ys n.
Proof.
  intro H; destruct (mod2 n) as [a E|a E]; subst n.
  - rewrite odd_0 in H. eapply LInc_spec in H. es; er; follow H; finish.
  - rewrite odd_1 in H. eapply LInc_spec in H. es; er; follow H; finish.
Qed.

Lemma Inc_zero a xs ys : LInc (Nat.odd a) xs ys ->
  S1 (a::xs) 0 -->+ S1 ys a.
Proof.
  intro H; destruct (mod2 a) as [k E|k E]; subst a.
  - rewrite odd_0 in H. eapply LInc_spec in H. unfold S1; cbn[LC].
    es; er; follow H; finish.
  - rewrite odd_1 in H. eapply LInc_spec in H. unfold S1; cbn[LC].
    es; er; follow H; finish.
Qed.

Lemma Run_right n xs ys : Run (Alt (Nat.odd n) n) xs ys -> S1 xs n -->* S1 ys 0.
Proof.
  revert xs; induction n; intros xs H.
  - inversion H; subst; apply evstep_refl.
  - cbn[Alt] in H; rewrite odd_S, negb_involutive in H.
    inversion H as [|p w source cut target HL HR]; subst.
    follow (Inc_right n HL); apply IHn; assumption.
Qed.

Lemma Macro_spec xs ys : Flow_Macro Edge retire xs ys -> S1 xs 0 -->+ S1 ys 0.
Proof.
  intro H; destruct H; cbn[retire] in H.
  inversion H as [|p w source cut target HL HR]; subst.
  follow10 (Inc_zero a HL); apply Run_right; assumption.
Qed.

Lemma init : c0 -->* S1 [2;1]%nat 2.
Proof. unfold S1; esx. Qed.

Lemma first_cut : c0 -->* S1 [3;2;1]%nat 0.
Proof.
  follow init. follow (@Inc_right 1 [2;1]%nat [2;2;1]%nat
    ltac:(apply LInc_I; [lia|apply LInc_edge, (Edge_odd 0)])).
  apply Inc_right, LInc_P.
Qed.

Lemma InfiniteMacro_nonhalt xs :
  Flow_InfiniteMacro Edge retire xs -> ~halts tm (S1 xs 0).
Proof.
  intro HI. eapply progress_nonhalt with
    (P:=fun c => exists ys, Flow_InfiniteMacro Edge retire ys /\ c=S1 ys 0).
  - intros c [ys [H ->]]. destruct H as [ys zs HM HI'].
    exists (S1 zs 0); split; [exists zs; auto|apply Macro_spec; assumption].
  - exists xs; auto.
Qed.

Lemma nonhalt_from_lives :
  Flow_InfiniteLife Edge retire [] [3;2;1]%nat -> ~halts tm c0.
Proof.
  intro H; eapply multistep_nonhalt; [apply first_cut|].
  apply InfiniteMacro_nonhalt. eapply InfiniteLife_sound;
    eauto using Edge_size, Edge_functional, Run_nil.
Qed.

Close Scope sym.


Notation NLife := (Life Edge TM3.retire).
Notation NLives := (Lives Edge TM3.retire).

Lemma odd_life w v : Life TM3.Edge TM3.retire w [1] v [1] -> NLife w [1] v [1].
Proof.
  intro H; inversion H as [u a xs b o Hne HP|k u a b c o kids HE HP]; subst.
  inversion HE; subst; eapply Life_terminal; [apply Edge_odd|exact HP].
Qed.

Lemma FlatSteps_lives N n xs ys : FlatSteps N n xs ys ->
  NLives n (FlatWord 0 (tl xs) (hd 0 xs)) [1] (FlatWord 0 (tl ys) (hd 0 ys)) [1].
Proof.
  intro H; induction H; [constructor|].
  destruct H0; cbn[tl hd] in *; replace (1+n) with (n+1) by lia.
  eapply Lives_app; [exact IHFlatSteps|].
  econstructor; [apply odd_life; eapply TM3.FlatWord_life; eassumption|constructor].
Qed.

Lemma SecondSteps_lives N n xs ys : FlatSteps N n xs ys ->
  NLives n (TM3.SecondWord N xs) [1] (TM3.SecondWord N ys) [1].
Proof.
  intro H; induction H; [constructor|].
  destruct H0; unfold TM3.SecondWord in *; cbn[hd tl] in *.
  replace (1+n) with (n+1) by lia; eapply Lives_app; [exact IHFlatSteps|].
  econstructor; [apply odd_life; eapply TM3.FlatWord_P_life; exact (Half_raise H0)|constructor].
Qed.

Theorem First_ordinary_round n : NLives (2^(2+n)*3)
  (Alt false 3++TM3.RTail n) [1] (TM3.RWord (1+n)) [1].
Proof.
  pose proof (@Flat_zero_exit (2+n) ltac:(lia)) as HF.
  rewrite TM3.FlatExitRows_values in HF.
  pose proof (SecondSteps_lives HF) as HS; rewrite TM3.SecondWord_exit in HS.
  replace (2^(2+n)*3) with (1+((2^(2+n)*3-2)+1)) by
    (pose proof (Nat.pow_nonzero 2 n ltac:(lia)); cbn[Nat.add Nat.pow]; lia).
  eapply Lives_cons; [apply odd_life, TM3.First_exit_boundary|].
  eapply Lives_app; [exact HS|].
  econstructor; [apply odd_life, TM3.Second_exit_boundary|constructor].
Qed.

Theorem First_early_entry n : NLives 3 (TM3.FlatEarlyWord n) [1]
  (TM3.SecondWord (3+n) (0::(repeat 0 (2+n)++[1]))) [1].
Proof.
  rewrite <- TM3.FlatEarly_word.
  eapply Lives_cons; [apply odd_life; apply TM3.FlatWord_I_overflow with (N:=3+n); apply TM3.Early_first_half|].
  eapply Lives_cons; [apply odd_life; apply TM3.FlatWord_P_reset with (N:=3+n); apply TM3.Early_second_half|].
  unfold TM3.SecondWord; cbn[hd tl]; rewrite Nat.add_0_l.
  replace (2+n) with (3+n-1) by lia.
  econstructor; [apply odd_life; apply TM3.FlatWord_I_overflow with (N:=3+n), TM3.Early_third_half; lia|constructor].
Qed.

Theorem First_early_round n : NLives (2^(3+n)*3)
  (TM3.FlatEarlyWord n) [1] (TM3.RPrimeWord (1+n)) [1].
Proof.
  set (N:=3+n); set (T:=2^N*3-4).
  assert (ET : 2^N*3-2=2+T) by
    (unfold T, N; pose proof (Nat.pow_nonzero 2 n ltac:(lia)); cbn[Nat.pow Nat.add]; lia).
  pose proof (@Flat_zero_exit N ltac:(unfold N; lia)) as HF.
  rewrite TM3.FlatExitRows_values, ET in HF.
  change (FlatSteps N (2+T) (0::repeat 0 N) (2^N::2::4::TM3.PowBody 3 (1+n))) in HF.
  assert (HS : FlatStep N (0::repeat 0 N) (1::repeat 0 N)) by (apply FlatStep_zero; unfold N; lia).
  pose proof (@FlatEarly_zero (2+n)) as HE.
  change (FlatEarly N (0::repeat 0 N) (1::repeat 0 N) (0::(repeat 0 (2+n)++[1]))) in HE.
  pose proof (FlatEarly_final_run (N:=N) ltac:(unfold N; lia) HS
    (Bump_here 0 (repeat 0 N)) ltac:(left; reflexivity) HE HF) as HA.
  pose proof (SecondSteps_lives HA) as HL; unfold N in HL; rewrite TM3.SecondWord_early in HL.
  replace (2^N*3) with (3+(T+1)) by
    (unfold T, N; pose proof (Nat.pow_nonzero 2 n ltac:(lia)); cbn[Nat.pow Nat.add]; lia).
  eapply Lives_app; [apply First_early_entry|].
  eapply Lives_app; [exact HL|].
  econstructor; [apply odd_life, TM3.Second_early_boundary|constructor].
Qed.

Definition Parent0 k := Alt false 4++Ladder true 6 (2+k).
Definition Parent1 k := Alt false 3++Alt false 6++Ladder true 12 (2+k).

Lemma RWord_parent k : NLife (TM3.RWord k) [1] (Parent0 k) [1;0].
Proof.
  pose proof (@TM3.Pass_ladder_tail_low k 6 ltac:(lia) eq_refl) as H.
  change (Pass (Ladder false 12 k++Alt false (2+12*2^k)) 5 (12*2^k)
    (Ladder true 6 (1+k))) in H.
  assert (HP : Pass (TM3.RTail k) 2 (12*2^k) (Alt false 4++Ladder true 6 (1+k))).
  { unfold TM3.RTail; cbn[Nat.add Ladder]; rewrite <- app_assoc; eapply Pass_cat;
      [exact (@Pass_alt_odd_I 3 2 ltac:(lia))|exact H]. }
  pose proof (@Life_terminal Edge TM3.retire 1 _ 1 2 _ _ [1;0] (Edge_even 0) HP) as HL.
  unfold TM3.retire in HL; replace (12*2^k) with ((6*2^k)*2) in HL by lia.
  rewrite odd_0 in HL; cbn[negb] in HL.
  unfold Parent0; replace (2+k) with ((1+k)+1) by lia; rewrite TM3.Ladder_snoc.
  change (NLife (TM3.RWord k) [1]
    (Alt false 4++(Ladder true 6 (1+k)++Alt true (1+6*2^(1+k)))) [1;0]).
  replace (6*2^(1+k)) with ((6*2^k)*2) by (cbn[Nat.add Nat.pow]; lia).
  rewrite !app_assoc; exact HL.
Qed.

Lemma RPrime_parent k : NLife (TM3.RPrimeWord k) [1] (Parent1 k) [1;0].
Proof.
  pose proof (@TM3.Pass_ladder_tail_low k 12 ltac:(lia) eq_refl) as H.
  change (Pass (Ladder false 24 k++Alt false (2+24*2^k)) 11 (24*2^k)
    (Ladder true 12 (1+k))) in H.
  assert (HP : Pass (Alt false 6++Alt true 12++Ladder false 24 k++Alt false (2+24*2^k))
    2 (24*2^k) (Alt false 3++Alt false 6++Ladder true 12 (1+k))).
  { eapply Pass_cat; [exact (@Pass_alt_even false 3 2 ltac:(left; lia))|].
    eapply Pass_cat; [exact (@Pass_alt_even true 6 5 ltac:(right; reflexivity))|exact H]. }
  pose proof (@Life_terminal Edge TM3.retire 1 _ 1 2 _ _ [1;0] (Edge_even 0) HP) as HL.
  unfold TM3.retire in HL; replace (24*2^k) with ((12*2^k)*2) in HL by lia.
  rewrite odd_0 in HL; cbn[negb] in HL.
  unfold Parent1; replace (2+k) with ((1+k)+1) by lia; rewrite TM3.Ladder_snoc.
  replace (12*2^(1+k)) with ((12*2^k)*2) by (cbn[Nat.add Nat.pow]; lia).
  replace ((12*2^k)*2) with (24*2^k) in HL |- * by lia.
  rewrite <- !app_assoc in HL; exact HL.
Qed.

Definition MidWord n q := Alt true 2++Alt false 3++Doubles 6 (1+n)++
  Alt false (24*4^n)++Alt true (3+q*2+n*2+48*4^n).

Lemma Pass_parent_tail n q : Pass (Ladder true 12 (3+n*2)) (5+q*2)
  (2+q*2+n*2+48*4^n) (Doubles 6 (1+n)++Alt false (24*4^n)).
Proof.
  pose proof (@TM3.Pass_ladder_P_pairs (1+n) 6 (5+q*2) eq_refl
    ltac:(replace (5+q*2) with (1+(2+q)*2) by lia; apply odd_1)) as H.
  replace (3+n*2) with ((1+n)*2+1) by lia; rewrite TM3.Ladder_snoc.
  rewrite TM3.power4.
  assert (EO : Nat.odd (5+q*2+(1+n)*2+6*(4^(1+n)-1))=true).
  { replace (5+q*2+(1+n)*2+6*(4^(1+n)-1)) with
      (1+(2+q+(1+n)+3*(4^(1+n)-1))*2) by lia; apply odd_1. }
  pose proof (@Pass_alt_odd_P (6*4^(1+n)) (5+q*2+(1+n)*2+6*(4^(1+n)-1))) as HT.
  rewrite EO in HT; cbn[negb] in HT.
  pose proof (Nat.pow_nonzero 4 n ltac:(lia)).
  applys_eq (Pass_cat H HT); cbn[Nat.add Nat.pow]; flia.
Qed.

Lemma Parent0_internal n : NLife (Parent0 (2+n*2)) [1;0] (MidWord n 1) [0].
Proof.
  pose proof (Pass_parent_tail n 1) as H.
  assert (HP : Pass (Parent0 (2+n*2)) 1 (4+n*2+48*4^n)
    (Alt true 2++Alt false 3++Doubles 6 (1+n)++Alt false (24*4^n))).
  { unfold Parent0; change (Ladder true 6 (2+(2+n*2))) with
      (Alt true 7++Ladder true 12 (3+n*2)).
    eapply Pass_cat; [exact (@Pass_alt_even false 2 1 ltac:(left; lia))|].
    eapply Pass_cat; [exact (@Pass_alt_odd_P 3 3)|exact H]. }
  pose proof (@Life_internal Edge TM3.retire _ 1 [0] _ _ ltac:(discriminate) HP) as HL.
  unfold TM3.retire in HL.
  replace (4+n*2+48*4^n) with ((2+n+24*4^n)*2) in HL by lia.
  rewrite odd_0 in HL; cbn[negb] in HL.
  unfold MidWord; rewrite <- !app_assoc in HL; applys_eq HL; flia.
Qed.

Lemma Parent1_internal n : NLife (Parent1 (1+n*2)) [1;0] (MidWord n 0) [0].
Proof.
  pose proof (Pass_parent_tail n 0) as H.
  assert (HP : Pass (Parent1 (1+n*2)) 1 (2+n*2+48*4^n)
    (Alt true 2++Alt false 3++Doubles 6 (1+n)++Alt false (24*4^n))).
  { unfold Parent1; eapply Pass_cat; [exact (@Pass_alt_odd_I 1 1 ltac:(lia))|].
    eapply Pass_cat; [exact (@Pass_alt_even false 3 2 ltac:(left; lia))|exact H]. }
  pose proof (@Life_internal Edge TM3.retire _ 1 [0] _ _ ltac:(discriminate) HP) as HL.
  unfold TM3.retire in HL.
  replace (2+n*2+48*4^n) with ((1+n+24*4^n)*2) in HL by lia.
  rewrite odd_0 in HL; cbn[negb] in HL.
  unfold MidWord; rewrite <- !app_assoc in HL; applys_eq HL; flia.
Qed.

Definition SeedWord n h := Alt false 2++Alt true 3++Alt true 6++Doubles 12 n++
  Alt false (12*4^n)++Alt true (24*4^n+h)++Alt (Nat.odd h) (2+48*4^n+h).

Lemma MidWord_terminal n q : NLife (MidWord n q) [0] (SeedWord n (1+n+q)) [1].
Proof.
  pose proof (@Pass_Doubles n 12 12 ltac:(lia) ltac:(lia) eq_refl eq_refl) as H.
  pose proof (Nat.pow_nonzero 4 n ltac:(lia)) as HPow.
  replace (12+12*(4^n-1)) with (12*4^n) in H by lia.
  assert (EO : Nat.odd (12*4^n)=false) by (rewrite Nat.odd_mul; reflexivity).
  pose proof (@Pass_alt_even false (12*4^n) (12*4^n) ltac:(left; lia)) as HI.
  rewrite EO in HI; cbn[xorb] in HI.
  replace (12*4^n+12*4^n) with (24*4^n) in HI by lia.
  pose proof (@Pass_alt_odd_P (1+n+q+24*4^n) (24*4^n)) as HT.
  replace (Nat.odd (24*4^n)) with false in HT by (rewrite Nat.odd_mul; reflexivity).
  cbn[negb] in HT.
  assert (HP : Pass (Alt false 3++Doubles 6 (1+n)++Alt false (24*4^n)++
      Alt true (3+q*2+n*2+48*4^n)) 2 (2+n+q+48*4^n)
    (Alt false 2++Alt true 3++Alt true 6++Doubles 12 n++
      Alt false (12*4^n)++Alt true (24*4^n+(1+n+q)))).
  { cbn[Nat.add Doubles]; rewrite <- !app_assoc.
    eapply Pass_cat; [exact (@Pass_alt_odd_I 1 2 ltac:(lia))|].
    eapply Pass_cat; [exact (@Pass_alt_even false 3 3 ltac:(left; lia))|].
    eapply Pass_cat; [exact (@Pass_alt_even true 6 6 ltac:(right; reflexivity))|].
    applys_eq (Pass_cat H (Pass_cat HI HT)); flia. }
  pose proof (@Life_terminal Edge TM3.retire 1 _ 0 2 _ _ [1] (Edge_odd 0) HP) as HL.
  assert (E : negb (Nat.odd (2+n+q+48*4^n))=Nat.odd (1+n+q)).
  { replace (2+n+q+48*4^n) with (1+(1+n+q)+(24*4^n)*2) by lia.
    rewrite Nat.odd_add, odd_0, xorb_false_r.
    change (1+(1+n+q)) with (S (1+n+q)); rewrite odd_S, negb_involutive; reflexivity. }
  unfold TM3.retire in HL; rewrite E in HL.
  unfold MidWord, SeedWord; rewrite <- !app_assoc in HL; applys_eq HL; flia.
Qed.

Lemma RWord_entry n : NLives 3 (TM3.RWord (2+n*2)) [1] (SeedWord n (2+n)) [1].
Proof.
  replace (2+n) with (1+n+1) by lia.
  eapply Lives_cons; [apply RWord_parent|].
  eapply Lives_cons; [apply Parent0_internal|].
  econstructor; [exact (MidWord_terminal n 1)|constructor].
Qed.

Lemma RPrime_entry n : NLives 3 (TM3.RPrimeWord (1+n*2)) [1] (SeedWord n (1+n)) [1].
Proof.
  eapply Lives_cons; [apply RPrime_parent|].
  eapply Lives_cons; [apply Parent1_internal|].
  econstructor; [pose proof (MidWord_terminal n 0) as H; rewrite Nat.add_0_r in H; exact H|constructor].
Qed.

Fixpoint BNums k n h := match n with
  | 0 => [4^k+h]
  | S n => 4^k::(4^k*2-1)::BNums (1+k) n h end.

Definition Seed n q := 4^(2+n)::BNums 0 (2+n) (1+n+q).

Lemma FlatWord_BNums n : forall k h u,
  FlatWord (4^(1+k)) ((4^(1+k)*2-1)::BNums (2+k) n h) u =
  Doubles (4^(1+k)*3) n++Alt false (4^(1+k+n)*3)++Alt true (4^(1+k+n)*6+h)++
  Alt (Nat.odd h) (2+4^(2+k+n)+h+u*2).
Proof.
  induction n; intros k h u;
    assert (HP : 4^(1+k)<>0) by (apply Nat.pow_nonzero; lia);
    assert (EO : Nat.odd (4^(1+k))=false) by
      (replace (4^(1+k)) with ((4^k*2)*2) by (cbn[Nat.add Nat.pow]; lia); apply odd_0);
    assert (EO' : Nat.odd (4^(1+k)*2-1)=true) by
      (replace (4^(1+k)*2-1) with (1+(4^(1+k)-1)*2) by lia; apply odd_1).
  - cbn[BNums FlatWord Doubles app]; rewrite EO, EO', Nat.odd_add.
    replace (Nat.odd (4^(2+k))) with false by
      (replace (4^(2+k)) with ((4^(1+k)*2)*2) by (cbn[Nat.add Nat.pow]; lia); rewrite odd_0; reflexivity).
    cbn[xorb]; rewrite !Nat.add_0_r; cbn[Nat.add Nat.pow] in HP |- *; flia.
  - change (BNums (2+k) (S n) h) with
      (4^(2+k)::(4^(2+k)*2-1)::BNums (3+k) n h).
    change (Alt (Nat.odd (4^(1+k))) (1+4^(1+k)+(4^(1+k)*2-1))++
      Alt (Nat.odd (4^(1+k)*2-1)) (1+(4^(1+k)*2-1)+4^(2+k))++
      FlatWord (4^(2+k)) ((4^(2+k)*2-1)::BNums (3+k) n h) u =
      Doubles (4^(1+k)*3) (S n)++Alt false (4^(1+k+S n)*3)++
      Alt true (4^(1+k+S n)*6+h)++Alt (Nat.odd h) (2+4^(2+k+S n)+h+u*2)).
    rewrite EO, EO'.
    pose proof (IHn (1+k) h u) as H.
    replace (1+(1+k)) with (2+k) in H by lia.
    replace (2+(1+k)) with (3+k) in H by lia.
    rewrite H; cbn[Doubles].
    replace (1+k+S n) with (1+(1+k)+n) by lia.
    replace (2+k+S n) with (2+(1+k)+n) by lia.
    rewrite <- !app_assoc; cbn[Nat.add Nat.pow] in HP |- *; flia.
Qed.

Lemma Seed_word n q : FlatWord 0 (tl (Seed n q)) (hd 0 (Seed n q))=SeedWord n (1+n+q).
Proof.
  change (Alt false 2++Alt true 3++Alt true 6++
    FlatWord 4 (7::BNums 2 n (1+n+q)) (4^(2+n))=SeedWord n (1+n+q)).
  rewrite (@FlatWord_BNums n 0); unfold SeedWord; cbn[Nat.add Nat.pow]; flia.
Qed.

Lemma RWord_flat_entry n : NLives 3 (TM3.RWord (2+n*2)) [1]
  (FlatWord 0 (tl (Seed n 1)) (hd 0 (Seed n 1))) [1].
Proof. rewrite Seed_word; applys_eq (RWord_entry n); flia. Qed.

Lemma RPrime_flat_entry n : NLives 3 (TM3.RPrimeWord (1+n*2)) [1]
  (FlatWord 0 (tl (Seed n 0)) (hd 0 (Seed n 0))) [1].
Proof. rewrite Seed_word; applys_eq (RPrime_entry n); flia. Qed.

Lemma BNums_mass n : forall k h, total (BNums k n h)+n=4^k*(4^n*2-1)+h.
Proof.
  induction n; intros k h; cbn[BNums total Nat.pow].
  - lia.
  - pose proof (Nat.pow_nonzero 4 k ltac:(lia)) as HP.
    pose proof (Nat.pow_nonzero 4 n ltac:(lia)) as HQ.
    pose proof (IHn (1+k) h) as H.
    change (total (BNums (1+k) n h)+n=4*4^k*(4^n*2-1)+h) in H; nia.
Qed.

Lemma BNums_bounds n : forall k h, h<4^(k+n) ->
  Forall2 le (TM3.BinaryCaps (k*2) (n*2)++[4^(k+n)]) (BNums k n h) /\
  Forall2 le (BNums k n h) (TM3.BinaryCaps (1+k*2) (1+n*2)).
Proof.
  induction n; intros k h HH; pose proof (Nat.pow_nonzero 4 k ltac:(lia)) as HP.
  - cbn[BNums TM3.BinaryCaps Nat.add Nat.pow]; rewrite TM3.power4, Nat.add_0_r.
    rewrite Nat.add_0_r in HH.
    change (Forall2 le [4^k] [4^k+h] /\ Forall2 le [4^k+h] [2*4^k-1]).
    split; (constructor; [lia|constructor]).
  - replace (k+S n) with (1+k+n) in HH by lia.
    destruct (IHn (1+k) h HH) as [HL HU].
    replace (S n*2) with (2+n*2) by lia.
    cbn[BNums TM3.BinaryCaps Nat.add Nat.pow]; rewrite TM3.power4.
    replace (1+(1+(k*2))) with ((1+k)*2) by lia.
    replace (1+(1+(1+(k*2)))) with (1+(1+k)*2) by lia.
    replace (k+S n) with (1+k+n) by lia.
    split.
    + constructor; [lia|constructor; [lia|]]. applys_eq HL; flia.
    + constructor; [lia|constructor; [lia|]].
      replace (1+(1+k)*2) with (3+k*2) in HU by lia.
      cbn[TM3.BinaryCaps Nat.add Nat.pow] in HU; rewrite TM3.power4 in HU; exact HU.
Qed.

Lemma seed_budget n : n+2<4^(2+n).
Proof.
  induction n; [cbn; lia|].
  replace (2+S n) with (S (2+n)) by lia; cbn[Nat.pow]; lia.
Qed.

Lemma Seed_bounds n q : q<=1 ->
  Forall2 le (FlatLower (TM3.RBound (1+n)) (TM3.RHeight (1+n))) (Seed n q) /\
  Forall2 le (tl (Seed n q)) (FlatUpper (TM3.RBound (1+n)) (TM3.RHeight (1+n))).
Proof.
  intro HQ; pose proof (seed_budget n).
  destruct (@BNums_bounds (2+n) 0 (1+n+q) ltac:(rewrite Nat.add_0_l; lia)) as [HL HU].
  assert (EP : 2^(1+(1+n)*2)<>0) by (apply Nat.pow_nonzero; lia).
  assert (EQ : 4^(2+n)=2^(1+(1+n)*2)*2).
  { rewrite <- TM3.power4; replace ((2+n)*2) with (1+(1+(1+n)*2)) by lia.
    change (2*2^(1+(1+n)*2)=2^(1+(1+n)*2)*2); lia. }
  split.
  - unfold Seed, FlatLower, TM3.RBound, TM3.RHeight; constructor; [lia|].
    replace (2+(2^(1+(1+n)*2)-1)*2) with (4^(2+n)) by lia.
    change (Forall2 le ((0::TM3.BinaryCaps 1 (1+(1+n)*2))++[4^(2+n)]) (BNums 0 (2+n) (1+n+q))).
    change (Forall2 le (TM3.BinaryCaps 0 (2+(1+n)*2)++[4^(2+n)]) (BNums 0 (2+n) (1+n+q))).
    applys_eq HL; flia.
  - unfold Seed, FlatUpper, TM3.RBound, TM3.RHeight; cbn[tl].
    change (Forall2 le (BNums 0 (2+n) (1+n+q)) (TM3.BinaryCaps 1 (1+(2+n)*2))) in HU.
    replace (1+(2+n)*2) with ((1+(1+n)*2)+2) in HU by lia.
    rewrite TM3.BinaryCaps_app in HU; cbn[TM3.BinaryCaps] in HU.
    cbn[Nat.add Nat.pow] in EP, HU |- *; applys_eq HU; flia.
Qed.

Lemma Seed_excess n q : total (Seed n q)=
  total (FlatLower (TM3.RBound (1+n)) (TM3.RHeight (1+n)))+(3+n*2+q).
Proof.
  pose proof (@BNums_mass (2+n) 0 (1+n+q)) as HM.
  destruct (FlatLower_capacity (TM3.RSeed_box (1+n))) as [HP HB].
  replace (1+(1+(1+n)*2)) with ((2+n)*2) in HP by lia; rewrite TM3.power4 in HP.
  change (total (Seed n q)=2+TM3.RHeight (1+n)*2+
    total (tl (FlatLower (TM3.RBound (1+n)) (TM3.RHeight (1+n))))+(3+n*2+q)).
  unfold Seed; cbn[total]; cbn[Nat.pow] in HM; lia.
Qed.

Lemma Seed_window n q t : q<=1 -> t<=((11+n*2)*4+12)*(10+n*2)+2 -> exists ys,
  FlatSteps (11+n*2) t (Seed (3+n) q) ys /\
  Forall2 le (FlatLower (TM3.RBound (4+n)) (TM3.RHeight (4+n))) ys /\
  Forall2 le (tl ys) (FlatUpper (TM3.RBound (4+n)) (TM3.RHeight (4+n))) /\
  total ys=total (Seed (3+n) q)+t.
Proof.
  intros HQ HT; destruct (Seed_bounds (3+n) HQ) as [HL HU].
  eapply (@FlatLower_large_window n (TM3.RBound (4+n)) (TM3.RHeight (4+n)) (10+n*2) t (Seed (3+n) q)).
  - applys_eq (TM3.RSeed_box (4+n)); flia.
  - exact HL.
  - exact HU.
  - rewrite Seed_excess; replace (1+(3+n)) with (4+n) by lia; lia.
  - lia.
Qed.

Lemma Seed_absorption n q : q<=1 -> exists ys,
  FlatSteps (11+n*2) (((11+n*2)*4+12)*(9+n*2+q)) (Seed (3+n) q) ys /\
  FlatAligned (11+n*2) (FlatLower (TM3.RBound (4+n)) (TM3.RHeight (4+n)))
    (((11+n*2)*4+12)*(9+n*2+q)+(9+n*2+q)) ys.
Proof.
  intro HQ; set (N:=11+n*2); set (K:=9+n*2+q); set (C:=N*4+12).
  assert (Hbox : FlatBox (9+n*2) (TM3.RBound (4+n)) (TM3.RHeight (4+n))).
  { applys_eq (TM3.RSeed_box (4+n)); flia. }
  destruct (Seed_window n HQ (t:=C*K) ltac:(unfold C,N,K; nia)) as [ys [Hrun _]].
  destruct (Seed_bounds (3+n) HQ) as [HL HU].
  destruct (@FlatLower_large_window n (TM3.RBound (4+n)) (TM3.RHeight (4+n)) 0 (C*K+K+1)
    (FlatLower (TM3.RBound (4+n)) (TM3.RHeight (4+n))) Hbox (le_refl_list _)
    (FlatLower_bounds Hbox) ltac:(lia) ltac:(unfold C,N,K; nia)) as [endc [Hmain _]].
  destruct (FlatLower_step Hbox) as [next [HS [HB HC]]].
  replace (2+(9+n*2)) with N in HS by (unfold N; lia).
  exists ys; split; [exact Hrun|].
  eapply Flat_many_absorbs; [unfold N; lia|unfold C; lia|exact HS|exact HB|exact HC|exact HL| |exact Hmain|exact Hrun].
  rewrite Seed_excess; replace (1+(3+n)) with (4+n) by lia; unfold K; lia.
Qed.

Theorem Seed_exit n q : q<=1 ->
  NLives (4^(5+n)*3-q) (FlatWord 0 (tl (Seed (3+n) q)) (hd 0 (Seed (3+n) q))) [1]
    (Alt false 3++TM3.RTail (9+n*2)) [1] \/
  NLives (4^(5+n)*3-1-q) (FlatWord 0 (tl (Seed (3+n) q)) (hd 0 (Seed (3+n) q))) [1]
    (TM3.FlatEarlyWord (8+n*2)) [1].
Proof.
  intro HQ; set (N:=11+n*2); set (K:=9+n*2+q); set (C:=N*4+12); set (P:=4^(5+n)).
  set (root:=FlatLower (TM3.RBound (4+n)) (TM3.RHeight (4+n))).
  set (J:=C*K+K); set (T:=P*3-1-q-C*K); set (L:=P*3+(9+n*2)).
  assert (HBudget : C*K+K+3<P).
  { pose proof (FlatLower_budget n) as H.
    replace (2^(10+n*2)) with (4^(5+n)) in H by (rewrite <- TM3.power4; f_equal; lia).
    unfold C,N,K,P; nia. }
  assert (ET : J+T+1=L) by (unfold J,T,L,K; lia).
  assert (ET' : C*K+T=P*3-1-q) by (unfold T; lia).
  destruct (Seed_absorption n HQ) as [cut [Hentry HA]].
  change (FlatAligned N root J cut) in HA.
  pose proof (TM3.RLower_exit n) as Hfull.
  change (FlatSteps N L root (2^N::TM3.PowBody 1 N)) in Hfull.
  assert (Href : FlatSteps N (J+T+1) root (2^N::TM3.PowBody 1 N)) by (rewrite ET; exact Hfull).
  destruct (@FlatAligned_continue N root J cut ltac:(unfold N; lia) HA T _ Href) as [out [Hout HAligned]].
  assert (Htrace : NLives (P*3-1-q) (FlatWord 0 (tl (Seed (3+n) q)) (hd 0 (Seed (3+n) q))) [1]
    (FlatWord 0 (tl out) (hd 0 out)) [1]).
  { rewrite <- ET'; eapply FlatSteps_lives; eapply FlatSteps_app; [exact Hentry|exact Hout]. }
  destruct (FlatLower_step (TM3.RSeed_box (4+n))) as [next [Hstep [Hbump Hcarry]]].
  replace (2+(1+(4+n)*2)) with N in Hstep by (unfold N; lia).
  change (FlatStep N root next) in Hstep.
  assert (HL : L=2+(P*3+(7+n*2))) by (unfold L; lia); rewrite HL in Hfull.
  assert (HJ : J+T=1+(P*3+(7+n*2))) by lia; rewrite HJ in HAligned.
  change (FlatSteps N (2+(P*3+(7+n*2))) root
    (2^N::2::4::TM3.PowBody 3 (9+n*2))) in Hfull.
  destruct (FlatAligned_final (N:=N) ltac:(unfold N; lia) Hstep Hbump Hcarry Hfull HAligned)
    as [[-> Hlast] | ->].
  - left.
    assert (Hone : FlatSteps N 1 (2^N::1::4::TM3.PowBody 3 (9+n*2)) (2^N::2::4::TM3.PowBody 3 (9+n*2)))
      by (econstructor; [constructor|exact Hlast]).
    pose proof (FlatSteps_lives Hone) as HF; cbn[hd tl] in HF.
    change (2::4::TM3.PowBody 3 (9+n*2)) with (TM3.PowBody 1 (2+(9+n*2))) in HF.
    unfold N in HF; replace (11+n*2) with (2+(9+n*2)) in HF by lia; rewrite TM3.FlatExit_word in HF.
    change (4^(5+n)*3-q) with (P*3-q).
    replace (P*3-q) with ((P*3-1-q)+1) by lia; eapply Lives_app; [exact Htrace|exact HF].
  - right; cbn[hd tl] in Htrace.
    replace (9+n*2) with (1+(8+n*2)) in Htrace by lia.
    unfold N in Htrace; replace (11+n*2) with (3+(8+n*2)) in Htrace by lia.
    rewrite TM3.FlatEarly_word in Htrace; exact Htrace.
Qed.

Definition Word n q := if q=?0 then TM3.RPrimeWord (1+n*2) else TM3.RWord (2+n*2).

Lemma Word_entry n q : q<=1 -> NLives 3 (Word n q) [1]
  (FlatWord 0 (tl (Seed n q)) (hd 0 (Seed n q))) [1].
Proof.
  destruct q as [|[|q]]; intro HQ; [apply RPrime_flat_entry|apply RWord_flat_entry|lia].
Qed.

Lemma Word_round n q : q<=1 -> exists t q', q'<=1 /\
  NLives (1+t) (Word (3+n) q) [1] (Word (4+n) q') [1].
Proof.
  intro HQ; destruct (Seed_exit n HQ) as [HO|HE].
  - pose proof (Lives_app (Word_entry (3+n) HQ) (Lives_app HO (First_ordinary_round (9+n*2)))) as H.
    exists (2+(4^(5+n)*3-q)+2^(2+(9+n*2))*3),1; split; [lia|].
    change (Word (4+n) 1) with (TM3.RWord (2+(4+n)*2)).
    applys_eq H; flia.
  - pose proof (Lives_app (Word_entry (3+n) HQ) (Lives_app HE (First_early_round (8+n*2)))) as H.
    exists (2+(4^(5+n)*3-1-q)+2^(3+(8+n*2))*3),0; split; [lia|].
    change (Word (4+n) 0) with (TM3.RPrimeWord (1+(4+n)*2)).
    applys_eq H; flia.
Qed.

Lemma Word_suffix_infinite : forall n q, q<=1 -> forall t w xs,
  NLives t w xs (Word (3+n) q) [1] -> InfiniteLife Edge TM3.retire w xs.
Proof.
  cofix IH; intros n q HQ t w xs H; destruct t.
  - inversion H; subst. destruct (Word_round n HQ) as [t [r [HR HT]]].
    replace (4+n) with (3+(1+n)) in HT by lia.
    inversion HT; subst; econstructor; [eassumption|eapply (IH (1+n) r HR t); eassumption].
  - inversion H; subst; econstructor; [eassumption|eapply (IH n q HQ t); eassumption].
Qed.

Theorem Word_infinite n q : q<=1 -> InfiniteLife Edge TM3.retire (Word (3+n) q) [1].
Proof. intro HQ; eapply (@Word_suffix_infinite n q HQ 0); constructor. Qed.

Lemma flat_to_small_seed : NLives 10 (FlatWord 0 [1] 2) [1] (FlatWord 0 [1;1;5] 4) [1].
Proof.
  do 2 (eapply Lives_cons;
    [eapply Life_terminal with (k:=0) (b:=2); [exact (Edge_odd 0)|
      repeat first [apply Pass_nil | apply Pass_P | apply Pass_I; [lia|]]]|]).
  do 5 (eapply Lives_cons;
    [eapply Life_terminal with (k:=2) (b:=4); [exact (Edge_odd 1)|
      repeat first [apply Pass_nil | apply Pass_P | apply Pass_I; [lia|]]]|]).
  eapply Lives_cons;
    [eapply Life_terminal with (k:=1) (b:=2); [exact (Edge_even 0)|
      repeat first [apply Pass_nil | apply Pass_P | apply Pass_I; [lia|]]]|].
  eapply Lives_cons;
    [eapply Life_internal; [discriminate|
      repeat first [apply Pass_nil | apply Pass_P | apply Pass_I; [lia|]]]|].
  eapply Lives_cons;
    [eapply Life_terminal with (k:=1) (b:=2); [exact (Edge_odd 0)|
      repeat first [apply Pass_nil | apply Pass_P | apply Pass_I; [lia|]]]|].
  constructor.
Qed.

Lemma initial_seed_checked : FlatEval.check 3 11 [1;1;5] 4 (TM3.PowBody 1 3) 8=true.
Proof. vm_compute; reflexivity. Qed.

Lemma flat_to_R4 : NLives 45 (FlatWord 0 [1] 2) [1] (Word 0 1) [1].
Proof.
  pose proof initial_seed_checked as HC; apply FlatEval.check_spec in HC.
  pose proof (FlatSteps_lives HC) as H; cbn[hd tl] in H.
  change 8 with (2^(2+1)) in H; change 3 with (2+1) in H; rewrite TM3.FlatExit_word in H.
  exact (Lives_app flat_to_small_seed (Lives_app H (First_ordinary_round 1))).
Qed.

Definition small_check (c:nat*nat*bool) := let '(n,q,early):=c in
  FlatEval.check (5+n*2) (4^(2+n)*3-q-(if early then 1 else 0))
    (tl (Seed n q)) (hd 0 (Seed n q))
    (if early then 2::3::TM3.PowBody 3 (3+n*2) else TM3.PowBody 1 (5+n*2)) (2^(5+n*2)).

Lemma small_checked : forallb small_check [(0,1,false);(1,1,true);(2,0,false)]=true.
Proof. vm_compute; reflexivity. Qed.

Lemma small_steps n q early : In (n,q,early) [(0,1,false);(1,1,true);(2,0,false)] ->
  FlatSteps (5+n*2) (4^(2+n)*3-q-(if early then 1 else 0)) (Seed n q)
    (2^(5+n*2)::(if early then 2::3::TM3.PowBody 3 (3+n*2) else TM3.PowBody 1 (5+n*2))).
Proof.
  intro H; pose proof (proj1 (forallb_forall _ _) small_checked (n,q,early) H) as HC.
  apply FlatEval.check_spec in HC; exact HC.
Qed.

Lemma small_round n q early : In (n,q,early) [(0,1,false);(1,1,true);(2,0,false)] ->
  NLives (3+(4^(2+n)*3-q-(if early then 1 else 0))+2^(5+n*2)*3)
    (Word n q) [1] (Word (1+n) (if early then 0 else 1)) [1].
Proof.
  intro H; assert (HQ : q<=1).
  { cbn in H; destruct H as [H|[H|[H|[]]]]; inversion H; lia. }
  pose proof (FlatSteps_lives (small_steps H)) as HL; cbn[hd tl] in HL.
  pose proof (Word_entry n HQ) as HE; destruct early.
  - replace (5+n*2) with (3+(2+n*2)) in HL by lia.
    replace (3+n*2) with (1+(2+n*2)) in HL by lia; rewrite TM3.FlatEarly_word in HL.
    change (Word (1+n) 0) with (TM3.RPrimeWord (1+(1+n)*2)).
    applys_eq (Lives_app HE (Lives_app HL (First_early_round (2+n*2)))); flia.
  - replace (5+n*2) with (2+(3+n*2)) in HL by lia; rewrite TM3.FlatExit_word in HL.
    change (Word (1+n) 1) with (TM3.RWord (2+(1+n)*2)).
    applys_eq (Lives_app HE (Lives_app HL (First_ordinary_round (3+n*2)))); flia.
Qed.

Lemma flat_to_R10 : NLives 3075 (FlatWord 0 [1] 2) [1] (Word 3 1) [1].
Proof.
  exact (Lives_app flat_to_R4
    (Lives_app (@small_round 0 1 false ltac:(cbn; auto))
    (Lives_app (@small_round 1 1 true ltac:(cbn; auto))
               (@small_round 2 0 false ltac:(cbn; auto))))).
Qed.

Lemma flat_infinite : InfiniteLife Edge TM3.retire (FlatWord 0 [1] 2) [1].
Proof. eapply Lives_infinite; [exact flat_to_R10|exact (@Word_infinite 0 1 ltac:(lia))]. Qed.

Lemma initial_flow : Lives Edge retire 2 [] [3;2;1] (Alt false 2++Alt true 5) [1].
Proof.
  do 2 (eapply Lives_cons;
    [eapply Life_internal; [discriminate|
      repeat first [apply Pass_nil | apply Pass_P | apply Pass_I; [lia|]]]|]).
  constructor.
Qed.

Lemma initial_infinite : InfiniteLife Edge retire [] [3;2;1].
Proof.
  eapply Lives_infinite; [apply initial_flow|].
  eapply TM6.InfiniteLife_trim; [exact Edge_positive|exact flat_infinite|].
  exact (TM6.Trim_make [false;true;true;false;true]).
Qed.

Theorem nonhalt : ~halts tm c0.
Proof. apply nonhalt_from_lives, initial_infinite. Qed.

End TM7.

Module TM5.
Definition tm := Eval compute in (TM_from_str "1RB1LC_1RC---_0LD1RF_0LE1LE_0LA1LE_0RC0RB").
Notation "c -->* c'" := (c -[tm]->* c') (at level 40).
Notation "c -->+ c'" := (c -[tm]->+ c') (at level 40).

Fixpoint LC (xs:list nat) :=
  match xs with [] => 0inf | a::xs => LC xs <* <[1;0]^^a <* <[1] end.
Definition S1 xs n := LC xs {{C}}> [1;0]^^n *> 0inf.
Definition QL (p:bool) := if p then C else E.

Inductive Edge : nat -> nat -> list nat -> Prop :=
| Edge_even a : Edge (a*2) (1+a*2) [0;0]%nat
| Edge_odd a : Edge (1+a*2) (3+a*2) [1;0]%nat.

Notation LInc := (Flow_LInc Edge).
Notation Run := (Flow_Run Edge).
Definition retire a := Alt (Nat.odd a) (1+a).

Lemma Edge_size a b kids : Edge a b kids -> length kids<=2.
Proof. intro H; destruct H; cbn; lia. Qed.

Lemma Edge_functional a b kids c kids' :
  Edge a b kids -> Edge a c kids' -> b=c /\ kids=kids'.
Proof. intros H H'; destruct H; inversion H'; subst; split; try reflexivity; f_equal; lia. Qed.

Lemma LInc_spec p xs ys : LInc p xs ys ->
  forall r, LC xs <{{QL p}} [1;0] *> r -->* LC ys {{C}}> r.
Proof.
  intro H; induction H; intros r.
  - cbn[LC QL]; es.
  - destruct (mod2 a) as [k E|k E]; subst a.
    + rewrite odd_0 in IHLInc. destruct k as [|k]; [lia|].
      replace (S k*2) with (2+k*2) by lia.
      cbn[LC QL] in *; es; er; follow IHLInc; es.
    + rewrite odd_1 in IHLInc. cbn[LC QL] in *; es; er; follow IHLInc; es.
  - destruct H; cbn[LC QL]; es.
Qed.

Lemma Inc_right n xs ys : LInc (Nat.odd n) xs ys ->
  S1 xs (1+n) -->* S1 ys n.
Proof.
  intro H; destruct (mod2 n) as [a E|a E]; subst n.
  - rewrite odd_0 in H. eapply LInc_spec in H. es; er; follow H; finish.
  - rewrite odd_1 in H. eapply LInc_spec in H. es; er; follow H; finish.
Qed.

Lemma Inc_zero a xs ys : LInc (Nat.odd a) xs ys ->
  S1 (a::xs) 0 -->+ S1 ys a.
Proof.
  intro H; destruct (mod2 a) as [k E|k E]; subst a.
  - rewrite odd_0 in H. eapply LInc_spec in H. unfold S1; cbn[LC].
    es; er; follow H; finish.
  - rewrite odd_1 in H. eapply LInc_spec in H. unfold S1; cbn[LC].
    es; er; follow H; finish.
Qed.

Lemma Run_right n xs ys : Run (Alt (negb (Nat.odd n)) n) xs ys ->
  S1 xs n -->* S1 ys 0.
Proof.
  revert xs; induction n; intros xs H.
  - inversion H; subst; apply evstep_refl.
  - cbn[Alt] in H. rewrite Nat.odd_succ, Nat.negb_even in H.
    inversion H as [|p w source cut target HL HR]; subst.
    follow (Inc_right n HL). apply IHn; assumption.
Qed.

Lemma Macro_spec xs ys : Flow_Macro Edge retire xs ys -> S1 xs 0 -->+ S1 ys 0.
Proof.
  intro H; destruct H. cbn[retire Alt] in H.
  inversion H as [|p w source cut target HL HR]; subst.
  follow10 (Inc_zero a HL). apply Run_right; assumption.
Qed.

Lemma init : c0 -->* S1 [2] 1.
Proof. unfold S1; esx. Qed.

Lemma first_cut : c0 -->* S1 [3;0;0]%nat 0.
Proof. follow init. apply Inc_right. apply LInc_edge, (Edge_even 1). Qed.

Lemma InfiniteMacro_nonhalt xs :
  Flow_InfiniteMacro Edge retire xs -> ~halts tm (S1 xs 0).
Proof.
  intro HI. eapply progress_nonhalt with
    (P:=fun c => exists ys, Flow_InfiniteMacro Edge retire ys /\ c=S1 ys 0).
  - intros c [ys [H ->]]. destruct H as [ys zs HM HI'].
    exists (S1 zs 0); split; [exists zs; auto|apply Macro_spec; assumption].
  - exists xs; auto.
Qed.

Lemma nonhalt_from_lives :
  Flow_InfiniteLife Edge retire [] [3;0;0]%nat -> ~halts tm c0.
Proof.
  intro H; eapply multistep_nonhalt; [apply first_cut|].
  apply InfiniteMacro_nonhalt. eapply InfiniteLife_sound;
    eauto using Edge_size, Edge_functional, Run_nil.
Qed.

Close Scope sym.

(* The base doubles at each segment; its parity supplies only the leading
   P of Word. All counter masks are false. *)
Fixpoint GWord (base x:nat) (xs:list nat) (u:nat) : list bool :=
  match xs with
  | [] => Alt (xorb (Nat.odd base) (Nat.odd x)) (1+base+x+u*2)
  | y::ys => Alt (xorb (Nat.odd base) (Nat.odd x)) (1+base+x+y) ++
      GWord (base*2) y ys u
  end.
Definition Word xs u := GWord 1 0 xs u.

Lemma Split_geo_adjacent x q r y q' r' b :
  Split false x q r -> Split false y q' r' ->
  Split (Nat.odd x) (1+b*2+x+y) (b+r+r') (1+b+q+q').
Proof.
  intros H H'; inversion H; subst; inversion H'; subst; rewrite ?odd_0, ?odd_1;
    first [apply Split_even_eq; lia | apply Split_odd0_eq; lia | apply Split_odd1_eq; lia].
Qed.

Lemma Pass_geo_block x q r y q' r' b s a :
  Split false x q r -> Split false y q' r' -> a<>0 -> a=b+r+s*2 ->
  Pass (Alt (Nat.odd x) (1+b*2+x+y)) a (a+(b+r+r'))
    (Alt (xorb (Nat.odd b) (Nat.odd q)) (1+b+q+q')).
Proof.
  intros HX HY Ha HE.
  assert (E : xorb (Nat.odd a) (Nat.odd x)=xorb (Nat.odd b) (Nat.odd q)).
  { rewrite HE, (Split_mass HX), !Nat.odd_add, odd_0, xorb_false_r.
    destruct (Nat.odd b), (Nat.odd q), (Nat.odd r); reflexivity. }
  rewrite <- E; apply Pass_alt_split; [eapply Split_geo_adjacent; eassumption|auto].
Qed.

Lemma GWord_pass xs : forall qs R, Scatter (repeat false (length xs)) xs qs R ->
  forall b x q r s u a, b<>0 -> Split false x q r -> a=b+r+s*2 -> exists A o,
    Pass (GWord (b*2) x xs u) a A o /\
    o++retire A=GWord b q (qs++[u]) (s+r+R).
Proof.
  induction xs as [|y xs IH]; intros qs R HS b x q r s u a Hb HX HE.
  - inversion HS; subst qs R.
    exists (a+(b+r+u)), (Alt (xorb (Nat.odd b) (Nat.odd q)) (1+b+q+u)); split.
    + cbn[GWord]; rewrite odd_0, xorb_false_l.
      eapply Pass_geo_block; [exact HX|exact (Split_even false u)|lia|exact HE].
    + assert (E : Nat.odd (a+(b+r+u))=Nat.odd u).
      { replace (a+(b+r+u)) with ((b+r+s)*2+u) by lia.
        rewrite Nat.odd_add, odd_0; reflexivity. }
      cbn[GWord app]; unfold retire; rewrite E, odd_0, xorb_false_l.
      f_equal; f_equal; lia.
  - cbn[length repeat] in HS.
    inversion HS as [|e y0 q0 r0 es tail out R0 HY HT]; subst e y0 es tail qs R.
    destruct (IH _ _ HT (b*2) y q0 r0 (s+r) u (a+(b+r+r0)) ltac:(lia) HY ltac:(lia))
      as [A [o [HP HO]]].
    exists A,(Alt (xorb (Nat.odd b) (Nat.odd q)) (1+b+q+q0)++o); split.
    + cbn[GWord]; rewrite odd_0, xorb_false_l.
      eapply Pass_cat; [eapply Pass_geo_block; eassumption || lia|exact HP].
    + rewrite <- app_assoc, HO; cbn[GWord app]; f_equal; f_equal; lia.
Qed.

Lemma internal_column xs qs r u : Scatter (repeat false (length xs)) xs (0::qs) r ->
  Life Edge retire (Word xs u) [0;0] (true::Word (qs++[u]) r) [0].
Proof.
  intro H; destruct xs as [|x xs]; [inversion H|].
  cbn[length repeat] in H; inversion H as [|e y q0 r0 es tail out R0 HX HT]; subst.
  destruct (@GWord_pass xs qs R0 HT 1 x 0 r0 0 u (1+r0) ltac:(lia) HX ltac:(lia))
    as [A [o [HP HE]]].
  change (o++retire A=Word (qs++[u]) (r0+R0)) in HE.
  rewrite <- HE. change (Life Edge retire (Word (x::xs) u) [0;0] ((true::o)++retire A) [0]).
  apply Life_internal; [discriminate|].
  inversion HX; subst; cbn[Word GWord Alt Nat.add Nat.mul app] in *;
    apply Pass_P, Pass_I; [lia|exact HP|lia|apply Pass_P; exact HP].
Qed.

Lemma parent_column xs qs r u : Scatter (repeat false (length xs)) xs (0::qs) r ->
  Life Edge retire (true::Word xs u) [0] (Word (qs++[u]) (1+r)) [0;0].
Proof.
  intro H; destruct xs as [|x xs]; [inversion H|].
  cbn[length repeat] in H; inversion H as [|e y q0 r0 es tail out R0 HX HT]; subst.
  destruct (@GWord_pass xs qs R0 HT 1 x 0 r0 1 u (3+r0) ltac:(lia) HX ltac:(lia))
    as [A [o [HP HE]]].
  change (o++retire A=Word (qs++[u]) (1+(r0+R0))) in HE.
  rewrite <- HE. inversion HX; subst; cbn[Word GWord Alt Nat.add Nat.mul app] in *.
  - eapply Life_terminal with (k:=2) (b:=3); [apply (Edge_even 1)|exact HP].
  - eapply Life_terminal with (k:=2) (b:=3); [apply (Edge_even 1)|apply Pass_P; exact HP].
Qed.

Lemma Tick_lives N xs u ys v : Tick (repeat false N) false xs u ys v 0 ->
  Lives Edge retire 2 (Word xs u) [0;0] (Word ys v) [0;0].
Proof.
  intro H; inversion H as [xs0 u0 mid root ys0 v0 a b H1 H2]; subst.
  assert (a=0 /\ b=0) as [-> ->] by lia.
  destruct (Half_length H1) as [EL EM]; rewrite repeat_length in EL.
  destruct (Half_length H2) as [EL' _]; rewrite repeat_length in EL'.
  rewrite <- EL in H1; rewrite <- EL' in H2; clear EL EL' EM.
  inversion H1; subst; inversion H2; subst.
  eapply Lives_cons; [apply internal_column; eassumption|].
  eapply Lives_cons; [apply parent_column; eassumption|constructor].
Qed.

Lemma Ticks_lives N t xs u ys v : Ticks (repeat false N) false t xs u ys v ->
  Lives Edge retire (t*2) (Word xs u) [0;0] (Word ys v) [0;0].
Proof.
  intro H; induction H; [constructor|].
  replace ((1+n)*2) with (2+n*2) by lia.
  eapply Lives_app; [apply (Tick_lives N); eassumption|assumption].
Qed.

(* Only the unit-routing table is translated; this is not a conjugacy of
   arbitrary full counter states or a way to discard boundary guards. *)
Definition RouteOffset i := match i with
  | 0 => 1 | _ => if Nat.odd i then 2 else 3 end.
Fixpoint RouteShift k (xs:list nat) := match xs with
  | [] => [] | a::xs => (RouteOffset k+a)::RouteShift (1+k) xs end.
Definition Move N i a j := TM2.Move N i (RouteOffset i+a) j.

Lemma RouteOffset_positive i : 0<i -> RouteOffset i=(if Nat.odd i then 2 else 3).
Proof. destruct i; reflexivity || lia. Qed.

Lemma RouteShift_nth xs : forall k i, i<length xs ->
  nth i (RouteShift k xs) 0=RouteOffset (k+i)+nth i xs 0.
Proof.
  induction xs; intros k [|i] HI; cbn[RouteShift nth length] in *; try lia.
  - rewrite Nat.add_0_r; reflexivity.
  - rewrite IHxs by lia; f_equal; f_equal; lia.
Qed.

Lemma RouteShift_bump i a xs ys : Bump i a xs ys -> forall k,
  Bump i (RouteOffset (k+i)+a) (RouteShift k xs) (RouteShift k ys).
Proof.
  intro H; induction H; intro k; cbn[RouteShift].
  - rewrite Nat.add_0_r. replace (RouteOffset k+(1+a)) with (1+(RouteOffset k+a)) by lia.
    constructor.
  - replace (k+(1+i)) with (1+k+i) by lia; constructor; apply IHBump.
Qed.

Lemma Move_root_even N a : Move N 0 (a*2) 0.
Proof. apply TM2.Move_root_odd. Qed.

Lemma Move_root_odd N a : Move N 0 (1+a*2) (N-1).
Proof. unfold Move; change (TM2.Move N 0 (1+(1+a*2)) (N-1)).
  replace (1+(1+a*2)) with ((1+a)*2) by lia; constructor. Qed.

Lemma Move_even N i a : 0<i -> Move N i (a*2) N.
Proof.
  intro HI; unfold Move; rewrite RouteOffset_positive by lia.
  destruct (Nat.odd i) eqn:EI.
  - replace (2+a*2) with ((1+a)*2) by lia; apply TM2.Move_odd_even; assumption.
  - replace (3+a*2) with (1+(1+a)*2) by lia; apply TM2.Move_even_odd; assumption.
Qed.

Lemma Move_one N i a : 1<i -> Move N i (1+a*4) 0.
Proof.
  intro HI; unfold Move; rewrite RouteOffset_positive by lia.
  destruct (Nat.odd i) eqn:EI.
  - replace (2+(1+a*4)) with (3+a*4) by lia; apply TM2.Move_odd3; assumption.
  - replace (3+(1+a*4)) with ((1+a)*4) by lia; apply TM2.Move_even0; assumption.
Qed.

Lemma Move_three N i a : 2<i -> Move N i (3+a*4) (i-2).
Proof.
  intro HI; unfold Move; rewrite RouteOffset_positive by lia.
  destruct (Nat.odd i) eqn:EI.
  - replace (2+(3+a*4)) with (1+(1+a)*4) by lia; apply TM2.Move_odd1; assumption.
  - replace (3+(3+a*4)) with (2+(1+a)*4) by lia; apply TM2.Move_even2; assumption.
Qed.

Inductive HalfRoute (N root:nat) : nat -> nat -> nat -> nat -> Prop :=
| HalfRoute_root a : HalfRoute N root 0 a N a
| HalfRoute_back i a : 0<i -> Nat.odd a=false -> HalfRoute N root i a 0 root
| HalfRoute_forward i a q r : 1<i -> Split false a q r -> Nat.odd a=true ->
    HalfRoute N root i a (i-1) q.

Lemma HalfMove_route N root i a j b : HalfMove (repeat false N) root i a j b ->
  HalfRoute N root i a j b.
Proof.
  intro H; destruct H; rewrite ?repeat_length, ?nth_repeat in *; cbn[xorb] in *.
  - constructor.
  - constructor; assumption || lia.
  - replace (1+i) with ((2+i)-1) by lia; econstructor; eassumption || lia.
Qed.

Lemma HalfRoute_pair N root out i a j b k c : 1<N ->
  HalfRoute N root i a j b -> HalfRoute N out j b k c -> Move N i a k.
Proof.
  intros HN H1 H2.
  destruct H1 as [a0|i0 a0 HI HE|i0 a0 q0 r0 HI HS HE];
    inversion H2 as [a1|i1 a1 HI1 HE1|i1 a1 q1 r1 HI1 HS1 HE1]; subst; try lia.
  - destruct (mod2 a0) as [x E|x E]; subst; rewrite ?odd_0, ?odd_1 in HE1;
      [apply Move_root_even|discriminate].
  - destruct (mod2 a0) as [x E|x E]; subst; rewrite ?odd_0, ?odd_1 in HE1;
      [discriminate|apply Move_root_odd].
  - destruct (mod2 a0) as [x E|x E]; subst; rewrite ?odd_0, ?odd_1 in HE;
      [apply Move_even; lia|discriminate].
  - pose proof (Split_forward HS HE) as EA.
    destruct (mod2 q0) as [x E|x E]; subst q0; rewrite ?odd_0, ?odd_1 in HE1; [|discriminate].
    replace a0 with (1+x*4) by lia; apply Move_one; assumption.
  - pose proof (Split_forward HS HE) as EA.
    destruct (mod2 q0) as [x E|x E]; subst q0; rewrite ?odd_0, ?odd_1 in HE1; [discriminate|].
    replace a0 with (3+x*4) by lia; replace (i0-1-1) with (i0-2) by lia.
    apply Move_three; lia.
Qed.

Lemma Tick_route N xs u ys v xs' u' ys' v' i a : 1<N ->
  Tick (repeat false N) false xs u ys v 0 ->
  Tick (repeat false N) false xs' u' ys' v' 0 ->
  Bump i a (u::xs) (u'::xs') -> exists j b,
  Move N i a j /\ Bump j b (v::ys) (v'::ys').
Proof.
  intros HN H H' HU.
  destruct (Tick_bump H H' HU) as [root [j [b [k [c [HM [HM' HB]]]]]]].
  exists k,c; split; [|exact HB].
  eapply HalfRoute_pair; [exact HN|apply HalfMove_route; exact HM|apply HalfMove_route; exact HM'].
Qed.

Lemma Move_waiting N xs ys i a j : 1<N -> Nat.odd N=false ->
  Bump i a xs ys -> Move N i a j ->
  Waiting 0 (RouteShift 0 xs) i -> Waiting N (RouteShift 0 xs) i ->
  Waiting 0 (RouteShift 0 ys) j /\ Waiting N (RouteShift 0 ys) j.
Proof.
  intros HN EN HB HM; eapply TM2.Move_waiting; [exact HN|exact EN| |exact HM].
  exact (RouteShift_bump HB 0).
Qed.

Lemma Apart_shift N n xs i k ys j l : Apart (Move N) n xs i k ys j l ->
  length xs=1+N -> i<=N -> k<=N ->
  Apart (TM2.Move N) n (RouteShift 0 xs) i k (RouteShift 0 ys) j l.
Proof.
  intro H; induction H; intros EL HI HK; [constructor; assumption|].
  assert (HJ : j<=N) by (eapply TM2.Move_bound; eassumption).
  assert (HL : l<=N) by (eapply TM2.Move_bound; eassumption).
  econstructor; [exact H|exact (RouteShift_bump H0 0)|exact H1| |].
  - rewrite RouteShift_nth by lia; exact H2.
  - apply IHApart; [pose proof (Bump_length H0); lia|exact HJ|exact HL].
Qed.

Theorem Apart_bound m n xs i k ys j l : 2<=m ->
  Apart (Move (m*2)) n xs i k ys j l -> length xs=1+m*2 -> i<=m*2 -> k<=m*2 ->
  Waiting 0 (RouteShift 0 xs) i -> Waiting (m*2) (RouteShift 0 xs) i ->
  n<=m*12+20.
Proof.
  intros HM H EL HI HK H0 HN.
  eapply TM2.Apart_bound; [exact HM|eapply Apart_shift; eassumption|exact HI|exact HK|exact H0|exact HN].
Qed.

Lemma initial_bump N xs u : 0<N ->
  Tick (repeat false N) false (repeat 0 N) 0 xs u 0 ->
  Bump 0 0 (0::repeat 0 N) (u::xs).
Proof.
  destruct N; [lia|intros _ HT].
  pose proof (Tick_late_zeros false (repeat false N)) as H; rewrite repeat_length in H.
  destruct (Tick_functional HT H) as [-> [-> _]]; constructor.
Qed.

Lemma canonical_waiting m n : 2<=m -> forall xs u ys v i a,
  Ticks (repeat false (m*2)) false n (repeat 0 (m*2)) 0 xs u ->
  Tick (repeat false (m*2)) false xs u ys v 0 -> Bump i a (u::xs) (v::ys) ->
  Waiting 0 (RouteShift 0 (u::xs)) i /\ Waiting (m*2) (RouteShift 0 (u::xs)) i.
Proof.
  intro HM; induction n; intros xs u ys v i a HP HT HB.
  - inversion HP; subst.
    destruct (Bump_position HB (initial_bump (N:=m*2) ltac:(lia) HT)) as [-> ->].
    split; [left; reflexivity|right].
    rewrite RouteShift_nth by (cbn[length]; rewrite repeat_length; lia).
    cbn[Nat.add]; rewrite RouteOffset_positive by lia; rewrite odd_0.
    change (Nat.odd (3+nth (m*2) (repeat 0 (1+m*2)) 0)=true).
    rewrite nth_repeat; reflexivity.
  - destruct (Ticks_unsnoc HP) as [prev [root [HR HS]]].
    assert (HU : One (root::prev) (u::xs)).
    { eapply (@Ticks_zero_unit (repeat false (m*2)) false n); rewrite repeat_length; eassumption. }
    destruct (One_bump HU) as [p [b Hprev]].
    destruct (IHn _ _ _ _ _ _ HR HS Hprev) as [HW0 HWN].
    destruct (Tick_route (N:=m*2) ltac:(lia) HS HT Hprev) as [j [c [HD Hnext]]].
    destruct (Bump_position Hnext HB) as [-> _].
    eapply Move_waiting; [lia|apply odd_0|exact Hprev|exact HD|exact HW0|exact HWN].
Qed.

Lemma couple_ticks m j t xs u noise z endc w endn q : 2<=m -> m*12+20<t ->
  Ticks (repeat false (m*2)) false j (repeat 0 (m*2)) 0 xs u ->
  Ticks (repeat false (m*2)) false (1+t) xs u endc w ->
  Ticks (repeat false (m*2)) false t noise z endn q ->
  One (u::xs) (z::noise) -> exists s ys root,
  s<=t /\ Ticks (repeat false (m*2)) false s noise z ys root /\
  Ticks (repeat false (m*2)) false (1+s) xs u ys root.
Proof.
  intros HM Ht HP HC HN HU.
  inversion HC as [|n0 xs0 u0 next v endc0 w0 HT HR]; subst.
  assert (HV : One (u::xs) (v::next)).
  { eapply (@Ticks_zero_unit (repeat false (m*2)) false j); rewrite repeat_length;
      [exact HP|eapply Ticks_snoc; eassumption]. }
  destruct (One_bump HV) as [i [a HB]]; destruct (One_bump HU) as [k [b HK]].
  destruct (canonical_waiting (m:=m) HM HP HT HB) as [HW0 HWN].
  destruct (@Ticks_couple_or_apart (repeat false (m*2)) false (Move (m*2))
    (fun _ _ _ _ _ _ _ _ _ _ => @Tick_route (m*2) _ _ _ _ _ _ _ _ _ _ ltac:(lia))
    t _ _ _ _ _ _ _ _ _ _ _ _ _ _ HT HR HN HB HK) as [HJ|[last [l [r HA]]]]; [exact HJ|].
  destruct (Tick_length HT) as [EL _]; rewrite repeat_length in EL.
  destruct (Bump_length HB) as [_ HI]; destruct (Bump_length HK) as [_ Hk]; cbn in HI, Hk.
  pose proof (@Apart_bound m t (u::xs) i k last l r HM HA ltac:(cbn; lia)
    ltac:(lia) ltac:(lia) HW0 HWN); lia.
Qed.

(* The first two capacities are zero. Appending one odd split doubles the
   available root capacity and adds one. *)
Inductive Box : nat -> list nat -> nat -> Prop :=
| Box_base : Box 0 [0;0] 0
| Box_next n xs h : Box n xs h -> Box (1+n) (xs++[1+h*2]) (1+h*2).

Lemma Box_total n : exists xs h, Box n xs h.
Proof. induction n as [|n [xs [h H]]]; eauto using Box_base, Box_next. Qed.

Lemma Box_spec n xs h : Box n xs h ->
  length xs=2+n /\ Half (repeat false (2+n)) 0 xs h xs h 0 /\
  h+1=2^n /\ exists tail, xs=0::0::tail.
Proof.
  intro H; induction H as [|n xs h H [EL [HB [EH [tail ->]]]]].
  - split; [reflexivity|split; [|split; [reflexivity|exists (@nil nat); reflexivity]]].
    change (Half ([false]++[false]) 0 ([0]++[0]) 0 ([0]++[0]) 0 0).
    eapply Half_box_extend; [apply Half_box_base; exact (Split_even false 0)|exact (Split_even false 0)].
  - split; [rewrite length_app; cbn in *; lia|split; [|split; [change (1+h*2+1=2*2^n); lia|eexists; reflexivity]]].
    replace (2+(1+n)) with ((2+n)+1) by lia; rewrite repeat_app.
    eapply Half_box_extend; [exact HB|constructor].
Qed.

Lemma Box_budget n : (12+n*2)*(6+n)*8+(6+n)*65+1<2^(10+n*2).
Proof.
  induction n; [cbn; lia|].
  replace (10+S n*2) with (2+(10+n*2)) by lia; rewrite Nat.pow_add_r.
  change ((12+S n*2)*(6+S n)*8+(6+S n)*65+1<4*2^(10+n*2)); nia.
Qed.

Lemma seed_absorbs m bounds h C k xs u : 2<=m -> m*12+20<C ->
  Half (repeat false (m*2)) 0 bounds h bounds h 0 ->
  total xs+u=k -> Forall2 le xs bounds -> k*(C+1)+1<=h ->
  exists t ys v, t<=k*C /\ Ticks (repeat false (m*2)) false t xs u ys v /\
    Ticks (repeat false (m*2)) false (t+k) (repeat 0 (m*2)) 0 ys v /\
    Lives Edge retire (t*2) (Word xs u) [0;0] (Word ys v) [0;0].
Proof.
  intros HM HC HB HE HX HK.
  pose proof (@Ticks_many_absorbs (repeat false (m*2)) false bounds h C HB) as Hmany.
  rewrite repeat_length in Hmany.
  destruct (Hmany
    (fun _ _ _ _ _ _ _ _ _ => @couple_ticks m _ C _ _ _ _ _ _ _ _ HM HC)
    k xs u HE HX HK) as [t [ys [v [Ht [HR [HP HY]]]]]].
  exists t,ys,v; repeat split; auto; eapply Ticks_lives; exact HR.
Qed.

(* Conservative redistribution during the second moving front. Its precise
   endpoint need not be written as an explicit vector of phases. *)
Inductive Conserves (N:nat) : nat -> list nat -> nat -> list nat -> nat -> Prop :=
| Conserves_nil xs u : Conserves N 0 xs u xs u
| Conserves_cons t xs u ys v zs w : Half (repeat false N) 0 xs u ys v 0 ->
    Conserves N t ys v zs w -> Conserves N (1+t) xs u zs w.

Lemma Conserves_mass N t xs u ys v : Conserves N t xs u ys v -> total ys+v=total xs+u.
Proof. intro H; induction H; [reflexivity|apply Half_mass in H; lia]. Qed.

Lemma Conserves_preserves N bounds h t xs u ys v :
  Half (repeat false N) 0 bounds h bounds h 0 -> Conserves N t xs u ys v ->
  Forall2 le xs bounds -> total xs+u<=h -> Forall2 le ys bounds.
Proof.
  intros HB H; induction H; intros HX HM; [exact HX|].
  destruct (Half_box_step HB H HX ltac:(lia)) as [HY _].
  apply IHConserves; [exact HY|apply Half_mass in H; lia].
Qed.

Definition Seed n xs u := Conserves (12+n*2) (11+n*2) (repeat 0 (12+n*2)) (6+n) xs u.

Theorem Seed_absorbs n xs u : Seed n xs u -> exists t ys v,
  t<=(6+n)*((12+n*2)*8+64) /\
  Ticks (repeat false (12+n*2)) false t xs u ys v /\
  Ticks (repeat false (12+n*2)) false (t+(6+n)) (repeat 0 (12+n*2)) 0 ys v /\
  Lives Edge retire (t*2) (Word xs u) [0;0] (Word ys v) [0;0].
Proof.
  intro HC; unfold Seed in HC.
  destruct (Box_total (10+n*2)) as [bounds [h H]].
  destruct (Box_spec H) as [EL [HB [EH _]]].
  replace (2+(10+n*2)) with (12+n*2) in EL, HB by lia.
  pose proof (zeros_le bounds) as HZ; rewrite EL in HZ.
  pose proof (Box_budget n) as Hbudget.
  pose proof (Conserves_preserves HB HC HZ ltac:(rewrite total_zeros; nia)) as HX.
  pose proof (Conserves_mass HC) as HM; rewrite total_zeros in HM; cbn[Nat.add] in HM.
  replace (12+n*2) with ((6+n)*2) in HB |- * by lia.
  apply (@seed_absorbs (6+n) bounds h ((12+n*2)*8+64) (6+n) xs u);
    assumption || nia.
Qed.

Fixpoint Wave b r k := match r with
  | 0 => Alt true (b-1)++Alt true (b*2)++Ladder false (b*4) k
  | S r => Alt (negb (Nat.odd (S r))) b++Wave (b*2) r k end.

Lemma Wave_pass r k : forall b, 0<b -> Nat.odd b=false -> exists A o,
  Pass (Wave (b*2) r k) b A o /\ o++retire A=Wave b r (1+k).
Proof.
  induction r; intros b Hb Eb.
  - destruct (Pass_ladder_return k (t:=b*4) ltac:(lia)) as [A [o [HP HE]]].
    assert (H1 : Pass (Alt true (b*2-1)) b (b*2) (Alt true (b-1))).
    { pose proof (@Pass_alt_odd_P (b-1) b) as H; rewrite Eb in H.
      replace (1+(b-1)*2) with (b*2-1) in H by lia.
      replace (1+b+(b-1)) with (b*2) in H by lia; exact H. }
    assert (H2 : Pass (Alt true (b*4)) (b*2) (b*4) (Alt true (b*2))).
    { pose proof (@Pass_alt_even true (b*2) (b*2) ltac:(right; reflexivity)) as H.
      rewrite odd_0 in H; cbn[xorb] in H.
      replace (b*2*2) with (b*4) in H by lia; replace (b*2+b*2) with (b*4) in H by lia; exact H. }
    exists A,(Alt true (b-1)++Alt true (b*2)++o); split.
    + cbn[Wave]; replace (b*2*2) with (b*4) by lia.
      replace (b*2*4) with (b*4*2) by lia.
      eapply Pass_cat; [exact H1|eapply Pass_cat; [exact H2|exact HP]].
    + unfold retire; rewrite <- !app_assoc, HE, odd_four; cbn[Wave Ladder Nat.add];
        replace (b*4*2) with (b*2*4) by lia; reflexivity.
  - destruct (IHr (b*2) ltac:(lia) (odd_0 b)) as [A [o [HP HE]]].
    pose proof (@Pass_alt_even (negb (Nat.odd (S r))) b b ltac:(left; lia)) as H.
    rewrite Eb, xorb_false_l in H; replace (b+b) with (b*2) in H by lia.
    exists A,(Alt (negb (Nat.odd (S r))) b++o); split.
    + cbn[Wave]; eapply Pass_cat; eassumption.
    + rewrite <- app_assoc, HE; reflexivity.
Qed.

Lemma Wave_H r k : exists A o, Pass (Wave 2 (1+r) k) 1 A o /\
  o++retire A=Nat.odd (1+r)::Wave 2 r (1+k).
Proof.
  destruct (@Wave_pass r k 2 ltac:(lia) eq_refl) as [A [o [HP HE]]].
  pose proof (@Pass_alt_even (negb (Nat.odd (1+r))) 1 1 ltac:(left; lia)) as H.
  replace (xorb (Nat.odd 1) (negb (Nat.odd (1+r)))) with (Nat.odd (1+r)) in H
    by (destruct (Nat.odd (1+r)); reflexivity).
  exists A,(Alt (Nat.odd (1+r)) 1++o); split.
  - change (Pass (Alt (negb (Nat.odd (1+r))) 2++Wave 4 r k) 1 A
      (Alt (Nat.odd (1+r)) 1++o)).
    eapply Pass_cat; [exact H|exact HP].
  - rewrite <- app_assoc, HE; reflexivity.
Qed.

Lemma H_internal w A o : Pass w 1 A o ->
  Life Edge retire (true::w) [0;0] (o++retire A) [0].
Proof. intro H; apply Life_internal; [discriminate|apply Pass_P; exact H]. Qed.

Lemma H_parent w A o : Pass w 1 A o ->
  Life Edge retire (false::w) [0] (o++retire A) [0;0].
Proof.
  intro H; change (Life Edge retire (repeat true 0++false::w) [0] (o++retire A) [0;0]).
  eapply Life_terminal; [exact (Edge_even 0)|exact H].
Qed.

Lemma Wave_pair n k : Lives Edge retire 2 (true::Wave 2 (2+n*2) k) [0;0]
  (true::Wave 2 (n*2) (2+k)) [0;0].
Proof.
  destruct (Wave_H (1+n*2) k) as [A [o [HP HE]]].
  replace (1+(1+n*2)) with ((1+n)*2) in HE by lia; rewrite odd_0 in HE.
  destruct (Wave_H (n*2) (1+k)) as [B [p [HQ HF]]].
  rewrite odd_1 in HF.
  replace (1+(1+k)) with (2+k) in HF by lia.
  eapply Lives_cons with (v:=false::Wave 2 (1+n*2) (1+k)) (ys:=[0]);
    [rewrite <- HE; apply H_internal; exact HP|].
  eapply Lives_cons; [|constructor]; rewrite <- HF; apply H_parent; exact HQ.
Qed.

Lemma Wave_pairs n : forall k, Lives Edge retire (n*2) (true::Wave 2 (n*2) k) [0;0]
  (true::Wave 2 0 (k+n*2)) [0;0].
Proof.
  induction n; intro k; [rewrite Nat.add_0_r; constructor|].
  replace (S n*2) with (2+n*2) by lia.
  replace (k+(2+n*2)) with (2+k+n*2) by lia.
  eapply Lives_app; [apply Wave_pair|apply IHn].
Qed.

Lemma Wave_zero_H k : exists A o, Pass (Wave 2 0 k) 1 A o /\
  o++retire A=Alt true 2++Ladder false 4 (1+k).
Proof.
  destruct (Pass_ladder_return k (t:=4) ltac:(lia)) as [A [o [HP HE]]].
  exists A,(Alt true 2++o); split.
  - change (Pass (true::(Alt true 4++Ladder false 8 k)) 1 A (Alt true 2++o)).
    apply Pass_P; eapply Pass_cat; [exact (@Pass_alt_even true 2 2 ltac:(right; reflexivity))|exact HP].
  - rewrite <- app_assoc; unfold retire; rewrite HE; reflexivity.
Qed.

Lemma Pass_ladder_high n : forall b, Nat.odd b=false ->
  Pass (Ladder false (b*2) n) (1+b) (1+b*2^n) (Ladder true b n).
Proof.
  induction n; intros b Eb.
  - cbn[Ladder Nat.pow]; rewrite Nat.mul_1_r; constructor.
  - pose proof (@Pass_alt_odd_I b (1+b) ltac:(lia)) as H.
    rewrite Nat.odd_add, Eb in H; cbn[xorb] in H.
    replace (1+b+b) with (1+b*2) in H by lia.
    cbn[Ladder Nat.pow]; replace (1+b*(2*2^n)) with (1+(b*2)*2^n) by lia.
    eapply Pass_cat; [exact H|apply IHn, odd_0].
Qed.

(* RWord n is the paper's R_(2+n). *)
Definition RWord n := Ladder true 2 (1+n)++Alt true (2+4*2^n).

Lemma RWord_terminal n : Life Edge retire (Alt true 2++Ladder false 4 (1+n)) [0]
  (RWord n) [1;0].
Proof.
  pose proof (@Pass_ladder_high (1+n) 2 eq_refl) as H.
  replace (1+2*2^(1+n)) with (1+(2*2^n)*2) in H by (cbn[Nat.pow Nat.add]; lia).
  pose proof (@Life_terminal Edge retire 1 _ 0 3 _ _ [1;0] (Edge_odd 0) H) as HL.
  unfold retire in HL; rewrite odd_1 in HL.
  unfold RWord; applys_eq HL; flia.
Qed.

Lemma Life_unprefix w v kids : Life Edge retire (true::w) [0;0] v kids ->
  Life Edge retire w [1;0] v kids.
Proof.
  intro H; inversion H; subst; match goal with H : Pass (true::_) 0 _ _ |- _ => inversion H; subst end.
  apply Life_internal; [discriminate|assumption].
Qed.

Lemma Lives_unprefix n w v kids : 0<n -> Lives Edge retire n (true::w) [0;0] v kids ->
  Lives Edge retire n w [1;0] v kids.
Proof.
  intros HN H; inversion H; subst; [lia|].
  eapply Lives_cons; [apply Life_unprefix; eassumption|eassumption].
Qed.

Theorem first_front n : Lives Edge retire (4+n*2) (Wave 2 (2+n*2) 0) [1;0]
  (RWord (2+n*2)) [1;0].
Proof.
  pose proof (Wave_pairs (1+n) 0) as H.
  replace ((1+n)*2) with (2+n*2) in H by lia; cbn[Nat.add] in H.
  apply Lives_unprefix in H; [|lia].
  replace (4+n*2) with ((2+n*2)+2) by lia.
  eapply Lives_app; [exact H|].
  destruct (Wave_zero_H (2+n*2)) as [A [o [HP HE]]].
  eapply Lives_cons with (v:=Alt true 2++Ladder false 4 (3+n*2)) (ys:=[0]).
  - change (o++retire A=Alt true 2++Ladder false 4 (3+n*2)) in HE.
    rewrite <- HE; apply H_internal; exact HP.
  - eapply Lives_cons; [apply RWord_terminal|constructor].
Qed.

Definition QWord n := Alt true 4++Doubles 8 n++Alt false (4^n*8-1)++Alt false (4^n*16-1).
Definition QInternal n := Alt true 2++Doubles 4 (1+n)++Alt false (4^n*16-3).

Lemma QWord_pass n : Pass (QWord n) 0 (4^n*16-4) (Alt true 2++Doubles 4 (1+n)).
Proof.
  pose proof (Nat.pow_nonzero 4 n ltac:(lia)) as Hpos.
  unfold QWord; replace (1+n) with (n+1) by lia; rewrite Doubles_snoc.
  replace (4*4^n) with (4^n*4) by lia; replace (4^n*4*2) with (4^n*8) by lia.
  eapply Pass_cat; [exact (@Pass_alt_even true 2 0 ltac:(auto))|].
  eapply Pass_cat with (b:=4^n*4-2).
  - applys_eq (@Pass_Doubles n 4 2 ltac:(lia) ltac:(lia) eq_refl eq_refl); flia.
  - eapply Pass_cat with (b:=4^n*8-3).
    + pose proof (@Pass_alt_odd_I (4^n*4-1) (4^n*4-2) ltac:(lia)) as H.
      replace (4^n*4-2) with ((4^n*2-1)*2) in H by lia; rewrite odd_0 in H.
      applys_eq H; flia.
    + pose proof (@Pass_alt_odd_I (4^n*8-1) (4^n*8-3) ltac:(lia)) as H.
      replace (4^n*8-3) with (1+(4^n*4-2)*2) in H by lia; rewrite odd_1 in H.
      applys_eq H; flia.
Qed.

Lemma Q_internal n : Life Edge retire (QWord n) [0;0] (QInternal n) [0].
Proof.
  pose proof (Nat.pow_nonzero 4 n ltac:(lia)) as Hpos.
  pose proof (@Life_internal Edge retire _ 0 [0] _ _ ltac:(discriminate) (QWord_pass n)) as HL.
  unfold retire in HL; replace (4^n*16-4) with ((4^n*8-2)*2) in HL by lia.
  rewrite odd_0, <- !app_assoc in HL; unfold QInternal; applys_eq HL; flia.
Qed.

Lemma Wave_even_shape n : forall b,
  Wave b (n*2) 0=map negb (Doubles b n)++Alt true (b*4^n-1)++Alt true (b*4^n*2).
Proof.
  induction n; intro b.
  - cbn[Wave Doubles Nat.pow Nat.mul map app Ladder]; rewrite !Nat.mul_1_r, app_nil_r; reflexivity.
  - replace (S n*2) with (2+n*2) by lia.
    cbn[Wave Nat.add]; rewrite !odd_S, !negb_involutive, odd_0; cbn[negb].
    replace (b*2*2) with (b*4) by lia; rewrite IHn.
    cbn[Doubles Nat.pow]; rewrite !map_app, !Alt_flip; cbn[negb].
    rewrite <- !app_assoc; flia.
Qed.

Lemma Q_parent n : Life Edge retire (QInternal n) [0] (Wave 2 (2+n*2) 0) [1;0].
Proof.
  pose proof (Nat.pow_nonzero 4 n ltac:(lia)) as Hpos.
  assert (HP : Pass (Doubles 4 (1+n)++Alt false (4^n*16-3)) 3 (4^n*16-1)
    (map negb (Doubles 2 (1+n))++Alt true (4^n*8-1))).
  { eapply Pass_cat with (b:=1+4^n*8).
    - pose proof (@Pass_Doubles_odd (1+n) 2 3 ltac:(lia) ltac:(lia) eq_refl eq_refl) as H.
      cbn[Nat.pow Nat.add] in H; applys_eq H; flia.
    - pose proof (@Pass_alt_odd_I (4^n*8-2) (1+4^n*8) ltac:(lia)) as H.
      replace (1+4^n*8) with (1+(4^n*4)*2) in H by lia; rewrite odd_1 in H.
      applys_eq H; flia. }
  pose proof (@Life_terminal Edge retire 1 _ 0 3 _ _ [1;0] (Edge_odd 0) HP) as HL.
  unfold retire in HL; replace (4^n*16-1) with (1+(4^n*8-1)*2) in HL by lia.
  rewrite odd_1 in HL.
  replace (2+n*2) with ((1+n)*2) by lia; rewrite Wave_even_shape.
  rewrite <- !app_assoc in HL.
  unfold QInternal; cbn[Nat.pow Nat.add]; applys_eq HL; flia.
Qed.

Theorem Q_to_R n : Lives Edge retire (6+n*2) (QWord n) [0;0] (RWord (2+n*2)) [1;0].
Proof.
  eapply Lives_cons; [apply Q_internal|].
  eapply Lives_cons; [apply Q_parent|apply first_front].
Qed.

(* Only the untouched prefix has a front index. The entire perturbed suffix
   is already the nonnegative GWord counter, with no classification of bits. *)
Fixpoint DWord b r xs u := match r with
  | 0 => GWord b 0 xs u
  | S r => Alt (Nat.odd (S r)) b++DWord (b*2) r xs u end.

Lemma DWord_pass r : forall xs qs R u b,
  Scatter (repeat false (length xs)) xs qs R -> 0<b -> Nat.odd b=false ->
  exists A o, Pass (DWord (b*2) r xs u) b A o /\
    o++retire A=DWord b r (qs++[u]) R.
Proof.
  induction r; intros xs qs R u b HS Hb Eb.
  - destruct (@GWord_pass xs qs R HS b 0 0 0 0 u b ltac:(lia) (Split_even false 0) ltac:(lia))
      as [A [o [HP HE]]]; exists A,o; split; assumption.
  - destruct (IHr xs qs R u (b*2) HS ltac:(lia) (odd_0 b)) as [A [o [HP HE]]].
    pose proof (@Pass_alt_even (Nat.odd (S r)) b b ltac:(left; lia)) as H.
    rewrite Eb, xorb_false_l in H; replace (b+b) with (b*2) in H by lia.
    exists A,(Alt (Nat.odd (S r)) b++o); split.
    + cbn[DWord]; eapply Pass_cat; eassumption.
    + rewrite <- app_assoc, HE; reflexivity.
Qed.

Lemma DWord_H r xs qs R u : Scatter (repeat false (length xs)) xs qs R ->
  exists A o, Pass (DWord 2 (1+r) xs u) 1 A o /\
    o++retire A=Nat.odd r::DWord 2 r (qs++[u]) R.
Proof.
  intro HS; destruct (@DWord_pass r xs qs R u 2 HS ltac:(lia) eq_refl) as [A [o [HP HE]]].
  pose proof (@Pass_alt_even (Nat.odd (1+r)) 1 1 ltac:(left; lia)) as H.
  assert (E : Nat.odd (1+r)=negb (Nat.odd r)) by apply odd_S.
  replace (xorb (Nat.odd 1) (Nat.odd (1+r))) with (Nat.odd r) in H
    by (rewrite E; destruct (Nat.odd r); reflexivity).
  exists A,(Alt (Nat.odd r) 1++o); split.
  - change (Pass (Alt (Nat.odd (1+r)) 2++DWord 4 r xs u) 1 A (Alt (Nat.odd r) 1++o)).
    eapply Pass_cat; [exact H|exact HP].
  - rewrite <- app_assoc, HE; reflexivity.
Qed.

Lemma DWord_zero_H xs qs R u : Scatter (repeat false (length xs)) xs qs R ->
  exists A o, Pass (DWord 2 0 xs u) 1 A o /\ o++retire A=Word (qs++[u]) R.
Proof.
  intro H; destruct (@GWord_pass xs qs R H 1 0 0 0 0 u 1 ltac:(lia)
    (Split_even false 0) ltac:(lia)) as [A [o [HP HE]]]; exists A,o; split; assumption.
Qed.

Lemma Front_half r xs qs R u : Scatter (repeat false (length xs)) xs qs R ->
  Half (repeat false (1+r+length xs)) 0 (repeat 0 (1+r)++xs) u
    (repeat 0 r++qs++[u]) R 0.
Proof.
  intro H; pose proof (Scatter_zeros (repeat false (1+r))) as HZ; rewrite repeat_length in HZ.
  pose proof (Scatter_app HZ H) as HS.
  rewrite <- repeat_app in HS; cbn[Nat.add repeat app] in HS.
  rewrite app_assoc; eapply Half_make with (r:=R); exact HS.
Qed.

Lemma DWord_life r xs qs R u : Scatter (repeat false (length xs)) xs qs R ->
  Life Edge retire (Nat.odd (1+r)::DWord 2 (1+r) xs u)
    (if Nat.odd (1+r) then [0;0] else [0])
    (Nat.odd r::DWord 2 r (qs++[u]) R) (if Nat.odd r then [0;0] else [0]).
Proof.
  intro H; destruct (DWord_H r u H) as [A [o [HP HE]]].
  rewrite <- HE; change (Nat.odd (1+r)) with (Nat.odd (S r)); rewrite odd_S.
  destruct (Nat.odd r); cbn[negb]; [apply H_parent|apply H_internal]; exact HP.
Qed.

Theorem DWord_run r : forall xs u, exists ys v,
  Conserves (1+r+length xs) (1+r) (repeat 0 (1+r)++xs) u ys v /\
  Lives Edge retire (1+r) (Nat.odd r::DWord 2 r xs u)
    (if Nat.odd r then [0;0] else [0]) (Word ys v) [0;0].
Proof.
  induction r; intros xs u.
  destruct (Scatter_total (repeat false (length xs)) xs (repeat_length false (length xs)))
    as [qs [R HS]].
  - exists (qs++[u]),R; split.
    + eapply Conserves_cons; [exact (Front_half 0 u HS)|constructor].
    + destruct (DWord_zero_H u HS) as [A [o [HP HE]]].
      eapply Lives_cons; [|constructor]; rewrite <- HE; apply H_parent; exact HP.
  - destruct (Scatter_total (repeat false (length xs)) xs (repeat_length false (length xs)))
      as [qs [R HS]].
    destruct (IHr (qs++[u]) R) as [ys [v [HC HL]]].
    destruct (Scatter_length HS) as [_ EL]; rewrite repeat_length in EL.
    assert (EN : 1+r+length (qs++[u])=1+S r+length xs) by (rewrite length_app; cbn; lia).
    rewrite EN in HC.
    exists ys,v; split.
    + eapply Conserves_cons; [|exact HC].
      exact (Front_half (1+r) u HS).
    + eapply Lives_cons; [exact (DWord_life r u HS)|exact HL].
Qed.

Lemma DWord_even_shape n : forall b xs u,
  DWord b (n*2) xs u=Doubles b n++GWord (b*4^n) 0 xs u.
Proof.
  induction n; intros b xs u.
  - cbn[DWord Doubles Nat.pow Nat.mul app]; rewrite Nat.mul_1_r; reflexivity.
  - replace (S n*2) with (2+n*2) by lia.
    cbn[DWord Nat.add]; rewrite !odd_S, negb_involutive, odd_0; cbn[negb].
    replace (b*2*2) with (b*4) by lia; rewrite IHn.
    cbn[Doubles Nat.pow]; rewrite <- !app_assoc; flia.
Qed.

Lemma DWord_root n u : DWord 2 (n*2) [0] u=Doubles 2 n++
  Alt false (1+4^n*2)++Alt false (1+4^n*4+u*2).
Proof.
  rewrite DWord_even_shape; cbn[GWord].
  replace (2*4^n) with (4^n*2) by lia; rewrite !odd_0.
  cbn[xorb Nat.odd]; flia.
Qed.

Lemma RWord_H n : exists A o, Pass (RWord (n*2)) 1 A o /\
  o++retire A=false::DWord 2 (n*2) [0] (1+n).
Proof.
  pose proof (Nat.pow_nonzero 4 n ltac:(lia)) as Hpos.
  pose proof (@TM3.Pass_ladder_P_pairs n 2 3 eq_refl eq_refl) as HM.
  replace (3+n*2+2*(4^n-1)) with (1+n*2+4^n*2) in HM by lia.
  pose proof (@Pass_alt_even true (1+4^n*2) (1+n*2+4^n*2) ltac:(right; reflexivity)) as HT.
  replace (1+n*2+4^n*2) with (1+(n+4^n)*2) in HT by lia; rewrite odd_1 in HT; cbn[xorb] in HT.
  exists (2+n*2+4^n*4),([false]++Doubles 2 n++Alt false (1+4^n*2)); split.
  - unfold RWord; rewrite TM3.power4.
    change (Ladder true 2 (1+n*2)) with (Alt true 3++Ladder true 4 (n*2)).
    rewrite <- !app_assoc.
    eapply Pass_cat; [exact (@Pass_alt_odd_P 1 1)|].
    eapply Pass_cat; [exact HM|applys_eq HT; flia].
  - unfold retire; replace (2+n*2+4^n*4) with ((1+n+4^n*2)*2) by lia.
    rewrite odd_0, DWord_root, <- !app_assoc; cbn[app]; flia.
Qed.

Theorem R_to_counter n : exists xs u,
  Conserves (2+n*2) (1+n*2) (repeat 0 (2+n*2)) (1+n) xs u /\
  Lives Edge retire (2+n*2) (RWord (n*2)) [1;0] (Word xs u) [0;0].
Proof.
  destruct (DWord_run (n*2) [0] (1+n)) as [xs [u [HC HL]]].
  cbn[length] in HC; rewrite zeros_snoc in HC.
  replace (1+n*2+1) with (2+n*2) in HC by lia.
  replace (1+(1+n*2)) with (2+n*2) in HC by lia.
  rewrite odd_0 in HL.
  exists xs,u; split; [exact HC|].
  destruct (RWord_H n) as [A [o [HP HE]]].
  eapply Lives_cons; [|exact HL]; rewrite <- HE.
  apply Life_internal; [discriminate|exact HP].
Qed.

Theorem R_to_Seed n : exists xs u, Seed n xs u /\
  Lives Edge retire (12+n*2) (RWord (10+n*2)) [1;0] (Word xs u) [0;0].
Proof.
  destruct (R_to_counter (5+n)) as [xs [u [HC HL]]]; exists xs,u; split.
  - unfold Seed; applys_eq HC; flia.
  - applys_eq HL; flia.
Qed.


Definition EvenCert N d k := Cycles [N;0;N;d] (4^k-1)++[N;0;N].
Definition OddCert N d k := Cycles [N;0;N;d] (4^k*2).
Fixpoint CertBody N n := match n with
  | 0 => [] | S k => CertBody N k++[EvenCert N (k*2) k;OddCert N (1+k*2) k] end.
Definition RootCert N n := Cycles [0;N-1] (4^n*2).
Definition LastCert N n := Cycles [N;0;N;N-2] (4^n-1)++[N;0].
Definition Rows n := RootCert (2+n*2) n::[2+n*2;3+n*2]::
  (CertBody (2+n*2) n++[LastCert (2+n*2) n]).

Lemma EvenCert_length N d k : length (EvenCert N d k)=4^k*4-1.
Proof. unfold EvenCert; rewrite length_app, Cycles_length; cbn[length].
  pose proof (Nat.pow_nonzero 4 k ltac:(lia)); lia. Qed.
Lemma OddCert_length N d k : length (OddCert N d k)=4^k*8.
Proof. unfold OddCert; rewrite Cycles_length; cbn[length]; lia. Qed.
Lemma RootCert_length N n : length (RootCert N n)=4^n*4.
Proof. unfold RootCert; rewrite Cycles_length; cbn[length]; lia. Qed.
Lemma LastCert_length N n : length (LastCert N n)=4^n*4-2.
Proof. unfold LastCert; rewrite length_app, Cycles_length; cbn[length].
  pose proof (Nat.pow_nonzero 4 n ltac:(lia)); lia. Qed.

Lemma EvenCert_count N d k v : count_occ Nat.eq_dec (EvenCert N d k) v=
  4^k*2*mark N v+4^k*mark 0 v+(4^k-1)*mark d v.
Proof.
  unfold EvenCert; rewrite count_occ_app, Cycles_count, !count_cons; cbn[count_occ].
  pose proof (Nat.pow_nonzero 4 k ltac:(lia)); nia.
Qed.
Lemma OddCert_count N d k v : count_occ Nat.eq_dec (OddCert N d k) v=
  4^k*4*mark N v+4^k*2*mark 0 v+4^k*2*mark d v.
Proof. unfold OddCert; rewrite Cycles_count, !count_cons; cbn[count_occ]; nia. Qed.
Lemma RootCert_count N n v : count_occ Nat.eq_dec (RootCert N n) v=
  4^n*2*mark 0 v+4^n*2*mark (N-1) v.
Proof. unfold RootCert; rewrite Cycles_count, !count_cons; cbn[count_occ]; nia. Qed.
Lemma LastCert_count N n v : count_occ Nat.eq_dec (LastCert N n) v=
  (4^n*2-1)*mark N v+4^n*mark 0 v+(4^n-1)*mark (N-2) v.
Proof.
  unfold LastCert; rewrite count_occ_app, Cycles_count, !count_cons; cbn[count_occ].
  pose proof (Nat.pow_nonzero 4 n ltac:(lia)); nia.
Qed.

Lemma CertBody_length N n : length (CertBody N n)=n*2.
Proof. induction n; cbn[CertBody]; rewrite ?length_app, ?IHn; cbn[length]; lia. Qed.

Lemma CertBody_balance N n v : incoming (CertBody N n) v+
  (4^n-1)*mark (n*2) v+4^n*2*mark (1+n*2) v=
  weighted (CertBody N n) 2 v+(4^n-1)*2*mark N v+(4^n-1)*mark 0 v+2*mark 1 v.
Proof.
  induction n as [|n IH]; [cbn[CertBody incoming weighted concat count_occ Nat.pow Nat.sub Nat.add Nat.mul]; lia|].
  cbn[CertBody]; unfold incoming in *.
  rewrite concat_app, count_occ_app, weighted_app, CertBody_length.
  cbn[concat weighted]; rewrite !count_occ_app, EvenCert_count, OddCert_count,
    EvenCert_length, OddCert_length; cbn[count_occ].
  replace (S n*2) with (2+n*2) by lia; replace (n*2+2) with (2+n*2) by lia.
  pose proof (Nat.pow_nonzero 4 n ltac:(lia)) as Hpos.
  cbn[Nat.pow]; replace (4*4^n-1) with (3+(4^n-1)*4) by lia.
  replace (4^n*4-1) with (3+(4^n-1)*4) by lia.
  remember (4^n-1) as q; replace (4^n) with (1+q) in * by lia.
  cbn[Nat.add] in *; ring_simplify in IH; ring_simplify; lia.
Qed.

Lemma Rows_length n : length (Rows n)=3+n*2.
Proof. unfold Rows; cbn[length]; rewrite length_app, CertBody_length; cbn; lia. Qed.

Theorem Rows_balance n : Balance (Rows n) 0 (3+n*2).
Proof.
  intro v; pose proof (CertBody_balance (2+n*2) n v) as HB.
  unfold Rows, incoming; cbn[concat]; rewrite concat_app; cbn[concat].
  rewrite !count_occ_app, RootCert_count, !count_cons, LastCert_count; cbn[count_occ].
  rewrite <- weighted_outgoing; cbn[weighted].
  rewrite RootCert_length, weighted_app, CertBody_length; cbn[weighted]; rewrite LastCert_length.
  replace (2+n*2-1) with (1+n*2) by lia; replace (2+n*2-2) with (n*2) by lia.
  replace (n*2+2) with (2+n*2) by lia.
  pose proof (Nat.pow_nonzero 4 n ltac:(lia)) as Hpos.
  remember (4^n-1) as q; replace (4^n) with (1+q) in * by lia.
  replace ((1+q)*4-2) with (2+q*4) by lia.
  replace ((1+q)*2-1) with (1+q*2) by lia.
  unfold incoming in HB; cbn[Nat.add] in *; ring_simplify in HB; ring_simplify.
  cbn[length]; replace (n*2+2) with (2+n*2) by lia.
  replace (1+(1+n*2)) with (2+n*2) by lia; lia.
Qed.

Lemma CertBody_at N n : forall k, k<n ->
  nth (k*2) (CertBody N n) []=EvenCert N (k*2) k /\
  nth (1+k*2) (CertBody N n) []=OddCert N (1+k*2) k.
Proof.
  induction n as [|n IH]; intros k HK; [lia|].
  destruct (Nat.eq_dec k n) as [->|Hne]; cbn[CertBody].
  - rewrite !app_nth2 by (rewrite CertBody_length; lia).
    rewrite CertBody_length, Nat.sub_diag; replace (1+n*2-n*2) with 1 by lia; split; reflexivity.
  - rewrite !app_nth1 by (rewrite CertBody_length; lia); apply IH; lia.
Qed.

Import TM3 (PairExitRank, PairExitRank_root, PairExitRank_sink, PairExitRank_odd, PairExitRank_even).

Theorem Rows_forest n : LastForest (PairExitRank n) (Rows n).
Proof.
  intros i Hne; assert (HI : i<3+n*2).
  { destruct (Nat.lt_ge_cases i (length (Rows n))) as [HL|HL].
    - rewrite Rows_length in HL; exact HL.
    - rewrite nth_overflow in Hne by lia; contradiction. }
  destruct i as [|[|i]].
  - change (PairExitRank n (last (RootCert (2+n*2) n) 0)<PairExitRank n 0).
    unfold RootCert; rewrite Cycles_last by (discriminate || (pose proof (Nat.pow_nonzero 4 n ltac:(lia)); lia)).
    cbn[last]; replace (2+n*2-1) with (1+n*2) by lia.
    rewrite PairExitRank_odd, PairExitRank_root by lia; lia.
  - change (PairExitRank n (3+n*2)<PairExitRank n 1).
    rewrite PairExitRank_sink, (PairExitRank_odd (k:=0)) by lia; lia.
  - change (PairExitRank n (last (nth i (CertBody (2+n*2) n++[LastCert (2+n*2) n]) []) 0)
      <PairExitRank n (2+i)).
    destruct (Nat.eq_dec i (n*2)) as [->|Hlast].
    + rewrite app_nth2 by (rewrite CertBody_length; lia).
      rewrite CertBody_length, Nat.sub_diag; cbn[nth].
      unfold LastCert; rewrite last_suffix by discriminate; cbn[last]; rewrite PairExitRank_root.
      replace (2+n*2) with ((1+n)*2) by lia.
      rewrite PairExitRank_even, Nat.eqb_refl by lia; lia.
    + rewrite app_nth1 by (rewrite CertBody_length; lia).
      destruct (mod2 i) as [k E|k E]; subst i.
      * rewrite (proj1 (CertBody_at (2+n*2) (n:=n) (k:=k) ltac:(lia))).
        unfold EvenCert; rewrite last_suffix by discriminate; cbn[last].
        replace (2+n*2) with ((1+n)*2) by lia; replace (2+k*2) with ((1+k)*2) by lia.
        rewrite !PairExitRank_even, Nat.eqb_refl by lia.
        assert (E : (1+k=?1+n)=false) by (apply Nat.eqb_neq; lia); rewrite E; lia.
      * rewrite (proj2 (CertBody_at (2+n*2) (n:=n) (k:=k) ltac:(lia))).
        unfold OddCert; rewrite Cycles_last by (discriminate || (pose proof (Nat.pow_nonzero 4 k ltac:(lia)); lia)).
        cbn[last]; replace (2+(1+k*2)) with (1+(1+k)*2) by lia.
        rewrite !PairExitRank_odd by lia; lia.
Qed.

Lemma CertBody_budget N n : length (concat (CertBody N n))+n+4=4^n*4.
Proof.
  induction n; [reflexivity|].
  cbn[CertBody]; rewrite concat_app, length_app.
  cbn[concat]; rewrite !length_app, EvenCert_length, OddCert_length; cbn[length].
  pose proof (Nat.pow_nonzero 4 n ltac:(lia)); cbn[Nat.pow]; lia.
Qed.

Lemma Rows_budget n : length (concat (Rows n))=4^n*12-n-4.
Proof.
  pose proof (CertBody_budget (2+n*2) n) as H.
  pose proof (Nat.pow_nonzero 4 n ltac:(lia)).
  unfold Rows; cbn[concat]; rewrite !length_app, concat_app, length_app, RootCert_length.
  cbn[concat]; rewrite length_app, LastCert_length; cbn[length]; lia.
Qed.

Theorem stack_exit n : exists rows', StackWalk 0 (Rows n) (3+n*2) rows' (4^n*12-n-4) /\
  forall i, nth i rows' []=[].
Proof.
  pose proof (stack_certificate (Rows_balance n) (Rows_forest n)) as H.
  rewrite Rows_budget in H; exact H.
Qed.

Definition ExitMove N i a j := Move N i a j \/ (i=1 /\ a=1 /\ j=1+N).

Lemma RootCert_rules N n : Indexed (Move N 0) 0 (RootCert N n).
Proof.
  unfold RootCert; rewrite <- (app_nil_r (Cycles _ _)).
  change (Indexed (Move N 0) (0*length [0;N-1]) (Cycles [0;N-1] (4^n*2)++[])).
  apply Indexed_cycles; [|exact (fun _=>I)].
  intro a; cbn[length Indexed]; split; [apply Move_root_even|split; [apply Move_root_odd|exact I]].
Qed.

Lemma Rotor_three N i a : 1<i -> Indexed (Move N i) (a*4) [N;0;N].
Proof.
  intro HI; cbn[Indexed]; repeat split.
  - replace (a*4) with ((a*2)*2) by lia; apply Move_even; lia.
  - apply Move_one; exact HI.
  - replace (1+(1+a*4)) with ((1+a*2)*2) by lia; apply Move_even; lia.
Qed.

Lemma Rotor_rules N i a : 2<i -> Indexed (Move N i) (a*4) [N;0;N;i-2].
Proof.
  intro HI; change (Indexed (Move N i) (a*4) ([N;0;N]++[i-2])).
  rewrite Indexed_app; split; [apply Rotor_three; lia|].
  cbn[length Indexed]; split; [apply Move_three; exact HI|exact I].
Qed.

Lemma EvenCert_rules N i k : 2<i -> Indexed (Move N i) 0 (EvenCert N (i-2) k).
Proof.
  intro HI; unfold EvenCert; change (Indexed (Move N i) (0*length [N;0;N;i-2])
    (Cycles [N;0;N;i-2] (4^k-1)++[N;0;N])).
  apply Indexed_cycles; intro a; [apply Rotor_rules; exact HI|apply Rotor_three; lia].
Qed.

Lemma OddCert_rules N i k : 2<i -> Indexed (Move N i) 0 (OddCert N (i-2) k).
Proof.
  intro HI; unfold OddCert; rewrite <- (app_nil_r (Cycles _ _)).
  change (Indexed (Move N i) (0*length [N;0;N;i-2]) (Cycles [N;0;N;i-2] (4^k*2)++[])).
  apply Indexed_cycles; intro a; [apply Rotor_rules; exact HI|exact I].
Qed.

Lemma LastCert_rules n : Indexed (Move (2+n*2) (2+n*2)) 0 (LastCert (2+n*2) n).
Proof.
  destruct n.
  - change (Move 2 2 0 2 /\ Move 2 2 1 0 /\ True); repeat split;
      [exact (@Move_even 2 2 0 ltac:(lia))|exact (@Move_one 2 2 0 ltac:(lia))].
  - unfold LastCert; change (Indexed (Move (2+S n*2) (2+S n*2))
      (0*length [2+S n*2;0;2+S n*2;2+S n*2-2])
      (Cycles [2+S n*2;0;2+S n*2;2+S n*2-2] (4^S n-1)++[2+S n*2;0])).
    apply Indexed_cycles; intro a; [apply Rotor_rules; lia|].
    cbn[length Indexed]; split; [|split; [apply Move_one; lia|exact I]].
    replace (a*4) with ((a*2)*2) by lia; apply Move_even; lia.
Qed.

Lemma Rows_rules n : RowRules (ExitMove (2+n*2)) (Rows n) (repeat 0 (3+n*2)).
Proof.
  rewrite <- Rows_length; apply RowRules_initial; intro i.
  destruct (Nat.lt_ge_cases i (length (Rows n))) as [HI|HI];
    [rewrite Rows_length in HI|rewrite nth_overflow by lia; exact I].
  destruct i as [|[|i]].
  - change (Indexed (ExitMove (2+n*2) 0) 0 (RootCert (2+n*2) n)).
    eapply Indexed_mono; [intros; left; eassumption|apply RootCert_rules].
  - change (ExitMove (2+n*2) 1 0 (2+n*2) /\ ExitMove (2+n*2) 1 1 (3+n*2) /\ True).
    repeat split; [left; exact (@Move_even (2+n*2) 1 0 ltac:(lia))|right; auto].
  - change (Indexed (ExitMove (2+n*2) (2+i)) 0
      (nth i (CertBody (2+n*2) n++[LastCert (2+n*2) n]) [])).
    destruct (Nat.eq_dec i (n*2)) as [->|Hlast].
    + rewrite app_nth2 by (rewrite CertBody_length; lia).
      rewrite CertBody_length, Nat.sub_diag; cbn[nth].
      eapply Indexed_mono; [intros; left; eassumption|apply LastCert_rules].
    + rewrite app_nth1 by (rewrite CertBody_length; lia).
      destruct (mod2 i) as [k E|k E]; subst i.
      * rewrite (proj1 (CertBody_at (2+n*2) (n:=n) (k:=k) ltac:(lia))).
        destruct k as [|k].
        -- change (Indexed (ExitMove (2+n*2) 2) 0 [2+n*2;0;2+n*2]).
           eapply Indexed_mono; [intros; left; eassumption|exact (@Rotor_three (2+n*2) 2 0 ltac:(lia))].
        -- replace (S k*2) with (2+S k*2-2) at 2 by lia.
           eapply Indexed_mono; [intros; left; eassumption|apply EvenCert_rules; lia].
      * rewrite (proj2 (CertBody_at (2+n*2) (n:=n) (k:=k) ltac:(lia))).
        replace (1+k*2) with (2+(1+k*2)-2) at 2 by lia.
        eapply Indexed_mono; [intros; left; eassumption|apply OddCert_rules; lia].
Qed.

Lemma Rows_front n : nth 1 (Rows n) []=[2+n*2;3+n*2] /\ length (nth 2 (Rows n) [])<=3.
Proof.
  split; [reflexivity|].
  destruct n; [change (2<=3); lia|].
  change (length (nth 0 (CertBody (2+S n*2) (S n)++[LastCert (2+S n*2) (S n)]) [])<=3).
  rewrite app_nth1 by (rewrite CertBody_length; lia).
  pose proof (proj1 (CertBody_at (2+S n*2) (n:=S n) (k:=0) ltac:(lia))) as E.
  change (nth 0 (CertBody (2+S n*2) (S n)) []=[2+S n*2;0;2+S n*2]) in E.
  rewrite E; reflexivity.
Qed.

Lemma Rows_sink n rows xs : RowRules (ExitMove (2+n*2)) rows xs ->
  VisitBudget (Rows n) rows xs -> nth (3+n*2) rows []=[].
Proof. intros [EL HR] [ES HV]; apply nth_overflow; rewrite Rows_length in ES; lia. Qed.

Lemma Rows_safe n rows xs i : RowRules (ExitMove (2+n*2)) rows xs ->
  VisitBudget (Rows n) rows xs -> Balance rows i (3+n*2) -> i<>3+n*2 ->
  nth 1 xs 0<=1 /\ nth 2 xs 0<=3.
Proof.
  intros HR HV HF HI; split.
  - pose proof (Rows_sink HR HV) as HE.
    specialize (HF (3+n*2)); unfold outgoing in HF; rewrite HE, mark_self, mark_other in HF by assumption.
    cbn[length] in HF.
    destruct (incoming_witness rows (3+n*2) ltac:(lia)) as [j [HJ HJ']].
    destruct HR as [EL HR]; destruct HV as [ES HV].
    destruct (Indexed_in (HR j) HJ') as [a [HA [HD|[-> [-> _]]]]]; [|lia].
    unfold Move in HD; pose proof (TM2.Move_bound HD ltac:(rewrite Rows_length in ES; lia)); lia.
  - pose proof (VisitBudget_bound 2 HV) as HB.
    pose proof (proj2 (Rows_front n)); unfold outgoing in HB; lia.
Qed.

Lemma tick_available n xs u : length xs=2+n*2 -> nth 0 xs 0<=1 -> nth 1 xs 0<=3 ->
  exists ys v, Tick (repeat false (2+n*2)) false xs u ys v 0.
Proof.
  intros EL H1 H2; destruct xs as [|a [|b xs]]; cbn[length] in EL; try lia.
  change (a<=1) in H1; change (b<=3) in H2.
  destruct (Split_total false b) as [q [r HQ]]; assert (Hq : q<=1) by (inversion HQ; subst; lia).
  destruct (Scatter_total (repeat false (n*2)) xs ltac:(rewrite repeat_length; lia)) as [qs [s HS]].
  assert (HA : Half (repeat false (2+n*2)) 0 (a::b::xs) u (q::(qs++[u])) (a+r+s) 0).
  { apply (Half_make 0 u (qs:=q::qs) (r:=a+r+s)).
    replace (a+r+s) with (a+(r+s)) by lia; apply Scatter_cons; [apply Split_false_small; exact H1|].
    exact (Scatter_cons HQ HS). }
  destruct (@Half_front_total false (repeat false (1+n*2)) q (qs++[u]) (a+r+s) 1)
    as [ys [v HB]]; [pose proof (Scatter_length HS); rewrite repeat_length in *; rewrite length_app; cbn[length]; lia|
      apply Split_false_small; exact Hq|].
  exists ys,v; exact (Tick_make false HA HB).
Qed.

Lemma stack_ticks n i rows j rows' t : StackWalk i rows j rows' t ->
  forall xs u next v a, RowRules (ExitMove (2+n*2)) rows (u::xs) ->
  VisitBudget (Rows n) rows (u::xs) -> Balance rows i (3+n*2) ->
  Tick (repeat false (2+n*2)) false xs u next v 0 -> Bump i a (u::xs) (v::next) ->
  exists ys w, Ticks (repeat false (2+n*2)) false t xs u ys w /\ VisitBudget (Rows n) rows' (w::ys).
Proof.
  intro HW; induction HW as [i rows|i j k rows rows' rows'' t HP HW IH];
    intros xs u next v a HR HV HF HT HB.
  - exists xs,u; split; [constructor|assumption].
  - destruct (RowRules_pop HR HP HB) as [HD HR']; pose proof (VisitBudget_pop HV HP HB) as HV'.
    pose proof (Pop_balance HP HF) as HF'.
    destruct (Nat.eq_dec j (3+n*2)) as [HJ|HJ].
    + pose proof (Rows_sink HR' HV') as HE; rewrite <- HJ in HE.
      destruct (StackWalk_stuck HW HE) as [EJ [EN ER]]; subst.
      exists next,v; split; [eapply Ticks_cons; [exact HT|constructor]|exact HV'].
    + destruct (Rows_safe HR' HV' HF' HJ) as [H1 H2].
      destruct (Tick_length HT) as [EL EN]; rewrite repeat_length in EL.
      destruct (@tick_available n next v ltac:(lia) H1 H2) as [next' [v' HT']].
      destruct (Tick_route (N:=2+n*2) ltac:(lia) HT HT' HB) as [j' [a' [HD' HB']]].
      destruct HD as [HD|[_ [_ HE]]]; [|contradiction].
      pose proof (TM2.Move_functional HD HD') as ->.
      destruct (IH next v next' v' a' HR' HV' HF' HT' HB') as [ys [w [HX HY]]].
      exists ys,w; split; [eapply Ticks_cons; eassumption|assumption].
Qed.

Theorem canonical_exit n : exists xs u,
  Ticks (repeat false (2+n*2)) false (4^n*12-n-4) (repeat 0 (2+n*2)) 0 xs u /\
  u::xs=map (@length nat) (Rows n).
Proof.
  destruct (stack_exit n) as [rows' [HW HE]].
  destruct (@tick_available n (repeat 0 (2+n*2)) 0 ltac:(rewrite repeat_length; reflexivity)
    ltac:(rewrite nth_repeat; lia) ltac:(rewrite nth_repeat; lia)) as [next [v HT]].
  pose proof (initial_bump (N:=2+n*2) ltac:(lia) HT) as HB.
  pose proof (Rows_rules n) as HR.
  pose proof (VisitBudget_initial (Rows n)) as HV; rewrite Rows_length in HV.
  destruct (@stack_ticks n 0 (Rows n) (3+n*2) rows' (4^n*12-n-4)
    HW (repeat 0 (2+n*2)) 0 next v 0 HR HV (Rows_balance n) HT HB) as [xs [u [HX HY]]].
  exists xs,u; split; [exact HX|eapply VisitBudget_done; eassumption].
Qed.

Fixpoint PairValues b n := match n with
  | 0 => [] | S n => (b*4-1)::(b*8)::PairValues (b*4) n end.
Definition ExitBody n := 2::(PairValues 1 n++[4^n*4-2]).

Lemma PairValues_snoc n : forall b, PairValues b (n+1)=PairValues b n++
  [b*4^n*4-1;b*4^n*8].
Proof.
  induction n; intro b; cbn[PairValues Nat.add Nat.pow app].
  - rewrite Nat.mul_1_r; reflexivity.
  - rewrite IHn; f_equal; f_equal; f_equal; f_equal; f_equal; lia.
Qed.

Lemma CertBody_values N n : map (@length nat) (CertBody N n)=PairValues 1 n.
Proof.
  induction n; [reflexivity|].
  cbn[CertBody]; rewrite map_app, IHn; cbn[map]; rewrite EvenCert_length, OddCert_length.
  replace (S n) with (n+1) by lia; rewrite PairValues_snoc, !Nat.mul_1_l; reflexivity.
Qed.

Lemma Rows_values n : map (@length nat) (Rows n)=(4^n*4)::ExitBody n.
Proof.
  unfold Rows, ExitBody; cbn[map]; rewrite RootCert_length, map_app, CertBody_values.
  cbn[map length]; rewrite LastCert_length; reflexivity.
Qed.

Theorem canonical_endpoint n :
  Ticks (repeat false (2+n*2)) false (4^n*12-n-4) (repeat 0 (2+n*2)) 0 (ExitBody n) (4^n*4).
Proof.
  destruct (canonical_exit n) as [xs [u [HT HE]]].
  rewrite Rows_values in HE; injection HE as -> ->; exact HT.
Qed.

Lemma GWord_exit n : forall b u, 0<b ->
  GWord (b*2) (b*2) (PairValues b n++[b*4^n*4-2]) u=
  Doubles (b*8) n++Alt false (b*4^n*8-1)++Alt false (b*4^n*8-1+u*2).
Proof.
  induction n; intros b u Hb.
  - cbn[PairValues Nat.pow app Doubles]; rewrite !Nat.mul_1_r; cbn[GWord].
    replace (b*4-2) with ((b*2-1)*2) by lia.
    rewrite !odd_0; cbn[xorb]; flia.
  - replace (b*4^S n) with ((b*4)*4^n) by (cbn[Nat.pow]; lia).
    cbn[PairValues app GWord].
    replace (b*4-1) with (1+(b*2-1)*2) by lia.
    replace (b*8) with ((b*4)*2) by lia.
    replace (b*2*2*2) with ((b*4)*2) by lia.
    rewrite !odd_0, odd_1; cbn[xorb].
    rewrite IHn by lia; cbn[Doubles].
    rewrite <- !app_assoc; flia.
Qed.

Lemma ExitBody_word n : Word (ExitBody n) (4^n*4)=QWord n.
Proof.
  unfold Word, ExitBody, QWord.
  change (Alt true 4++GWord 2 2 (PairValues 1 n++[4^n*4-2]) (4^n*4)=
    Alt true 4++Doubles 8 n++Alt false (4^n*8-1)++Alt false (4^n*16-1)).
  pose proof (@GWord_exit n 1 (4^n*4) ltac:(lia)) as H; rewrite !Nat.mul_1_l in H.
  rewrite H; pose proof (Nat.pow_nonzero 4 n ltac:(lia)); flia.
Qed.

Theorem canonical_word n : Lives Edge retire ((4^n*12-n-4)*2)
  (Word (repeat 0 (2+n*2)) 0) [0;0] (QWord n) [0;0].
Proof. rewrite <- ExitBody_word; apply (Ticks_lives (2+n*2)), canonical_endpoint. Qed.

Theorem seed_exit n xs u : Seed n xs u ->
  Ticks (repeat false (12+n*2)) false (4^(5+n)*12-(5+n)-4-(6+n))
    xs u (ExitBody (5+n)) (4^(5+n)*4).
Proof.
  intro HS; destruct (Seed_absorbs HS) as [t [mid [root [Ht [HR [HP HL]]]]]].
  pose proof (canonical_endpoint (5+n)) as HC.
  replace (2+(5+n)*2) with (12+n*2) in HC by lia.
  pose proof (Box_budget n) as HB.
  replace (2^(10+n*2)) with (4^(5+n)) in HB by (rewrite <- TM3.power4; f_equal; lia).
  pose proof (CertBody_budget (12+n*2) (5+n)) as Hlength.
  assert (HT : t+(6+n)<=4^(5+n)*12-(5+n)-4) by nia.
  eapply Ticks_suffix with (k:=t+(6+n)) in HC; [|exact HT|exact HP].
  replace (4^(5+n)*12-(5+n)-4-(6+n)) with
    (t+(4^(5+n)*12-(5+n)-4-(t+(6+n)))) by lia.
  eapply Ticks_app; eassumption.
Qed.

Theorem R_paired_exit n : Lives Edge retire
  ((12+n*2)+(4^(5+n)*12-(5+n)-4-(6+n))*2)
  (RWord (10+n*2)) [1;0] (QWord (5+n)) [0;0].
Proof.
  destruct (R_to_Seed n) as [xs [u [HS HL]]].
  eapply Lives_app; [exact HL|].
  rewrite <- ExitBody_word; apply (Ticks_lives (12+n*2)), seed_exit; exact HS.
Qed.

Theorem Q_round n : Lives Edge retire (4^(5+n)*24-4)
  (QWord (4+n)) [0;0] (QWord (5+n)) [0;0].
Proof.
  pose proof (Lives_app (Q_to_R (4+n))) as H.
  assert (HL : Lives Edge retire ((12+n*2)+(4^(5+n)*12-(5+n)-4-(6+n))*2)
    (RWord (2+(4+n)*2)) [1;0] (QWord (5+n)) [0;0]).
  { applys_eq (R_paired_exit n); flia. }
  pose proof (CertBody_budget (12+n*2) (5+n)) as HB.
  pose proof (Nat.pow_nonzero 4 (5+n) ltac:(lia)).
  applys_eq (H _ _ _ HL); flia.
Qed.

Lemma Q_progress n : exists t, Lives Edge retire (1+t) (QWord (4+n)) [0;0] (QWord (5+n)) [0;0].
Proof.
  exists (4^(5+n)*24-5); pose proof (Nat.pow_nonzero 4 (5+n) ltac:(lia)).
  applys_eq (Q_round n); flia.
Qed.

Lemma Q_suffix_infinite : forall n t w kids,
  Lives Edge retire t w kids (QWord (4+n)) [0;0] -> InfiniteLife Edge retire w kids.
Proof.
  cofix IH; intros n t w kids H; destruct t.
  - inversion H; subst; destruct (Q_progress n) as [k HT].
    replace (5+n) with (4+(1+n)) in HT by lia.
    inversion HT; subst; econstructor; [eassumption|eapply (IH (1+n) k); eassumption].
  - inversion H; subst; econstructor; [eassumption|eapply (IH n t); eassumption].
Qed.

Theorem Q_infinite n : InfiniteLife Edge retire (QWord (4+n)) [0;0].
Proof. eapply (@Q_suffix_infinite n 0); constructor. Qed.

Lemma Conserves_functional N t xs u ys v : Conserves N t xs u ys v ->
  forall zs w, Conserves N t xs u zs w -> ys=zs /\ v=w.
Proof.
  intro H; induction H; intros ps z HC; inversion HC; subst; [auto|].
  match goal with HH : Half _ _ _ _ _ _ _ |- _ =>
    destruct (Half_functional H HH) as [E [F _]] end.
  subst; eauto.
Qed.

Fixpoint conserve_c N t c := match t with
  | 0 => Some c
  | S t => match CounterEval.half_c (repeat false N) 0 c with
    | Some d => conserve_c N t d | None => None end end.

Lemma conserve_c_spec N t : forall xs u ys v,
  conserve_c N t (xs,u)=Some (ys,v) -> Conserves N t xs u ys v.
Proof.
  induction t; intros xs u ys v H; cbn[conserve_c] in H.
  - inversion H; constructor.
  - destruct (CounterEval.half_c (repeat false N) 0 (xs,u)) as [[zs w]|] eqn:HH;
      [|discriminate].
    econstructor; [exact (CounterEval.half_c_spec HH)|eapply IHt; exact H].
Qed.

Definition small_seed_check n :=
  match conserve_c (2+n*2) (1+n*2) (repeat 0 (2+n*2),1+n) with
  | Some (xs,u) => CounterEval.check (repeat false (2+n*2)) false
      (4^n*12-n-4-(1+n)) xs u (ExitBody n) (4^n*4)
  | None => false end.

Lemma small_seed_checked : forallb small_seed_check [1;2;3;4]=true.
Proof. vm_compute; reflexivity. Qed.

Lemma small_seed_ticks n xs u : 1<=n<=4 ->
  Conserves (2+n*2) (1+n*2) (repeat 0 (2+n*2)) (1+n) xs u ->
  Ticks (repeat false (2+n*2)) false (4^n*12-n-4-(1+n))
    xs u (ExitBody n) (4^n*4).
Proof.
  intros HN HC.
  pose proof (proj1 (forallb_forall small_seed_check [1;2;3;4])
    small_seed_checked n ltac:(cbn; lia)) as HT.
  unfold small_seed_check in HT.
  destruct (conserve_c (2+n*2) (1+n*2) (repeat 0 (2+n*2),1+n)) as [[ys v]|] eqn:HE;
    [|discriminate].
  apply conserve_c_spec in HE.
  destruct (Conserves_functional HC HE) as [-> ->].
  apply CounterEval.check_spec; exact HT.
Qed.

Lemma small_R_exit n : 1<=n<=4 -> Lives Edge retire
  ((2+n*2)+(4^n*12-n-4-(1+n))*2)
  (RWord (n*2)) [1;0] (QWord n) [0;0].
Proof.
  intro HN; destruct (R_to_counter n) as [xs [u [HC HL]]].
  eapply Lives_app; [exact HL|].
  rewrite <- ExitBody_word; apply (Ticks_lives (2+n*2)), small_seed_ticks; assumption.
Qed.

Lemma small_Q_round n : n<=3 -> Lives Edge retire (4^(1+n)*24-4)
  (QWord n) [0;0] (QWord (1+n)) [0;0].
Proof.
  intro HN; pose proof (@small_R_exit (1+n) ltac:(lia)) as HR.
  replace ((1+n)*2) with (2+n*2) in HR by lia.
  pose proof (Lives_app (Q_to_R n) HR) as H.
  pose proof (CertBody_budget (2+(1+n)*2) (1+n)) as HB.
  pose proof (Nat.pow_nonzero 4 (1+n) ltac:(lia)).
  applys_eq H; flia.
Qed.

Lemma initial_counter : Lives Edge retire 5 [] [3;0;0] (Word [0;0] 0) [0;0].
Proof.
  do 2 (eapply Lives_cons;
    [eapply Life_internal; [discriminate|
      repeat first [apply Pass_nil | apply Pass_P | apply Pass_I; [lia|]]]|]).
  eapply Lives_cons;
    [eapply Life_terminal with (k:=1) (b:=3); [exact (Edge_odd 0)|
      repeat first [apply Pass_nil | apply Pass_P | apply Pass_I; [lia|]]]|].
  eapply Lives_cons;
    [eapply Life_internal; [discriminate|
      repeat first [apply Pass_nil | apply Pass_P | apply Pass_I; [lia|]]]|].
  eapply Lives_cons;
    [eapply Life_terminal with (k:=0) (b:=1); [exact (Edge_even 0)|
      repeat first [apply Pass_nil | apply Pass_P | apply Pass_I; [lia|]]]|].
  constructor.
Qed.

Lemma initial_Q2 : Lives Edge retire 21 [] [3;0;0] (QWord 0) [0;0].
Proof. exact (Lives_app initial_counter (canonical_word 0)). Qed.

Lemma initial_Q_prefix n : n<=4 ->
  Lives Edge retire (4^n*32-32-n*4) (QWord 0) [0;0] (QWord n) [0;0].
Proof.
  induction n; intro HN.
  - constructor.
  - pose proof (Lives_app (IHn ltac:(lia)) (@small_Q_round n ltac:(lia))) as H.
    pose proof (CertBody_budget (2+n*2) n).
    cbn[Nat.pow Nat.add] in H |- *; applys_eq H; flia.
Qed.

Lemma initial_Q10 : Lives Edge retire 8165 [] [3;0;0] (QWord 4) [0;0].
Proof. exact (Lives_app initial_Q2 (@initial_Q_prefix 4 ltac:(lia))). Qed.

Lemma initial_infinite : InfiniteLife Edge retire [] [3;0;0].
Proof. eapply Lives_infinite; [apply initial_Q10|exact (Q_infinite 0)]. Qed.

Theorem nonhalt : ~halts tm c0.
Proof. apply nonhalt_from_lives, initial_infinite. Qed.


End TM5.

(* Skelet17 and the shared physical-machine interface. *)

Open Scope sym.


Module Skelet17.
Definition tm := Eval compute in (TM_from_str "1RB---_0LC1RE_0LD1LC_1RA1LB_0RB0RA_------").
Notation "c -->* c'" := (c -[tm]->* c') (at level 40).
Notation "c -->+ c'" := (c -[tm]->+ c') (at level 40).
Fixpoint LC (xs:list nat) :=
  match xs with [] => 0inf | a::xs => LC xs <* <[1;0]^^a <* <[1] end.
Definition S1 xs n := LC xs {{B}}> [1;0]^^n *> 0inf.
Definition QL (p:bool) := if p then B else C.

Inductive Edge : nat -> nat -> list nat -> Prop :=
| Edge_even a : Edge (a*2) (1+a*2) [0;0]%nat
| Edge_odd a : Edge (1+a*2) (2+a*2) [1;0;0]%nat.
Notation LInc := (Flow_LInc Edge).
Notation Run := (Flow_Run Edge).
Definition retire a := Nat.odd a::Alt (Nat.odd a) a.

Lemma Edge_size a b kids : Edge a b kids -> length kids<=3.
Proof. intro H; destruct H; cbn; lia. Qed.
Lemma Edge_functional a b kids c kids' :
  Edge a b kids -> Edge a c kids' -> b=c /\ kids=kids'.
Proof. intros H H'; destruct H; inversion H'; subst; split; try reflexivity; f_equal; lia. Qed.

Lemma LInc_spec p xs ys : LInc p xs ys ->
  forall r, LC xs <{{QL p}} [1;0] *> r -->* LC ys {{B}}> r.
Proof.
  intro H; induction H; intros r.
  - cbn[LC QL]; es.
  - destruct (mod2 a) as [k E|k E]; subst a.
    + rewrite odd_0 in IHLInc; destruct k as [|k]; [lia|].
      replace (S k*2) with (2+k*2) by lia.
      cbn[LC QL] in *; es; er; follow IHLInc; es.
    + rewrite odd_1 in IHLInc; cbn[LC QL] in *.
      es; er; follow IHLInc; es.
  - destruct H; cbn[LC QL]; es.
Qed.

Lemma Inc_right n xs ys : LInc (negb (Nat.odd n)) xs ys ->
  S1 xs (1+n) -->* S1 ys n.
Proof.
  intro H; destruct (mod2 n) as [a E|a E]; subst n.
  - rewrite odd_0 in H; eapply LInc_spec in H; es; er; follow H; finish.
  - rewrite odd_1 in H; eapply LInc_spec in H; es; er; follow H; finish.
Qed.

Lemma Inc_zero a xs ys : LInc (Nat.odd a) xs ys ->
  S1 (a::xs) 0 -->+ S1 ys a.
Proof.
  intro H; destruct (mod2 a) as [k E|k E]; subst a.
  - rewrite odd_0 in H; eapply LInc_spec in H; unfold S1; cbn[LC].
    es; er; follow H; finish.
  - rewrite odd_1 in H; eapply LInc_spec in H; unfold S1; cbn[LC].
    es; er; follow H; finish.
Qed.

Lemma init : c0 -->* S1 [2;1]%nat 0.
Proof. unfold S1; esx. Qed.

Lemma Run_right n xs ys : Run (Alt (Nat.odd n) n) xs ys -> S1 xs n -->* S1 ys 0.
Proof.
  revert xs; induction n; intros xs H.
  - inversion H; subst; apply evstep_refl.
  - cbn[Alt] in H; rewrite odd_S, negb_involutive in H.
    inversion H as [|p w source cut target HL HR]; subst.
    follow (Inc_right n HL); apply IHn; assumption.
Qed.

Lemma Macro_spec xs ys : Flow_Macro Edge retire xs ys -> S1 xs 0 -->+ S1 ys 0.
Proof.
  intro H; destruct H; cbn[retire] in H.
  inversion H as [|p w source cut target HL HR]; subst.
  follow10 (Inc_zero a HL); apply Run_right; assumption.
Qed.

Lemma InfiniteMacro_nonhalt xs :
  Flow_InfiniteMacro Edge retire xs -> ~halts tm (S1 xs 0).
Proof.
  intro HI; eapply progress_nonhalt with
    (P:=fun c => exists ys, Flow_InfiniteMacro Edge retire ys /\ c=S1 ys 0).
  - intros c [ys [H ->]]; destruct H as [ys zs HM HI'].
    exists (S1 zs 0); split; [exists zs; auto|apply Macro_spec; assumption].
  - exists xs; auto.
Qed.

Lemma nonhalt_from_lives :
  InfiniteLife Edge retire [] [2;1]%nat -> ~halts tm c0.
Proof.
  intro H; eapply multistep_nonhalt; [apply init|].
  apply InfiniteMacro_nonhalt; eapply (InfiniteLife_sound_bounded Edge_functional Edge_size);
    eauto using Edge_functional, Run_nil.
Qed.

Close Scope sym.
Definition cut (w:list bool) := removelast w.
Definition LastI (w:list bool) := exists u, w=u++[false].

Lemma cut_snoc w p : cut (w++[p])=w.
Proof. unfold cut; apply removelast_last. Qed.

Lemma LastI_app p w : LastI w -> LastI (p++w).
Proof. intros [u ->]; exists (p++u); apply app_assoc. Qed.

Lemma LastI_suffix p : forall w, w<>[] -> LastI (p++w) -> LastI w.
Proof.
  induction p as [|a p IH]; intros w HN [u E]; [exists u; exact E|].
  destruct u as [|b u].
  - cbn[app] in E; injection E as _ HE.
    apply app_eq_nil in HE; tauto.
  - cbn[app] in E; injection E as _ E; apply IH; [exact HN|exists u; exact E].
Qed.

Lemma retire_complete a : retire a++[false]=Nat.odd a::TM5.retire a.
Proof.
  unfold retire, TM5.retire; cbn[app]; f_equal.
  replace (1+a) with (a+1) by lia; rewrite Alt_snoc, xorb_nilpotent; reflexivity.
Qed.

Lemma Pass_cut w a b o : Pass (w++[false]) a b o -> exists q,
  Pass w a b q /\ (q++retire b)++[false]=o++TM5.retire b.
Proof.
  intro H; destruct (Pass_app w [false] H) as [c [q [z [HP [HT ->]]]]].
  inversion HT; subst.
  match goal with H : Pass [] _ _ _ |- _ => inversion H; subst end.
  exists q; split; [assumption|].
  rewrite <- !app_assoc, retire_complete; reflexivity.
Qed.

Lemma Life_cut_with E w xs v ys : Life E TM5.retire w xs v ys ->
  LastI w -> In false (cut w) -> (forall a b, E a b ys -> Edge a b ys) ->
  Life Edge retire (cut w) xs (cut v) ys.
Proof.
  intro H; destruct H as [w a xs b o Hne HP|k u a b c o kids HE HP]; intros HW HI HY.
  - destruct HW as [z ->]; rewrite cut_snoc in *.
    destruct (Pass_cut z HP) as [q [HQ EQ]]; rewrite <- EQ, cut_snoc.
    apply Life_internal; assumption.
  - assert (HU : u<>[]).
    { intro EN; subst u; change (In false (cut (repeat true k++[false]))) in HI.
      rewrite cut_snoc in HI; apply repeat_spec in HI; discriminate. }
    assert (HU' : LastI u).
    { eapply (LastI_suffix (repeat true k++[false])); [exact HU|].
      rewrite <- app_assoc; exact HW. }
    destruct HU' as [z ->]; destruct (Pass_cut z HP) as [q [HQ EQ]].
    replace (repeat true k++false::(z++[false])) with
      ((repeat true k++false::z)++[false]) by (rewrite <- app_assoc; reflexivity).
    rewrite cut_snoc, <- EQ, cut_snoc.
    eapply Life_terminal with (b:=b); [apply HY; exact HE|exact HQ].
Qed.

Lemma Life_cut w xs v ys : Life TM5.Edge TM5.retire w xs v ys ->
  LastI w -> In false (cut w) -> ys<>[1;0] ->
  Life Edge retire (cut w) xs (cut v) ys.
Proof.
  intros H HW HI HY; eapply Life_cut_with; [exact H|exact HW|exact HI|].
  intros a b HE; destruct HE; [constructor|contradiction HY; reflexivity].
Qed.

Lemma Alt_counter_last b x u : LastI (Alt (xorb (Nat.odd b) (Nat.odd x)) (1+b+x+u*2)).
Proof.
  exists (Alt (xorb (Nat.odd b) (Nat.odd x)) (b+x+u*2)).
  replace (1+b+x+u*2) with (b+x+u*2+1) by lia.
  rewrite Alt_snoc, !Nat.odd_add, odd_0, xorb_false_r, xorb_nilpotent; reflexivity.
Qed.

Lemma GWord_last xs : forall b x u, LastI (TM5.GWord b x xs u).
Proof.
  induction xs; intros; cbn[TM5.GWord]; [apply Alt_counter_last|apply LastI_app, IHxs].
Qed.

Lemma Word_last xs u : LastI (TM5.Word xs u).
Proof. apply GWord_last. Qed.

Lemma Word_has_I x xs u : In false (cut (TM5.Word (x::xs) u)).
Proof.
  destruct (GWord_last xs 2 x u) as [z E].
  change (In false (cut (true::false::(Alt true x++TM5.GWord 2 x xs u)))).
  rewrite E, app_assoc.
  change (In false (cut ((true::false::(Alt true x++z))++[false]))).
  rewrite cut_snoc; cbn; auto.
Qed.

Lemma cut_cons p w : LastI w -> cut (p::w)=p::cut w.
Proof.
  intros [z ->]; change (cut ((p::z)++[false])=p::cut (z++[false])); rewrite !cut_snoc; reflexivity.
Qed.

Definition Word xs u := cut (TM5.Word xs u).
Definition QWord n := cut (TM5.QWord n).

Lemma internal_column xs qs r u : Scatter (repeat false (length xs)) xs (0::qs) r ->
  Life Edge retire (Word xs u) [0;0] (cut (true::TM5.Word (qs++[u]) r)) [0].
Proof.
  intro H; destruct xs as [|x xs]; [inversion H|].
  apply Life_cut; [apply TM5.internal_column; exact H|apply Word_last|apply Word_has_I|discriminate].
Qed.

Lemma parent_column xs qs r u : Scatter (repeat false (length xs)) xs (0::qs) r ->
  Life Edge retire (cut (true::TM5.Word xs u)) [0] (Word (qs++[u]) (1+r)) [0;0].
Proof.
  intro H; destruct xs as [|x xs]; [inversion H|].
  apply Life_cut; [apply TM5.parent_column; exact H|apply (LastI_app [true]), Word_last| |discriminate].
  rewrite cut_cons by apply Word_last; right; apply Word_has_I.
Qed.

Lemma Tick_lives N xs u ys v : Tick (repeat false N) false xs u ys v 0 ->
  Lives Edge retire 2 (Word xs u) [0;0] (Word ys v) [0;0].
Proof.
  intro H; inversion H as [xs0 u0 mid root ys0 v0 a b H1 H2]; subst.
  assert (a=0 /\ b=0) as [-> ->] by lia.
  destruct (Half_length H1) as [EL EM]; rewrite repeat_length in EL.
  destruct (Half_length H2) as [EL' _]; rewrite repeat_length in EL'.
  rewrite <- EL in H1; rewrite <- EL' in H2; clear EL EL' EM.
  inversion H1; subst; inversion H2; subst.
  eapply Lives_cons; [apply internal_column; eassumption|].
  eapply Lives_cons; [apply parent_column; eassumption|constructor].
Qed.

Lemma Ticks_lives N t xs u ys v : Ticks (repeat false N) false t xs u ys v ->
  Lives Edge retire (t*2) (Word xs u) [0;0] (Word ys v) [0;0].
Proof.
  intro H; induction H; [constructor|].
  replace ((1+n)*2) with (2+n*2) by lia.
  eapply Lives_app; [apply (Tick_lives N); eassumption|assumption].
Qed.

Theorem canonical_word n : Lives Edge retire ((4^n*12-n-4)*2)
  (Word (repeat 0 (2+n*2)) 0) [0;0] (QWord n) [0;0].
Proof.
  unfold QWord; rewrite <- TM5.ExitBody_word.
  apply (Ticks_lives (2+n*2)), TM5.canonical_endpoint.
Qed.

Lemma initial_counter : Lives Edge retire 5 [] [2;1] (Word [0;0] 0) [0;0].
Proof.
  eapply Lives_cons; [eapply Life_internal; [discriminate|apply Pass_nil]|].
  eapply Lives_cons;
    [eapply Life_terminal with (k:=0) (b:=2); [exact (Edge_odd 0)|
      repeat first [apply Pass_nil | apply Pass_P | apply Pass_I; [lia|]]]|].
  do 2 (eapply Lives_cons;
    [eapply Life_internal; [discriminate|
      repeat first [apply Pass_nil | apply Pass_P | apply Pass_I; [lia|]]]|]).
  eapply Lives_cons;
    [eapply Life_terminal with (k:=0) (b:=1); [exact (Edge_even 0)|
      repeat first [apply Pass_nil | apply Pass_P | apply Pass_I; [lia|]]]|].
  constructor.
Qed.

Theorem initial_Q2 : Lives Edge retire 21 [] [2;1] (QWord 0) [0;0].
Proof. exact (Lives_app initial_counter (canonical_word 0)). Qed.

Lemma DWord_last r : forall b xs u, LastI (TM5.DWord b r xs u).
Proof.
  induction r; intros; cbn[TM5.DWord]; [apply GWord_last|apply LastI_app, IHr].
Qed.

Lemma prefix_has_I p w : LastI w -> In false (cut (p::Alt p 2++w)).
Proof.
  intros [z ->]; destruct p.
  - change (In false (cut ((true::true::false::z)++[false]))); rewrite cut_snoc; cbn; auto.
  - change (In false (cut ((false::false::true::z)++[false]))); rewrite cut_snoc; cbn; auto.
Qed.

Lemma DWord_has_I r xs u : In false (cut (Nat.odd r::TM5.DWord 2 r xs u)).
Proof.
  destruct r.
  - rewrite cut_cons by apply DWord_last; left; reflexivity.
  - cbn[TM5.DWord]; apply prefix_has_I, DWord_last.
Qed.

Lemma DWord_zero_step r N : Life Edge retire
  (cut (Nat.odd (1+r)::TM5.DWord 2 (1+r) (repeat 0 N) 0))
    (if Nat.odd (1+r) then [0;0] else [0])
  (cut (Nat.odd r::TM5.DWord 2 r (repeat 0 (1+N)) 0))
    (if Nat.odd r then [0;0] else [0]).
Proof.
  pose proof (Scatter_zeros (repeat false N)) as H; rewrite repeat_length in H.
  assert (HS : Scatter (repeat false (length (repeat 0 N))) (repeat 0 N) (repeat 0 N) 0)
    by (rewrite repeat_length; exact H).
  pose proof (TM5.DWord_life r 0 HS) as HL.
  rewrite zeros_snoc in HL; replace (N+1) with (1+N) in HL by lia.
  apply Life_cut; [exact HL|apply (LastI_app [_]), DWord_last|apply DWord_has_I|].
  destruct (Nat.odd r); discriminate.
Qed.

Theorem DWord_zeros r : forall N, Lives Edge retire (1+r)
  (cut (Nat.odd r::TM5.DWord 2 r (repeat 0 N) 0))
    (if Nat.odd r then [0;0] else [0])
  (Word (repeat 0 (1+r+N)) 0) [0;0].
Proof.
  induction r; intro N.
  - pose proof (Scatter_zeros (repeat false N)) as H; rewrite repeat_length in H.
    assert (HS : Scatter (repeat false (length (repeat 0 N))) (repeat 0 N) (repeat 0 N) 0)
      by (rewrite repeat_length; exact H).
    destruct (TM5.DWord_zero_H 0 HS) as [A [o [HP HE]]].
    rewrite zeros_snoc in HE; replace (N+1) with (1+N) in HE by lia.
    pose proof (TM5.H_parent HP) as HL; rewrite HE in HL.
    eapply Lives_cons; [apply Life_cut; [exact HL|apply (LastI_app [_]), DWord_last|
      apply DWord_has_I|discriminate]|constructor].
  - eapply Lives_cons; [apply DWord_zero_step|].
    applys_eq (IHr (1+N)); flia.
Qed.

Lemma retire_last a : LastI (TM5.retire a).
Proof.
  exists (Alt (Nat.odd a) a); unfold TM5.retire.
  replace (1+a) with (a+1) by lia; rewrite Alt_snoc, xorb_nilpotent; reflexivity.
Qed.

Lemma Life_last E w xs v ys : Life E TM5.retire w xs v ys -> LastI v.
Proof. intro H; destruct H; apply LastI_app, retire_last. Qed.

Definition FrontA n := Doubles 2 (1+n)++Alt false (4^n*8-1)++Alt false (4^n*16-1).
Definition FrontB n := true::Alt true 2++Doubles 4 (1+n)++Alt false (4^n*16-1).
Definition FrontC n := false::Doubles 2 (2+n).
Definition FrontD n := true::TM5.DWord 2 (3+n*2) [] 0.

Lemma Q_cut_step n : Life Edge retire (QWord n) [0;0] (cut (TM5.QInternal n)) [0].
Proof.
  apply Life_cut; [apply TM5.Q_internal| | |discriminate].
  - rewrite <- TM5.ExitBody_word; apply Word_last.
  - unfold TM5.QWord; cbn[cut removelast Alt app In]; auto.
Qed.

Lemma Q_to_A n : Life Edge TM5.retire (TM5.QInternal n) [0] (FrontA n) [1;0;0].
Proof.
  pose proof (Nat.pow_nonzero 4 n ltac:(lia)) as Hpos.
  assert (HP : Pass (Doubles 4 (1+n)++Alt false (4^n*16-3)) 2 (4^n*16-2)
    (Doubles 2 (1+n)++Alt false (4^n*8-1))).
  { eapply Pass_cat with (b:=4^n*8).
    - applys_eq (@Pass_Doubles (1+n) 2 2 ltac:(lia) ltac:(lia) eq_refl eq_refl);
        cbn[Nat.pow Nat.add]; flia.
    - pose proof (@Pass_alt_odd_I (4^n*8-2) (4^n*8) ltac:(lia)) as H.
      replace (4^n*8) with ((4^n*4)*2) in H by lia; rewrite odd_0 in H; applys_eq H; flia. }
  pose proof (@Life_terminal Edge TM5.retire 1 _ 0 2 _ _ [1;0;0] (Edge_odd 0) HP) as HL.
  unfold TM5.retire in HL; replace (4^n*16-2) with ((4^n*8-1)*2) in HL by lia.
  rewrite odd_0, <- app_assoc in HL; unfold FrontA, TM5.QInternal; applys_eq HL; flia.
Qed.

Lemma Pass_Doubles_head n : Pass (Doubles 2 (1+n)) 1 (4^n*4)
  (true::Alt true 2++Doubles 4 n).
Proof.
  change (Pass ((Alt false 2++Alt true 4)++Doubles 8 n) 1 (4^n*4)
    ((true::Alt true 2)++Doubles 4 n)).
  eapply Pass_cat with (b:=4).
  - repeat first [apply Pass_nil | apply Pass_P | apply Pass_I; [lia|]].
  - applys_eq (@Pass_Doubles n 4 4 ltac:(lia) ltac:(lia) eq_refl eq_refl); flia.
Qed.

Lemma A_to_B n : Life Edge TM5.retire (FrontA n) [1;0;0] (FrontB n) [0;0].
Proof.
  pose proof (Nat.pow_nonzero 4 n ltac:(lia)) as Hpos.
  assert (HP : Pass (FrontA n) 1 (4^n*16-2)
    (true::Alt true 2++Doubles 4 (1+n))).
  { unfold FrontA; replace (1+n) with (n+1) at 2 by lia.
    rewrite Doubles_snoc.
    replace (4*4^n) with (4^n*4) by lia.
    replace (4^n*4*2) with (4^n*8) by lia.
    pose proof (Pass_Doubles_head n) as HH.
    assert (H1 : Pass (Alt false (4^n*8-1)) (4^n*4) (4^n*8-1) (Alt false (4^n*4))).
    { pose proof (@Pass_alt_odd_I (4^n*4-1) (4^n*4) ltac:(lia)) as H.
      replace (4^n*4) with ((4^n*2)*2) in H by lia; rewrite odd_0 in H; applys_eq H; flia. }
    assert (H2 : Pass (Alt false (4^n*16-1)) (4^n*8-1) (4^n*16-2) (Alt true (4^n*8))).
    { pose proof (@Pass_alt_odd_I (4^n*8-1) (4^n*8-1) ltac:(lia)) as H.
      replace (4^n*8-1) with (1+(4^n*4-1)*2) in H by lia; rewrite odd_1 in H; applys_eq H; flia. }
    exact (Pass_cat HH (Pass_cat H1 H2)). }
  pose proof (@Life_internal Edge TM5.retire _ 1 [0;0] _ _ ltac:(discriminate) HP) as HL.
  unfold TM5.retire in HL; replace (4^n*16-2) with ((4^n*8-1)*2) in HL by lia.
  rewrite odd_0 in HL; unfold FrontB; cbn[app Alt] in HL |- *; applys_eq HL; flia.
Qed.

Lemma B_to_C n : Life Edge TM5.retire (FrontB n) [0;0] (FrontC n) [0].
Proof.
  pose proof (Nat.pow_nonzero 4 n ltac:(lia)) as Hpos.
  assert (HP : Pass (FrontB n) 0 (4^n*16-1)
    (false::Doubles 2 (1+n)++Alt false (4^n*8))).
  { unfold FrontB; apply Pass_P.
    change (Pass (Alt true 2++(Doubles 4 (1+n)++Alt false (4^n*16-1))) 1 (4^n*16-1)
      ([false]++(Doubles 2 (1+n)++Alt false (4^n*8)))).
    eapply Pass_cat with (b:=2); [repeat first [apply Pass_nil|apply Pass_P|apply Pass_I; [lia|]]|].
    eapply Pass_cat with (b:=4^n*8).
    - applys_eq (@Pass_Doubles (1+n) 2 2 ltac:(lia) ltac:(lia) eq_refl eq_refl);
        cbn[Nat.pow Nat.add]; flia.
    - pose proof (@Pass_alt_odd_I (4^n*8-1) (4^n*8) ltac:(lia)) as H.
      replace (4^n*8) with ((4^n*4)*2) in H by lia; rewrite odd_0 in H; applys_eq H; flia. }
  pose proof (@Life_internal Edge TM5.retire _ 0 [0] _ _ ltac:(discriminate) HP) as HL.
  unfold TM5.retire in HL; replace (4^n*16-1) with (1+(4^n*8-1)*2) in HL by lia.
  rewrite odd_1 in HL; cbn[app] in HL; rewrite <- !app_assoc in HL.
  unfold FrontC; replace (2+n) with ((1+n)+1) by lia; rewrite Doubles_snoc.
  applys_eq HL; cbn[Nat.pow Nat.add]; flia.
Qed.

Lemma C_to_D n : Life Edge TM5.retire (FrontC n) [0] (FrontD n) [0;0].
Proof.
  pose proof (@Life_terminal Edge TM5.retire 0 _ 0 1 _ _ [0;0]
    (Edge_even 0) (Pass_Doubles_head (1+n))) as HL.
  replace (4^(1+n)*4) with ((4^n*8)*2) in HL by (cbn[Nat.pow Nat.add]; lia).
  cbn[repeat app] in HL.
  unfold TM5.retire in HL.
  rewrite odd_0 in HL.
  unfold FrontC, FrontD.
  change (TM5.DWord 2 (3+n*2) [] 0) with
    (Alt (Nat.odd (3+n*2)) 2++TM5.DWord 4 (2+n*2) [] 0).
  replace (3+n*2) with (1+(1+n)*2) by lia; rewrite odd_1.
  replace (2+n*2) with ((1+n)*2) by lia; rewrite TM5.DWord_even_shape.
  cbn[TM5.GWord]; replace (4*4^(1+n)) with ((4^n*8)*2) by (cbn[Nat.pow Nat.add]; lia).
  rewrite odd_0; cbn[xorb app Alt] in HL |- *.
  applys_eq HL; cbn[Nat.pow Nat.add]; flia.
Qed.

Theorem Q_front n : Lives Edge retire 5 (QWord n) [0;0] (cut (FrontD n)) [0;0].
Proof.
  eapply Lives_cons; [apply Q_cut_step|].
  eapply Lives_cons; [eapply Life_cut_with; [apply Q_to_A|eapply Life_last; apply TM5.Q_internal|
    unfold TM5.QInternal; cbn[cut removelast Alt app Doubles In Nat.add negb]; auto|auto]|].
  eapply Lives_cons; [eapply Life_cut_with; [apply A_to_B|eapply Life_last; apply Q_to_A|
    unfold FrontA; cbn[cut removelast Alt app Doubles In Nat.add negb]; auto|auto]|].
  eapply Lives_cons; [eapply Life_cut_with; [apply B_to_C|eapply Life_last; apply A_to_B|
    unfold FrontB; cbn[cut removelast Alt app Doubles In Nat.add negb]; auto|auto]|].
  eapply Lives_cons; [eapply Life_cut_with; [apply C_to_D|eapply Life_last; apply B_to_C|
    unfold FrontC; cbn[cut removelast Alt app Doubles In Nat.add negb]; auto|auto]|constructor].
Qed.

Theorem Q_to_zero n : Lives Edge retire (9+n*2) (QWord n) [0;0]
  (Word (repeat 0 (4+n*2)) 0) [0;0].
Proof.
  pose proof (DWord_zeros (3+n*2) 0) as H.
  replace (3+n*2) with (1+(1+n)*2) in H by lia; rewrite odd_1 in H.
  cbn[repeat] in H.
  assert (HT : Lives Edge retire (4+n*2) (cut (FrontD n)) [0;0]
    (Word (repeat 0 (4+n*2)) 0) [0;0]) by (unfold FrontD; applys_eq H; flia).
  applys_eq (Lives_app (Q_front n) HT); flia.
Qed.

Theorem Q_round n : Lives Edge retire (4^(1+n)*24-1)
  (QWord n) [0;0] (QWord (1+n)) [0;0].
Proof.
  pose proof (canonical_word (1+n)) as H.
  replace (2+(1+n)*2) with (4+n*2) in H by lia.
  pose proof (TM5.CertBody_budget (4+n*2) (1+n)).
  applys_eq (Lives_app (Q_to_zero n) H); flia.
Qed.

Lemma Q_progress n : exists t, Lives Edge retire (1+t) (QWord n) [0;0] (QWord (1+n)) [0;0].
Proof.
  exists (4^(1+n)*24-2); pose proof (Nat.pow_nonzero 4 (1+n) ltac:(lia)).
  applys_eq (Q_round n); flia.
Qed.

Lemma Q_suffix_infinite : forall n t w xs,
  Lives Edge retire t w xs (QWord n) [0;0] -> InfiniteLife Edge retire w xs.
Proof.
  cofix IH; intros n t w xs H; destruct t.
  - inversion H; subst; destruct (Q_progress n) as [k HT].
    inversion HT; subst; econstructor; [eassumption|eapply (IH (1+n) k); eassumption].
  - inversion H; subst; econstructor; [eassumption|eapply (IH n t); eassumption].
Qed.

Theorem Q_infinite n : InfiniteLife Edge retire (QWord n) [0;0].
Proof. eapply (@Q_suffix_infinite n 0); constructor. Qed.

Lemma initial_infinite : InfiniteLife Edge retire [] [2;1].
Proof. eapply Lives_infinite; [apply initial_Q2|apply Q_infinite]. Qed.

Theorem nonhalt : ~halts tm c0.
Proof. apply nonhalt_from_lives, initial_infinite. Qed.

Lemma macro_next xs ys : Flow_Macro Edge retire xs ys ->
  Flow_InfiniteMacro Edge retire xs -> Flow_InfiniteMacro Edge retire ys.
Proof.
  intros HM HI; destruct HI as [xs zs HZ HI]; inversion HM; subst; inversion HZ; subst.
  match goal with H : Run _ _ ys, H' : Run _ _ zs |- _ =>
    assert (ys=zs) by (eapply (Run_functional Edge_functional); eassumption); subst; assumption end.
Qed.

Lemma later_infinite : Flow_InfiniteMacro Edge retire [4;2;0].
Proof.
  eapply macro_next with (xs:=[3;1;1;0]).
  - constructor; change (Run [true;true;false;true] [1;1;0] [4;2;0]).
    eapply Run_cons; [constructor|]; eapply Run_cons; [constructor|].
    eapply Run_cons; [apply LInc_I; [discriminate|constructor]|].
    eapply Run_cons; constructor.
  - eapply macro_next with (xs:=[2;1]).
    + constructor; cbn[retire Alt Nat.odd Nat.even negb].
      eapply Run_cons; [apply LInc_edge, (Edge_odd 0)|].
      eapply Run_cons; [apply LInc_I; [discriminate|apply LInc_I; [discriminate|constructor]]|].
      eapply Run_cons; constructor.
    + eapply (InfiniteLife_sound_bounded Edge_functional Edge_size);
        [apply initial_infinite|constructor].
Qed.

Definition Positive xs := exists a tail, xs=a::tail /\ a<>0.

Lemma LInc_positive p xs ys : LInc p xs ys -> Positive ys.
Proof.
  intro H; destruct H; unfold Positive.
  - exists (1+a),xs; split; [reflexivity|lia].
  - exists a,ys; auto.
  - destruct H; (eexists; eexists; split; [reflexivity|lia]).
Qed.

Lemma Run_positive w xs ys : Run w xs ys -> Positive xs -> Positive ys.
Proof. intro H; induction H; eauto using LInc_positive. Qed.

Lemma Macro_positive xs ys : Flow_Macro Edge retire xs ys -> Positive ys.
Proof.
  intro H; destruct H; cbn[retire] in H; inversion H; subst.
  eapply Run_positive; [eassumption|eapply LInc_positive; eassumption].
Qed.

End Skelet17.

(* The eight encodings use the same stream proof, but different physical heads. *)
Section SkeletMachine.
Close Scope sym.
Variable machine : TM.
Variable cfg : list nat -> nat -> Q*tape.
Hypothesis inc_right : forall n xs ys, Flow_LInc Skelet17.Edge (negb (Nat.odd n)) xs ys ->
  cfg xs (1+n) -[machine]->* cfg ys n.
Hypothesis inc_zero : forall a xs ys, Flow_LInc Skelet17.Edge (Nat.odd a) xs ys ->
  cfg (a::xs) 0 -[machine]->+ cfg ys a.

Lemma skelet_run_right n xs ys :
  Flow_Run Skelet17.Edge (Alt (Nat.odd n) n) xs ys -> cfg xs n -[machine]->* cfg ys 0.
Proof.
  revert xs; induction n; intros xs H.
  - inversion H; subst; apply evstep_refl.
  - cbn[Alt] in H; rewrite odd_S, negb_involutive in H.
    inversion H as [|p w source cut target HL HR]; subst.
    follow (inc_right n HL); apply IHn; assumption.
Qed.

Lemma skelet_macro xs ys : Flow_Macro Skelet17.Edge Skelet17.retire xs ys ->
  cfg xs 0 -[machine]->+ cfg ys 0.
Proof.
  intro H; destruct H; cbn[Skelet17.retire] in H.
  inversion H as [|p w source cut target HL HR]; subst.
  follow10 (inc_zero a HL); apply skelet_run_right; assumption.
Qed.

Theorem skelet_machine_nonhalt :
  c0 -[machine]->* cfg [4;2;0] 0 -> ~halts machine c0.
Proof.
  intro H; eapply multistep_nonhalt; [exact H|].
  eapply progress_nonhalt with (P:=fun c => exists xs,
    Flow_InfiniteMacro Skelet17.Edge Skelet17.retire xs /\ c=cfg xs 0).
  - intros c [xs [HI ->]]; destruct HI as [xs ys HM HI].
    exists (cfg ys 0); split; [exists ys; auto|apply skelet_macro; assumption].
  - exists [4;2;0]; split; [apply Skelet17.later_infinite|reflexivity].
Qed.
End SkeletMachine.

Theorem skelet_positive_nonhalt machine cfg :
  (forall xs ys, Skelet17.Positive xs -> Flow_Macro Skelet17.Edge Skelet17.retire xs ys ->
    cfg xs -[machine]->+ cfg ys) ->
  c0 -[machine]->* cfg [4;2;0]%nat -> ~halts machine c0.
Proof.
  intros HM H0; eapply multistep_nonhalt; [exact H0|].
  eapply progress_nonhalt with (P:=fun c => exists xs,
    Flow_InfiniteMacro Skelet17.Edge Skelet17.retire xs /\ Skelet17.Positive xs /\ c=cfg xs).
  - intros c [xs [HI [HP ->]]]; destruct HI as [xs ys HS HI].
    exists (cfg ys); split; [exists ys; eauto using Skelet17.Macro_positive|apply HM; assumption].
  - exists [4;2;0]%nat; repeat split; try reflexivity; [apply Skelet17.later_infinite|].
    exists 4%nat,[2;0]%nat; split; [reflexivity|discriminate].
Qed.

(* Skelet17 variants v2 through v8. *)

Open Scope sym.


Module Skelet17_v2.
Definition tm := Eval compute in (TM_from_str "1RB1RF_0LC1RE_0LD1LC_1RA1LB_0RB1LA_---0RA").
Notation "c -->* c'" := (c -[tm]->* c') (at level 40).
Notation "c -->+ c'" := (c -[tm]->+ c') (at level 40).
Notation LC := Skelet17.LC.
Notation LInc := (Flow_LInc Skelet17.Edge).
Definition S1 xs n := LC xs {{B}}> [1;0]^^n *> 0inf.
Definition QL (p:bool) := if p then B else C.

Lemma LInc_spec p xs ys : LInc p xs ys ->
  forall r, LC xs <{{QL p}} [1;0] *> r -->* LC ys {{B}}> r.
Proof.
  intro H; induction H; intros r.
  - cbn[Skelet17.LC QL]; es.
  - destruct (mod2 a) as [k E|k E]; subst a.
    + rewrite odd_0 in IHLInc; destruct k as [|k]; [lia|].
      replace (S k*2) with (2+k*2) by lia.
      cbn[Skelet17.LC QL] in *; es; er; follow IHLInc; es.
    + rewrite odd_1 in IHLInc; cbn[Skelet17.LC QL] in *.
      es; er; follow IHLInc; es.
  - destruct H; cbn[Skelet17.LC QL]; es.
Qed.

Lemma Inc_right n xs ys : LInc (negb (Nat.odd n)) xs ys ->
  S1 xs (1+n) -->* S1 ys n.
Proof.
  intro H; destruct (mod2 n) as [a E|a E]; subst n.
  - rewrite odd_0 in H; eapply LInc_spec in H; es; er; follow H; finish.
  - rewrite odd_1 in H; eapply LInc_spec in H; es; er; follow H; finish.
Qed.

Lemma Inc_zero a xs ys : LInc (Nat.odd a) xs ys ->
  S1 (a::xs) 0 -->+ S1 ys a.
Proof.
  intro H; destruct (mod2 a) as [k E|k E]; subst a.
  - rewrite odd_0 in H; eapply LInc_spec in H; unfold S1; cbn[Skelet17.LC].
    es; er; follow H; finish.
  - rewrite odd_1 in H; eapply LInc_spec in H; unfold S1; cbn[Skelet17.LC].
    es; er; follow H; finish.
Qed.

Lemma init : c0 -->* S1 [4;2;0]%nat 0.
Proof. unfold S1; esx. Qed.

Theorem nonhalt : ~halts tm c0.
Proof. eapply skelet_machine_nonhalt; eauto using Inc_right, Inc_zero, init. Qed.
End Skelet17_v2.

Module Skelet17_v3.
Definition tm := Eval compute in (TM_from_str "1RB1RF_0LC1RE_0LD1LC_1RA1LB_1LA0RA_---0RB").
Notation "c -->* c'" := (c -[tm]->* c') (at level 40).
Notation "c -->+ c'" := (c -[tm]->+ c') (at level 40).
Notation LC := Skelet17.LC.
Notation LInc := (Flow_LInc Skelet17.Edge).
Definition S1 xs n := LC xs {{B}}> [1;0]^^n *> 0inf.
Definition QL (p:bool) := if p then B else C.

Lemma LInc_spec p xs ys : LInc p xs ys ->
  forall r, LC xs <{{QL p}} [1;0] *> r -->* LC ys {{B}}> r.
Proof.
  intro H; induction H; intros r.
  - cbn[Skelet17.LC QL]; es.
  - destruct (mod2 a) as [k E|k E]; subst a.
    + rewrite odd_0 in IHLInc; destruct k as [|k]; [lia|].
      replace (S k*2) with (2+k*2) by lia.
      cbn[Skelet17.LC QL] in *; es; er; follow IHLInc; es.
    + rewrite odd_1 in IHLInc; cbn[Skelet17.LC QL] in *.
      es; er; follow IHLInc; es.
  - destruct H; cbn[Skelet17.LC QL]; es.
Qed.

Lemma Inc_right n xs ys : LInc (negb (Nat.odd n)) xs ys ->
  S1 xs (1+n) -->* S1 ys n.
Proof.
  intro H; destruct (mod2 n) as [a E|a E]; subst n.
  - rewrite odd_0 in H; eapply LInc_spec in H; es; er; follow H; finish.
  - rewrite odd_1 in H; eapply LInc_spec in H; es; er; follow H; finish.
Qed.

Lemma Inc_zero a xs ys : LInc (Nat.odd a) xs ys ->
  S1 (a::xs) 0 -->+ S1 ys a.
Proof.
  intro H; destruct (mod2 a) as [k E|k E]; subst a.
  - rewrite odd_0 in H; eapply LInc_spec in H; unfold S1; cbn[Skelet17.LC].
    es; er; follow H; finish.
  - rewrite odd_1 in H; eapply LInc_spec in H; unfold S1; cbn[Skelet17.LC].
    es; er; follow H; finish.
Qed.

Lemma init : c0 -->* S1 [4;2;0]%nat 0.
Proof. unfold S1; esx. Qed.

Theorem nonhalt : ~halts tm c0.
Proof. eapply skelet_machine_nonhalt; eauto using Inc_right, Inc_zero, init. Qed.
End Skelet17_v3.

Module Skelet17_v4.
Definition tm := Eval compute in (TM_from_str "1RB---_0LC1RF_0LD1LC_1LE1LB_0RE1RA_0RB0RA").
Notation "c -->* c'" := (c -[tm]->* c') (at level 40).
Notation "c -->+ c'" := (c -[tm]->+ c') (at level 40).
Notation LC := Skelet17.LC.
Notation LInc := (Flow_LInc Skelet17.Edge).
Definition S1 xs n := LC xs {{B}}> [1;0]^^n *> 0inf.
Definition QL (p:bool) := if p then B else C.

Lemma LInc_spec p xs ys : LInc p xs ys ->
  forall r, LC xs <{{QL p}} [1;0] *> r -->* LC ys {{B}}> r.
Proof.
  intro H; induction H; intros r.
  - cbn[Skelet17.LC QL]; es.
  - destruct (mod2 a) as [k E|k E]; subst a.
    + rewrite odd_0 in IHLInc; destruct k as [|k]; [lia|].
      replace (S k*2) with (2+k*2) by lia.
      cbn[Skelet17.LC QL] in *; es; er; follow IHLInc; es.
    + rewrite odd_1 in IHLInc; cbn[Skelet17.LC QL] in *.
      es; er; follow IHLInc; es.
  - destruct H; cbn[Skelet17.LC QL]; es.
Qed.

Lemma Inc_right n xs ys : LInc (negb (Nat.odd n)) xs ys ->
  S1 xs (1+n) -->* S1 ys n.
Proof.
  intro H; destruct (mod2 n) as [a E|a E]; subst n.
  - rewrite odd_0 in H; eapply LInc_spec in H; es; er; follow H; finish.
  - rewrite odd_1 in H; eapply LInc_spec in H; es; er; follow H; finish.
Qed.

Lemma Inc_zero a xs ys : LInc (Nat.odd a) xs ys ->
  S1 (a::xs) 0 -->+ S1 ys a.
Proof.
  intro H; destruct (mod2 a) as [k E|k E]; subst a.
  - rewrite odd_0 in H; eapply LInc_spec in H; unfold S1; cbn[Skelet17.LC].
    es; er; follow H; finish.
  - rewrite odd_1 in H; eapply LInc_spec in H; unfold S1; cbn[Skelet17.LC].
    es; er; follow H; finish.
Qed.

Lemma init : c0 -->* S1 [4;2;0]%nat 0.
Proof. unfold S1; esx. Qed.

Theorem nonhalt : ~halts tm c0.
Proof. eapply skelet_machine_nonhalt; eauto using Inc_right, Inc_zero, init. Qed.
End Skelet17_v4.

Module Skelet17_v5.
Definition tm := Eval compute in (TM_from_str "1RB---_0LC1RE_0LD1LC_1RA1LB_0RB1RF_0LF0RA").
Notation "c -->* c'" := (c -[tm]->* c') (at level 40).
Notation "c -->+ c'" := (c -[tm]->+ c') (at level 40).
Notation LC := Skelet17.LC.
Notation LInc := (Flow_LInc Skelet17.Edge).
Definition S1 xs n := LC xs {{B}}> [1;0]^^n *> 0inf.
Definition QL (p:bool) := if p then B else C.

Lemma LInc_spec p xs ys : LInc p xs ys ->
  forall r, LC xs <{{QL p}} [1;0] *> r -->* LC ys {{B}}> r.
Proof.
  intro H; induction H; intros r.
  - cbn[Skelet17.LC QL]; es.
  - destruct (mod2 a) as [k E|k E]; subst a.
    + rewrite odd_0 in IHLInc; destruct k as [|k]; [lia|].
      replace (S k*2) with (2+k*2) by lia.
      cbn[Skelet17.LC QL] in *; es; er; follow IHLInc; es.
    + rewrite odd_1 in IHLInc; cbn[Skelet17.LC QL] in *.
      es; er; follow IHLInc; es.
  - destruct H; cbn[Skelet17.LC QL]; es.
Qed.

Lemma Inc_right n xs ys : LInc (negb (Nat.odd n)) xs ys ->
  S1 xs (1+n) -->* S1 ys n.
Proof.
  intro H; destruct (mod2 n) as [a E|a E]; subst n.
  - rewrite odd_0 in H; eapply LInc_spec in H; es; er; follow H; finish.
  - rewrite odd_1 in H; eapply LInc_spec in H; es; er; follow H; finish.
Qed.

Lemma Inc_zero a xs ys : LInc (Nat.odd a) xs ys ->
  S1 (a::xs) 0 -->+ S1 ys a.
Proof.
  intro H; destruct (mod2 a) as [k E|k E]; subst a.
  - rewrite odd_0 in H; eapply LInc_spec in H; unfold S1; cbn[Skelet17.LC].
    es; er; follow H; finish.
  - rewrite odd_1 in H; eapply LInc_spec in H; unfold S1; cbn[Skelet17.LC].
    es; er; follow H; finish.
Qed.

Lemma init : c0 -->* S1 [4;2;0]%nat 0.
Proof. unfold S1; esx. Qed.

Theorem nonhalt : ~halts tm c0.
Proof. eapply skelet_machine_nonhalt; eauto using Inc_right, Inc_zero, init. Qed.
End Skelet17_v5.

Module Skelet17_v6.
Definition tm := Eval compute in (TM_from_str "1RB---_0LC1LB_1RE1LD_0LB1RF_1RD1RA_0RD0RE").
Notation "c -->* c'" := (c -[tm]->* c') (at level 40).
Notation "c -->+ c'" := (c -[tm]->+ c') (at level 40).
Notation LC := Skelet17.LC.
Notation LInc := (Flow_LInc Skelet17.Edge).
Definition S1 xs n := LC xs {{D}}> [1;0]^^n *> 0inf.
Definition QL (p:bool) := if p then D else B.

Lemma LInc_spec p xs ys : LInc p xs ys ->
  forall r, LC xs <{{QL p}} [1;0] *> r -->* LC ys {{D}}> r.
Proof.
  intro H; induction H; intros r.
  - cbn[Skelet17.LC QL]; es.
  - destruct (mod2 a) as [k E|k E]; subst a.
    + rewrite odd_0 in IHLInc; destruct k as [|k]; [lia|].
      replace (S k*2) with (2+k*2) by lia.
      cbn[Skelet17.LC QL] in *; es; er; follow IHLInc; es.
    + rewrite odd_1 in IHLInc; cbn[Skelet17.LC QL] in *.
      es; er; follow IHLInc; es.
  - destruct H; cbn[Skelet17.LC QL]; es.
Qed.

Lemma Inc_right n xs ys : LInc (negb (Nat.odd n)) xs ys ->
  S1 xs (1+n) -->* S1 ys n.
Proof.
  intro H; destruct (mod2 n) as [a E|a E]; subst n.
  - rewrite odd_0 in H; eapply LInc_spec in H; es; er; follow H; finish.
  - rewrite odd_1 in H; eapply LInc_spec in H; es; er; follow H; finish.
Qed.

Lemma Inc_zero a xs ys : LInc (Nat.odd a) xs ys ->
  S1 (a::xs) 0 -->+ S1 ys a.
Proof.
  intro H; destruct (mod2 a) as [k E|k E]; subst a.
  - rewrite odd_0 in H; eapply LInc_spec in H; unfold S1; cbn[Skelet17.LC].
    es; er; follow H; finish.
  - rewrite odd_1 in H; eapply LInc_spec in H; unfold S1; cbn[Skelet17.LC].
    es; er; follow H; finish.
Qed.

Lemma init : c0 -->* S1 [4;2;0]%nat 0.
Proof. unfold S1; esx. Qed.

Theorem nonhalt : ~halts tm c0.
Proof. eapply skelet_machine_nonhalt; eauto using Inc_right, Inc_zero, init. Qed.
End Skelet17_v6.

Module Skelet17_v7.
Definition tm := Eval compute in (TM_from_str "1RB1RF_0LC1RE_0LD1LC_1RA1LB_0RB0LA_0RA---").
Notation "c -->* c'" := (c -[tm]->* c') (at level 40).
Notation "c -->+ c'" := (c -[tm]->+ c') (at level 40).
Notation LC := Skelet17.LC.
Notation LInc := (Flow_LInc Skelet17.Edge).
Definition S1 xs n := LC xs {{B}}> [1;0]^^n *> 0inf.
Definition QL (p:bool) := if p then B else C.

Lemma LInc_spec p xs ys : LInc p xs ys ->
  forall r, LC xs <{{QL p}} [1;0] *> r -->* LC ys {{B}}> r.
Proof.
  intro H; induction H; intros r.
  - cbn[Skelet17.LC QL]; es.
  - destruct (mod2 a) as [k E|k E]; subst a.
    + rewrite odd_0 in IHLInc; destruct k as [|k]; [lia|].
      replace (S k*2) with (2+k*2) by lia.
      cbn[Skelet17.LC QL] in *; es; er; follow IHLInc; es.
    + rewrite odd_1 in IHLInc; cbn[Skelet17.LC QL] in *.
      es; er; follow IHLInc; es.
  - destruct H; cbn[Skelet17.LC QL]; es.
Qed.

Lemma Inc_right n xs ys : LInc (negb (Nat.odd n)) xs ys ->
  S1 xs (1+n) -->* S1 ys n.
Proof.
  intro H; destruct (mod2 n) as [a E|a E]; subst n.
  - rewrite odd_0 in H; eapply LInc_spec in H; es; er; follow H; finish.
  - rewrite odd_1 in H; eapply LInc_spec in H; es; er; follow H; finish.
Qed.

Lemma Inc_zero a xs ys : LInc (Nat.odd a) xs ys ->
  S1 (a::xs) 0 -->+ S1 ys a.
Proof.
  intro H; destruct (mod2 a) as [k E|k E]; subst a.
  - rewrite odd_0 in H; eapply LInc_spec in H; unfold S1; cbn[Skelet17.LC].
    es; er; follow H; finish.
  - rewrite odd_1 in H; eapply LInc_spec in H; unfold S1; cbn[Skelet17.LC].
    es; er; follow H; finish.
Qed.

Lemma init : c0 -->* S1 [4;2;0]%nat 0.
Proof. unfold S1; esx. Qed.

Theorem nonhalt : ~halts tm c0.
Proof. eapply skelet_machine_nonhalt; eauto using Inc_right, Inc_zero, init. Qed.
End Skelet17_v7.

Module Skelet17_v8.
Definition tm := Eval compute in (TM_from_str "1RB1LC_1RC---_0LD1RE_0LA1LD_0RF0RB_0LC1RE").
Notation "c -->* c'" := (c -[tm]->* c') (at level 40).
Notation "c -->+ c'" := (c -[tm]->+ c') (at level 40).
Notation LC := Skelet17.LC.
Notation LInc := (Flow_LInc Skelet17.Edge).
Definition S1 xs n := LC xs << 1 {{E}}> [0;1]^^n *> 0inf.
Definition RC (n:nat) := match n with O => 0inf | S n => [0;1]^^n *> 1 >> 0inf end.
Definition S2 xs n := LC xs << 1 {{E}}> RC n.
Definition QL (p:bool) := if p then C else D.

Lemma LInc_spec p xs ys : LInc p xs ys ->
  forall r, LC xs <{{QL p}} [1;0;1] *> r -->* LC ys << 1 {{E}}> r.
Proof.
  intro H; induction H; intros r.
  - cbn[Skelet17.LC QL]; es.
  - destruct (mod2 a) as [k EQ|k EQ]; subst a.
    + rewrite odd_0 in IHLInc; destruct k as [|k]; [lia|].
      replace (S k*2) with (2+k*2) by lia.
      cbn[Skelet17.LC QL] in *; es; er; follow IHLInc; es.
    + rewrite odd_1 in IHLInc; cbn[Skelet17.LC QL] in *.
      es; er; follow IHLInc; es.
  - destruct H; cbn[Skelet17.LC QL]; es.
Qed.

Lemma Inc_right n xs ys : LInc (negb (Nat.odd n)) xs ys ->
  S1 xs (1+n) -->* S1 ys n.
Proof.
  intro H; destruct (mod2 n) as [a EQ|a EQ]; subst n.
  - rewrite odd_0 in H; eapply LInc_spec in H; es; er; follow H; finish.
  - rewrite odd_1 in H; eapply LInc_spec in H; es; er; follow H; finish.
Qed.

Lemma Inc_first n xs ys : LInc (negb (Nat.odd n)) xs ys ->
  S2 xs (1+n) -->* S1 ys n.
Proof.
  intro H; destruct n as [|n].
  - cbn[Nat.odd Nat.even negb] in H; eapply LInc_spec in H.
    unfold S1, S2; cbn[RC]; es; er; follow H; finish.
  - destruct (mod2 n) as [a EQ|a EQ]; subst n.
    + change (S (a*2)) with (1+a*2) in *; rewrite odd_1 in H.
      eapply LInc_spec in H; unfold S1, S2; cbn[RC]; es; er; es; er; follow H; finish.
    + replace (S (1+a*2)) with (2+a*2) in * by lia.
      change (negb (Nat.odd (2+a*2))) with (negb (Nat.odd ((1+a)*2))) in H.
      rewrite odd_0 in H; eapply LInc_spec in H.
      unfold S1, S2; cbn[RC]; es; er; es; er; follow H; finish.
Qed.

Lemma Inc_zero (a:nat) xs ys : a<>O -> LInc (Nat.odd a) xs ys ->
  S1 (a::xs) 0 -->+ S2 ys a.
Proof.
  intros HA H; destruct (mod2 a) as [k EQ|k EQ]; subst a.
  - destruct k as [|k]; [contradiction HA; reflexivity|].
    replace (S k*2) with (2+k*2) in * by lia.
    change (Nat.odd (2+k*2)) with (Nat.odd ((1+k)*2)) in H.
    rewrite odd_0 in H; eapply LInc_spec in H; unfold S1, S2; cbn[Skelet17.LC RC].
    es; er; follow H; finish; rewrite lpow_mul; reflexivity.
  - rewrite odd_1 in H; eapply LInc_spec in H; unfold S1, S2; cbn[Skelet17.LC RC].
    es; er; follow H; finish; rewrite lpow_mul; reflexivity.
Qed.

Lemma Run_right n xs ys : Flow_Run Skelet17.Edge (Alt (Nat.odd n) n) xs ys ->
  S2 xs n -->* S1 ys 0.
Proof.
  intro H; destruct n as [|n]; [inversion H; subst; apply evstep_refl|].
  cbn[Alt] in H; rewrite odd_S in H.
  inversion H as [|p w source cut target HL HR]; subst.
  follow (Inc_first n HL).
  eapply (skelet_run_right S1 Inc_right); rewrite negb_involutive in HR; exact HR.
Qed.

Lemma Macro_spec xs ys : Skelet17.Positive xs -> Flow_Macro Skelet17.Edge Skelet17.retire xs ys ->
  S1 xs 0 -->+ S1 ys 0.
Proof.
  intros HP H; destruct H; destruct HP as [b [tail [EQ HA]]]; injection EQ as -> ->.
  cbn[Skelet17.retire] in H; inversion H as [|p w source cut target HL HR]; subst.
  follow10 (Inc_zero HA HL); apply Run_right; assumption.
Qed.

Lemma init : c0 -->* S1 [4;2;0]%nat 0.
Proof. unfold S1; esx. Qed.

Theorem nonhalt : ~halts tm c0.
Proof. eapply skelet_positive_nonhalt with (cfg:=fun xs => S1 xs 0); eauto using Macro_spec, init. Qed.
End Skelet17_v8.

(* The common odd-dimensional counter. *)

Close Scope sym.

Module OddCounter.
(* The common all-false counter in TM1/TM8 has odd dimension 3+2n.
   The certificate exits through rotor 2, not through rotor 1. *)
Definition LowRow N d k := Cycles [N;0;N;d] (4^k*2-1)++[N;0;N].
Definition HighRow N d k := Cycles [N;0;N;d] (4^k*4).
Fixpoint Body N n := match n with
  | 0 => [] | S k => Body N k++[LowRow N (1+k*2) k;HighRow N (2+k*2) k] end.
Definition RootRow N n := Cycles [0;N-1] (4^n*4).
Definition LastRow N n := Cycles [N;0;N;N-2] (4^n*2-1)++[N;0].
Definition Rows n := RootRow (3+n*2) n::[3+n*2]::[3+n*2;0;3+n*2;4+n*2]::
  (Body (3+n*2) n++[LastRow (3+n*2) n]).

Lemma LowRow_length N d k : length (LowRow N d k)=4^k*8-1.
Proof. unfold LowRow; rewrite length_app, Cycles_length; cbn[length]; nia. Qed.
Lemma HighRow_length N d k : length (HighRow N d k)=4^k*16.
Proof. unfold HighRow; rewrite Cycles_length; cbn[length]; lia. Qed.
Lemma RootRow_length N n : length (RootRow N n)=4^n*8.
Proof. unfold RootRow; rewrite Cycles_length; cbn[length]; lia. Qed.
Lemma LastRow_length N n : length (LastRow N n)=4^n*8-2.
Proof. unfold LastRow; rewrite length_app, Cycles_length; cbn[length]; nia. Qed.

Lemma LowRow_count N d k v : count_occ Nat.eq_dec (LowRow N d k) v=
  4^k*4*mark N v+4^k*2*mark 0 v+(4^k*2-1)*mark d v.
Proof. unfold LowRow; rewrite count_occ_app, Cycles_count, !count_cons; cbn[count_occ]; nia. Qed.
Lemma HighRow_count N d k v : count_occ Nat.eq_dec (HighRow N d k) v=
  4^k*8*mark N v+4^k*4*mark 0 v+4^k*4*mark d v.
Proof. unfold HighRow; rewrite Cycles_count, !count_cons; cbn[count_occ]; nia. Qed.
Lemma RootRow_count N n v : count_occ Nat.eq_dec (RootRow N n) v=
  4^n*4*mark 0 v+4^n*4*mark (N-1) v.
Proof. unfold RootRow; rewrite Cycles_count, !count_cons; cbn[count_occ]; nia. Qed.
Lemma LastRow_count N n v : count_occ Nat.eq_dec (LastRow N n) v=
  (4^n*4-1)*mark N v+4^n*2*mark 0 v+(4^n*2-1)*mark (N-2) v.
Proof. unfold LastRow; rewrite count_occ_app, Cycles_count, !count_cons; cbn[count_occ]; nia. Qed.

Lemma Body_length N n : length (Body N n)=n*2.
Proof. induction n; cbn[Body]; rewrite ?length_app, ?IHn; cbn[length]; lia. Qed.

Lemma Body_balance N n v : incoming (Body N n) v+
  (4^n*2-1)*mark (1+n*2) v+4^n*4*mark (2+n*2) v=
  weighted (Body N n) 3 v+(4^n-1)*4*mark N v+(4^n-1)*2*mark 0 v+mark 1 v+4*mark 2 v.
Proof.
  induction n as [|n IH]; [cbn[Body incoming weighted concat count_occ Nat.pow Nat.sub Nat.add Nat.mul]; lia|].
  cbn[Body]; unfold incoming in *.
  rewrite concat_app, count_occ_app, weighted_app, Body_length.
  cbn[concat weighted]; rewrite !count_occ_app, LowRow_count, HighRow_count,
    LowRow_length, HighRow_length; cbn[count_occ].
  replace (S n*2) with (2+n*2) by lia; replace (n*2+3) with (3+n*2) by lia.
  assert (HP : 4^n<>0) by (apply Nat.pow_nonzero; lia).
  cbn[Nat.pow]; remember (4^n-1) as q; replace (4^n) with (1+q) in * by lia.
  replace ((1+q)*2-1) with (1+q*2) in * by lia.
  replace ((1+q)*8-1) with (7+q*8) in * by lia.
  replace (4*(1+q)-1) with (3+q*4) in * by lia.
  replace (4*(1+q)*2-1) with (7+q*8) in * by lia.
  cbn[Nat.add] in *; ring_simplify in IH; ring_simplify; lia.
Qed.

Lemma Rows_length n : length (Rows n)=4+n*2.
Proof. unfold Rows; cbn[length]; rewrite length_app, Body_length; cbn; lia. Qed.

Theorem Rows_balance n : Balance (Rows n) 0 (4+n*2).
Proof.
  intro v; pose proof (Body_balance (3+n*2) n v) as HB.
  unfold Rows, incoming; cbn[concat]; rewrite concat_app; cbn[concat].
  rewrite !count_occ_app, RootRow_count, !count_cons, LastRow_count; cbn[count_occ].
  rewrite <- weighted_outgoing; cbn[weighted].
  rewrite RootRow_length, weighted_app, Body_length; cbn[weighted]; rewrite LastRow_length.
  replace (3+n*2-1) with (2+n*2) by lia; replace (3+n*2-2) with (1+n*2) by lia.
  replace (n*2+3) with (3+n*2) by lia.
  assert (HP : 4^n<>0) by (apply Nat.pow_nonzero; lia).
  remember (4^n-1) as q; replace (4^n) with (1+q) in * by lia.
  replace ((1+q)*8-2) with (6+q*8) by lia.
  replace ((1+q)*4-1) with (3+q*4) by lia.
  replace ((1+q)*2-1) with (1+q*2) in * by lia.
  unfold incoming in HB; cbn[Nat.add] in *; ring_simplify in HB; ring_simplify.
  cbn[length]; replace (n*2+3) with (3+n*2) by lia.
  replace (1+(1+n*2)) with (2+n*2) in HB by lia.
  replace (1+(2+n*2)) with (3+n*2) by lia.
  lia.
Qed.

Lemma Body_at N n : forall k, k<n ->
  nth (k*2) (Body N n) []=LowRow N (1+k*2) k /\
  nth (1+k*2) (Body N n) []=HighRow N (2+k*2) k.
Proof.
  induction n as [|n IH]; intros k HK; [lia|].
  destruct (Nat.eq_dec k n) as [->|Hne]; cbn[Body].
  - rewrite !app_nth2 by (rewrite Body_length; lia).
    rewrite Body_length, Nat.sub_diag; replace (1+n*2-n*2) with 1 by lia; split; reflexivity.
  - rewrite !app_nth1 by (rewrite Body_length; lia); apply IH; lia.
Qed.

Definition Rank n i := if i=?4+n*2 then 0 else if i=?0 then 3+n*2 else
  if Nat.odd i then if i=?3+n*2 then 4+n*2 else 5+n*2 else i.
Ltac rank_eqbs := repeat match goal with |- context [?a =? ?b] => destruct (Nat.eqb_spec a b) end; lia.

Lemma Rank_root n : Rank n 0=3+n*2.
Proof. unfold Rank; rank_eqbs. Qed.
Lemma Rank_sink n : Rank n (4+n*2)=0.
Proof. unfold Rank; rewrite Nat.eqb_refl; reflexivity. Qed.
Lemma Rank_even n k : k<>0 -> k<=1+n -> Rank n (k*2)=k*2.
Proof. intros; unfold Rank; rewrite odd_0; rank_eqbs. Qed.
Lemma Rank_odd n k : k<=1+n ->
  Rank n (1+k*2)=(if k=?1+n then 4+n*2 else 5+n*2).
Proof. intros; unfold Rank; rewrite odd_1; rank_eqbs. Qed.

Theorem Rows_forest n : LastForest (Rank n) (Rows n).
Proof.
  intros i Hne; assert (HI : i<4+n*2).
  { destruct (Nat.lt_ge_cases i (length (Rows n))) as [HL|HL].
    - rewrite Rows_length in HL; exact HL.
    - rewrite nth_overflow in Hne by lia; contradiction. }
  destruct i as [|[|[|i]]].
  - change (Rank n (last (RootRow (3+n*2) n) 0)<Rank n 0).
    unfold RootRow; rewrite Cycles_last by (discriminate || lia).
    cbn[last]; replace (3+n*2-1) with ((1+n)*2) by lia.
    rewrite Rank_even, Rank_root by lia; lia.
  - change (Rank n (3+n*2)<Rank n 1).
    replace (3+n*2) with (1+(1+n)*2) by lia.
    change (Rank n 1) with (Rank n (1+0*2)).
    rewrite !Rank_odd by lia; rewrite Nat.eqb_refl; rank_eqbs.
  - change (Rank n (4+n*2)<Rank n 2).
    change (Rank n 2) with (Rank n (1*2)); rewrite Rank_sink, Rank_even by lia; lia.
  - change (Rank n (last (nth i (Body (3+n*2) n++[LastRow (3+n*2) n]) []) 0)<Rank n (3+i)).
    destruct (Nat.eq_dec i (n*2)) as [->|Hlast].
    + rewrite app_nth2 by (rewrite Body_length; lia).
      rewrite Body_length, Nat.sub_diag; cbn[nth].
      unfold LastRow; rewrite last_suffix by discriminate; cbn[last]; rewrite Rank_root.
      replace (3+n*2) with (1+(1+n)*2) by lia; rewrite Rank_odd, Nat.eqb_refl by lia; lia.
    + rewrite app_nth1 by (rewrite Body_length; lia).
      destruct (mod2 i) as [k E|k E]; subst i.
      * rewrite (proj1 (Body_at (3+n*2) (n:=n) (k:=k) ltac:(lia))).
        unfold LowRow; rewrite last_suffix by discriminate; cbn[last].
        replace (3+n*2) with (1+(1+n)*2) by lia.
        replace (3+k*2) with (1+(1+k)*2) by lia.
        rewrite !Rank_odd by lia; rewrite Nat.eqb_refl; rank_eqbs.
      * rewrite (proj2 (Body_at (3+n*2) (n:=n) (k:=k) ltac:(lia))).
        unfold HighRow; rewrite Cycles_last by (discriminate || lia); cbn[last].
        replace (2+k*2) with ((1+k)*2) by lia.
        replace (3+(1+k*2)) with ((2+k)*2) by lia.
        rewrite !Rank_even by lia; lia.
Qed.

Lemma Body_budget N n : length (concat (Body N n))+n+8=4^n*8.
Proof.
  induction n; [reflexivity|].
  cbn[Body]; rewrite concat_app, length_app.
  cbn[concat]; rewrite !length_app, LowRow_length, HighRow_length; cbn[length Nat.pow]; lia.
Qed.

Lemma Rows_budget n : length (concat (Rows n))=4^n*24-n-5.
Proof.
  pose proof (Body_budget (3+n*2) n).
  unfold Rows; cbn[concat]; rewrite !length_app, concat_app, length_app, RootRow_length.
  cbn[concat]; rewrite length_app, LastRow_length; cbn[length]; lia.
Qed.

Theorem stack_exit n : exists rows', StackWalk 0 (Rows n) (4+n*2) rows' (4^n*24-n-5) /\
  forall i, nth i rows' []=[].
Proof.
  pose proof (stack_certificate (Rows_balance n) (Rows_forest n)) as H.
  rewrite Rows_budget in H; exact H.
Qed.
Definition ExitMove N i a j := TM5.Move N i a j \/ (i=2 /\ a=3 /\ j=1+N).

Lemma RootRow_rules N n : Indexed (TM5.Move N 0) 0 (RootRow N n).
Proof.
  unfold RootRow; rewrite <- (app_nil_r (Cycles _ _)).
  change (Indexed (TM5.Move N 0) (0*length [0;N-1]) (Cycles [0;N-1] (4^n*4)++[])).
  apply Indexed_cycles; [|exact (fun _=>I)].
  intro a; cbn[length Indexed]; split; [apply TM5.Move_root_even|split; [apply TM5.Move_root_odd|exact I]].
Qed.

Lemma LowRow_rules N i k : 2<i -> Indexed (TM5.Move N i) 0 (LowRow N (i-2) k).
Proof.
  intro HI; unfold LowRow; change (Indexed (TM5.Move N i) (0*length [N;0;N;i-2])
    (Cycles [N;0;N;i-2] (4^k*2-1)++[N;0;N])).
  apply Indexed_cycles; intro a; [apply TM5.Rotor_rules; exact HI|apply TM5.Rotor_three; lia].
Qed.

Lemma HighRow_rules N i k : 2<i -> Indexed (TM5.Move N i) 0 (HighRow N (i-2) k).
Proof.
  intro HI; unfold HighRow; rewrite <- (app_nil_r (Cycles _ _)).
  change (Indexed (TM5.Move N i) (0*length [N;0;N;i-2]) (Cycles [N;0;N;i-2] (4^k*4)++[])).
  apply Indexed_cycles; intro a; [apply TM5.Rotor_rules; exact HI|exact I].
Qed.

Lemma LastRow_rules n : Indexed (TM5.Move (3+n*2) (3+n*2)) 0 (LastRow (3+n*2) n).
Proof.
  unfold LastRow; change (Indexed (TM5.Move (3+n*2) (3+n*2))
    (0*length [3+n*2;0;3+n*2;3+n*2-2])
    (Cycles [3+n*2;0;3+n*2;3+n*2-2] (4^n*2-1)++[3+n*2;0])).
  apply Indexed_cycles; intro a; [apply TM5.Rotor_rules; lia|].
  cbn[length Indexed]; split; [|split; [apply TM5.Move_one; lia|exact I]].
  replace (a*4) with ((a*2)*2) by lia; apply TM5.Move_even; lia.
Qed.

Lemma Rows_rules n : RowRules (ExitMove (3+n*2)) (Rows n) (repeat 0 (4+n*2)).
Proof.
  rewrite <- Rows_length; apply RowRules_initial; intro i.
  destruct (Nat.lt_ge_cases i (length (Rows n))) as [HI|HI];
    [rewrite Rows_length in HI|rewrite nth_overflow by lia; exact I].
  destruct i as [|[|[|i]]].
  - change (Indexed (ExitMove (3+n*2) 0) 0 (RootRow (3+n*2) n)).
    eapply Indexed_mono; [intros; left; eassumption|apply RootRow_rules].
  - change (ExitMove (3+n*2) 1 0 (3+n*2) /\ True).
    split; [left; exact (@TM5.Move_even (3+n*2) 1 0 ltac:(lia))|exact I].
  - change (Indexed (ExitMove (3+n*2) 2) 0 ([3+n*2;0;3+n*2]++[4+n*2])).
    rewrite Indexed_app; split.
    + eapply Indexed_mono; [intros; left; eassumption|exact (@TM5.Rotor_three (3+n*2) 2 0 ltac:(lia))].
    + cbn[Indexed length]; split; [right; auto|exact I].
  - change (Indexed (ExitMove (3+n*2) (3+i)) 0
      (nth i (Body (3+n*2) n++[LastRow (3+n*2) n]) [])).
    destruct (Nat.eq_dec i (n*2)) as [->|Hlast].
    + rewrite app_nth2 by (rewrite Body_length; lia).
      rewrite Body_length, Nat.sub_diag; cbn[nth].
      eapply Indexed_mono; [intros; left; eassumption|apply LastRow_rules].
    + rewrite app_nth1 by (rewrite Body_length; lia).
      destruct (mod2 i) as [k E|k E]; subst i.
      * rewrite (proj1 (Body_at (3+n*2) (n:=n) (k:=k) ltac:(lia))).
        replace (1+k*2) with (3+k*2-2) at 2 by lia.
        eapply Indexed_mono; [intros; left; eassumption|apply LowRow_rules; lia].
      * rewrite (proj2 (Body_at (3+n*2) (n:=n) (k:=k) ltac:(lia))).
        replace (2+k*2) with (3+(1+k*2)-2) at 2 by lia.
        eapply Indexed_mono; [intros; left; eassumption|apply HighRow_rules; lia].
Qed.

Lemma Rows_sink n rows xs : RowRules (ExitMove (3+n*2)) rows xs ->
  VisitBudget (Rows n) rows xs -> nth (4+n*2) rows []=[].
Proof. intros [EL HR] [ES HV]; apply nth_overflow; rewrite Rows_length in ES; lia. Qed.

Lemma Rows_safe n rows xs i : RowRules (ExitMove (3+n*2)) rows xs ->
  VisitBudget (Rows n) rows xs -> Balance rows i (4+n*2) -> i<>4+n*2 ->
  nth 1 xs 0<=1 /\ nth 2 xs 0<=3.
Proof.
  intros HR HV HF HI; split.
  - pose proof (VisitBudget_bound 1 HV) as HB.
    change (nth 1 xs 0<=length [3+n*2]) in HB; exact HB.
  - pose proof (Rows_sink HR HV) as HE.
    specialize (HF (4+n*2)); unfold outgoing in HF; rewrite HE, mark_self, mark_other in HF by assumption.
    cbn[length] in HF.
    destruct (incoming_witness rows (4+n*2) ltac:(lia)) as [j [HJ HJ']].
    destruct HR as [EL HR]; destruct HV as [ES HV].
    destruct (Indexed_in (HR j) HJ') as [a [HA [HD|[-> [-> _]]]]]; [|lia].
    unfold TM5.Move in HD; pose proof (TM2.Move_bound HD ltac:(rewrite Rows_length in ES; lia)); lia.
Qed.

Lemma tick_available m xs u : length xs=2+m -> nth 0 xs 0<=1 -> nth 1 xs 0<=3 ->
  exists ys v, Tick (repeat false (2+m)) false xs u ys v 0.
Proof.
  intros EL H1 H2; destruct xs as [|a [|b xs]]; cbn[length] in EL; try lia.
  change (a<=1) in H1; change (b<=3) in H2.
  destruct (Split_total false b) as [q [r HQ]]; assert (Hq : q<=1) by (inversion HQ; subst; lia).
  destruct (Scatter_total (repeat false m) xs ltac:(rewrite repeat_length; lia)) as [qs [s HS]].
  assert (HA : Half (repeat false (2+m)) 0 (a::b::xs) u (q::(qs++[u])) (a+r+s) 0).
  { apply (Half_make 0 u (qs:=q::qs) (r:=a+r+s)).
    replace (a+r+s) with (a+(r+s)) by lia; apply Scatter_cons; [apply Split_false_small; exact H1|].
    exact (Scatter_cons HQ HS). }
  destruct (@Half_front_total false (repeat false (1+m)) q (qs++[u]) (a+r+s) 1)
    as [ys [v HB]]; [pose proof (Scatter_length HS); rewrite repeat_length in *; rewrite length_app; cbn[length]; lia|
      apply Split_false_small; exact Hq|].
  exists ys,v; exact (Tick_make false HA HB).
Qed.

Lemma stack_ticks n i rows j rows' t : StackWalk i rows j rows' t ->
  forall xs u next v a, RowRules (ExitMove (3+n*2)) rows (u::xs) ->
  VisitBudget (Rows n) rows (u::xs) -> Balance rows i (4+n*2) ->
  Tick (repeat false (3+n*2)) false xs u next v 0 -> Bump i a (u::xs) (v::next) ->
  exists ys w, Ticks (repeat false (3+n*2)) false t xs u ys w /\ VisitBudget (Rows n) rows' (w::ys).
Proof.
  intro HW; induction HW as [i rows|i j k rows rows' rows'' t HP HW IH];
    intros xs u next v a HR HV HF HT HB.
  - exists xs,u; split; [constructor|assumption].
  - destruct (RowRules_pop HR HP HB) as [HD HR']; pose proof (VisitBudget_pop HV HP HB) as HV'.
    pose proof (Pop_balance HP HF) as HF'.
    destruct (Nat.eq_dec j (4+n*2)) as [HJ|HJ].
    + pose proof (Rows_sink HR' HV') as HE; rewrite <- HJ in HE.
      destruct (StackWalk_stuck HW HE) as [EJ [EN ER]]; subst.
      exists next,v; split; [eapply Ticks_cons; [exact HT|constructor]|exact HV'].
    + destruct (Rows_safe HR' HV' HF' HJ) as [H1 H2].
      destruct (Tick_length HT) as [EL EN]; rewrite repeat_length in EL.
      destruct (@tick_available (1+n*2) next v ltac:(lia) H1 H2) as [next' [v' HT']].
      destruct (TM5.Tick_route (N:=3+n*2) ltac:(lia) HT HT' HB) as [j' [a' [HD' HB']]].
      destruct HD as [HD|[_ [_ HE]]]; [|contradiction].
      pose proof (TM2.Move_functional HD HD') as ->.
      destruct (IH next v next' v' a' HR' HV' HF' HT' HB') as [ys [w [HX HY]]].
      exists ys,w; split; [eapply Ticks_cons; eassumption|assumption].
Qed.

Theorem canonical_exit n : exists xs u,
  Ticks (repeat false (3+n*2)) false (4^n*24-n-5) (repeat 0 (3+n*2)) 0 xs u /\
  u::xs=map (@length nat) (Rows n).
Proof.
  destruct (stack_exit n) as [rows' [HW HE]].
  destruct (@tick_available (1+n*2) (repeat 0 (3+n*2)) 0 ltac:(rewrite repeat_length; reflexivity)
    ltac:(rewrite nth_repeat; lia) ltac:(rewrite nth_repeat; lia)) as [next [v HT]].
  pose proof (TM5.initial_bump (N:=3+n*2) ltac:(lia) HT) as HB.
  pose proof (Rows_rules n) as HR.
  pose proof (VisitBudget_initial (Rows n)) as HV; rewrite Rows_length in HV.
  destruct (@stack_ticks n 0 (Rows n) (4+n*2) rows' (4^n*24-n-5)
    HW (repeat 0 (3+n*2)) 0 next v 0 HR HV (Rows_balance n) HT HB) as [xs [u [HX HY]]].
  exists xs,u; split; [exact HX|eapply VisitBudget_done; eassumption].
Qed.

Definition ExitBody n := 1::4::(TM5.PairValues 2 n++[4^n*8-2]).
Definition QWord n := Alt true 3++Alt true 8++Doubles 16 n++
  Alt false (4^n*16-1)++Alt false (4^n*32-1).

Lemma Body_values N n : map (@length nat) (Body N n)=TM5.PairValues 2 n.
Proof.
  induction n; [reflexivity|].
  cbn[Body]; rewrite map_app, IHn; cbn[map]; rewrite LowRow_length, HighRow_length.
  replace (S n) with (n+1) by lia; rewrite TM5.PairValues_snoc; flia.
Qed.

Lemma Rows_values n : map (@length nat) (Rows n)=(4^n*8)::ExitBody n.
Proof.
  unfold Rows, ExitBody; cbn[map]; rewrite RootRow_length, map_app, Body_values.
  cbn[map length]; rewrite LastRow_length; reflexivity.
Qed.

Theorem canonical_endpoint n :
  Ticks (repeat false (3+n*2)) false (4^n*24-n-5) (repeat 0 (3+n*2)) 0 (ExitBody n) (4^n*8).
Proof.
  destruct (canonical_exit n) as [xs [u [HT HE]]].
  rewrite Rows_values in HE; injection HE as -> ->; exact HT.
Qed.

Lemma ExitBody_word n : TM5.Word (ExitBody n) (4^n*8)=QWord n.
Proof.
  unfold TM5.Word, ExitBody, QWord.
  change (Alt true 3++Alt true 8++TM5.GWord 4 4 (TM5.PairValues 2 n++[4^n*8-2]) (4^n*8)=
    Alt true 3++Alt true 8++Doubles 16 n++Alt false (4^n*16-1)++Alt false (4^n*32-1)).
  pose proof (@TM5.GWord_exit n 2 (4^n*8) ltac:(lia)) as H.
  replace (2*4^n*4) with (4^n*8) in H by lia.
  change (2*2) with 4 in H; change (2*8) with 16 in H.
  rewrite H; flia.
Qed.
End OddCounter.

(* Short boundary signal waves. *)

Close Scope sym.

Module OddBoundary.
Definition U n := true::Alt true 4++Doubles 8 n++Alt false (4^n*8)++
  Alt true (4^n*16)++Alt false (4^n*32-3).
Definition Vtail n := Doubles 4 n++Alt false (4^n*4)++Alt true (4^n*8)++
  Alt false (4^n*16-1)++Alt false (4^n*32-1).
Definition V n := false::Vtail n.
Definition W n := Alt true 2++Doubles 4 (1+n)++Alt false (4^n*16)++Alt true (4^n*32-2).
Definition C n := true::Alt true 2++Doubles 4 (1+n)++
  Alt false (4^n*16-1)++Alt false (4^n*32-1).
Definition Dtail n := Doubles 2 (2+n)++Alt false (4^n*32-1).
Definition D n := false::Dtail n.
Definition E n := true::Alt true 2++Doubles 4 (1+n)++Alt false (4^n*16)++Alt true (4^n*32).
Definition F n := false::TM5.DWord 2 (4+n*2) [] 0.

Ltac parity_in H :=
  rewrite ?Nat.odd_sub in H by lia;
  rewrite ?Nat.odd_add, ?Nat.odd_mul in H;
  cbn[Nat.odd Nat.even andb xorb negb] in H;
  rewrite ?andb_false_r, ?andb_true_r, ?xorb_false_r, ?xorb_true_r in H;
  cbn[negb] in H.

Ltac pass_alt := match goal with
| |- Pass (Alt ?p ?l) ?a ?b (Alt ?o ?k) =>
  solve [let H := fresh in pose proof (@Pass_alt_even p k a ltac:(auto; lia)) as H;
         parity_in H; applys_eq H; flia
        |let H := fresh in pose proof (@Pass_alt_odd_I (k-1) a ltac:(lia)) as H;
         parity_in H; applys_eq H; flia
        |let H := fresh in pose proof (@Pass_alt_odd_P k a) as H;
         parity_in H; applys_eq H; flia]
end.

Lemma FlipDoubles_shift n : forall b, map negb (Doubles b n)++Alt true (b*4^n)=
  Alt true b++Doubles (b*2) n.
Proof.
  induction n; intro b; cbn[Doubles map Nat.pow]; [rewrite Nat.mul_1_r, app_nil_r; reflexivity|].
  rewrite !map_app, !Alt_flip; cbn[negb].
  replace (b*(4*4^n)) with ((b*4)*4^n) by lia.
  rewrite <- !app_assoc, IHn; flia.
Qed.

Lemma Q_pass n : exists A o, Pass (OddCounter.QWord n) 0 A o /\ o++TM5.retire A=U n.
Proof.
  assert (HP : 4^n<>0) by (apply Nat.pow_nonzero; lia).
  exists (4^n*32-4),(true::Alt true 4++Doubles 8 n++Alt false (4^n*8)++Alt true (4^n*16)); split.
  - unfold OddCounter.QWord.
    change (true::Alt true 4++Doubles 8 n++Alt false (4^n*8)++Alt true (4^n*16)) with
      (Alt true 1++Alt true 4++Doubles 8 n++Alt false (4^n*8)++Alt true (4^n*16)).
    eapply Pass_cat with (b:=2); [pass_alt|].
    eapply Pass_cat with (b:=6); [pass_alt|].
    eapply Pass_cat with (b:=4^n*8-2).
    + applys_eq (@Pass_Doubles n 8 6 ltac:(lia) ltac:(lia) eq_refl eq_refl); flia.
    + eapply Pass_cat with (b:=4^n*16-3); pass_alt.
  - unfold U, TM5.retire.
    replace (4^n*32-4) with ((4^n*16-2)*2) by lia.
    rewrite odd_0; cbn[app]; rewrite <- ?app_assoc; flia.
Qed.

Lemma U_pass n : exists A o, Pass
  (true::false::(Doubles 8 n++Alt false (4^n*8)++Alt true (4^n*16)++Alt false (4^n*32-3)))
  3 A o /\ o++TM5.retire A=V n.
Proof.
  assert (HP : 4^n<>0) by (apply Nat.pow_nonzero; lia).
  exists (4^n*32-2),(false::Doubles 4 n++Alt false (4^n*4)++Alt true (4^n*8)++Alt false (4^n*16-1)); split.
  - apply Pass_P, Pass_I; [lia|].
    eapply Pass_cat with (b:=4^n*4).
    + applys_eq (@Pass_Doubles n 4 4 ltac:(lia) ltac:(lia) eq_refl eq_refl); flia.
    + eapply Pass_cat with (b:=4^n*8); [pass_alt|].
      eapply Pass_cat with (b:=4^n*16); pass_alt.
  - unfold V, Vtail, TM5.retire.
    replace (4^n*32-2) with ((4^n*16-1)*2) by lia; rewrite odd_0; cbn[app]; rewrite <- ?app_assoc; flia.
Qed.

Lemma V_pass n : exists A o, Pass (Vtail n) 1 A o /\ o++TM5.retire A=W n.
Proof.
  assert (HP : 4^n<>0) by (apply Nat.pow_nonzero; lia).
  exists (4^n*32-3),(map negb (Doubles 2 n)++Alt true (4^n*2)++Alt false (4^n*4)++
    Alt true (4^n*8)++Alt false (4^n*16)); split.
  - unfold Vtail; eapply Pass_cat with (b:=4^n*2-1).
    + applys_eq (@Pass_Doubles_odd n 2 1 ltac:(lia) ltac:(lia) eq_refl eq_refl); flia.
    + eapply Pass_cat with (b:=4^n*4-1); [pass_alt|].
      eapply Pass_cat with (b:=4^n*8-1); [pass_alt|].
      eapply Pass_cat with (b:=4^n*16-2); pass_alt.
  - replace (4^n*2) with (2*4^n) by lia.
    rewrite !app_assoc, FlipDoubles_shift; rewrite <- !app_assoc.
    unfold W, TM5.retire; replace (4^n*32-3) with (1+(4^n*16-2)*2) by lia; rewrite odd_1.
    replace (1+n) with (n+1) by lia; rewrite Doubles_snoc, <- !app_assoc; flia.
Qed.

Lemma W_pass n : exists A o, Pass (W n) 0 A o /\ o++TM5.retire A=C n.
Proof.
  assert (HP : 4^n<>0) by (apply Nat.pow_nonzero; lia).
  exists (4^n*32-2),(true::map negb (Doubles 2 (1+n))++Alt true (4^n*8)++Alt false (4^n*16-1)); split.
  - unfold W.
    apply Pass_P, Pass_I; [lia|].
    eapply Pass_cat with (b:=4^n*8-1).
    + applys_eq (@Pass_Doubles_odd (1+n) 2 1 ltac:(lia) ltac:(lia) eq_refl eq_refl);
        cbn[Nat.pow Nat.add]; flia.
    + eapply Pass_cat with (b:=4^n*16-1); pass_alt.
  - replace (4^n*8) with (2*4^(1+n)) by (cbn[Nat.pow Nat.add]; lia).
    rewrite !app_assoc, FlipDoubles_shift; rewrite <- !app_assoc.
    unfold C, TM5.retire; replace (4^n*32-2) with ((4^n*16-1)*2) by lia; rewrite odd_0;
      cbn[app]; rewrite <- ?app_assoc; flia.
Qed.

Lemma C_pass n : exists A o, Pass (C n) 0 A o /\ o++TM5.retire A=D n.
Proof.
  assert (HP : 4^n<>0) by (apply Nat.pow_nonzero; lia).
  exists (4^n*32-2),(false::Doubles 2 (1+n)++Alt false (4^n*8)++Alt true (4^n*16)); split.
  - unfold C; apply Pass_P.
    change (false::Doubles 2 (1+n)++Alt false (4^n*8)++Alt true (4^n*16)) with
      (Alt false 1++Doubles 2 (1+n)++Alt false (4^n*8)++Alt true (4^n*16)).
    eapply Pass_cat with (b:=2); [pass_alt|].
    eapply Pass_cat with (b:=4^n*8).
    + applys_eq (@Pass_Doubles (1+n) 2 2 ltac:(lia) ltac:(lia) eq_refl eq_refl);
        cbn[Nat.pow Nat.add]; flia.
    + eapply Pass_cat with (b:=4^n*16-1); pass_alt.
  - unfold D, Dtail, TM5.retire; replace (4^n*32-2) with ((4^n*16-1)*2) by lia; rewrite odd_0.
    replace (2+n) with ((1+n)+1) by lia; rewrite Doubles_snoc; cbn[app]; rewrite <- ?app_assoc; cbn[Nat.pow Nat.add]; flia.
Qed.

Lemma D_pass n : exists A o, Pass (Dtail n) 1 A o /\ o++TM5.retire A=E n.
Proof.
  assert (HP : 4^n<>0) by (apply Nat.pow_nonzero; lia).
  exists (4^n*32-1),(true::Alt true 2++Doubles 4 (1+n)++Alt false (4^n*16)); split.
  - unfold Dtail; change (true::Alt true 2++Doubles 4 (1+n)++Alt false (4^n*16)) with
      ((true::Alt true 2++Doubles 4 (1+n))++Alt false (4^n*16)).
    eapply Pass_cat with (b:=4^n*16).
    + applys_eq (Skelet17.Pass_Doubles_head (1+n)); cbn[Nat.pow Nat.add]; flia.
    + pass_alt.
  - unfold E, TM5.retire; replace (4^n*32-1) with (1+(4^n*16-1)*2) by lia; rewrite odd_1.
    cbn[app]; rewrite <- ?app_assoc; flia.
Qed.

Lemma E_pass n : exists A o, Pass (E n) 0 A o /\ o++TM5.retire A=F n.
Proof.
  assert (HP : 4^n<>0) by (apply Nat.pow_nonzero; lia).
  exists (4^n*32),(false::Doubles 2 (1+n)++Alt false (4^n*8)++Alt true (4^n*16)); split.
  - unfold E; apply Pass_P.
    change (false::Doubles 2 (1+n)++Alt false (4^n*8)++Alt true (4^n*16)) with
      (Alt false 1++Doubles 2 (1+n)++Alt false (4^n*8)++Alt true (4^n*16)).
    eapply Pass_cat with (b:=2); [pass_alt|].
    eapply Pass_cat with (b:=4^n*8).
    + applys_eq (@Pass_Doubles (1+n) 2 2 ltac:(lia) ltac:(lia) eq_refl eq_refl);
        cbn[Nat.pow Nat.add]; flia.
    + eapply Pass_cat with (b:=4^n*16); pass_alt.
  - unfold F, TM5.retire; replace (4+n*2) with ((2+n)*2) by lia.
    rewrite TM5.DWord_even_shape; cbn[TM5.GWord]; replace (2*4^(2+n)) with (4^n*32) by (cbn[Nat.pow Nat.add]; lia).
    replace (4^n*32) with ((4^n*16)*2) by lia; rewrite odd_0; cbn[xorb].
    replace (2+n) with ((1+n)+1) by lia; rewrite Doubles_snoc; cbn[app]; rewrite <- ?app_assoc; cbn[Nat.pow Nat.add]; flia.
Qed.
Lemma Q_last n : Skelet17.LastI (OddCounter.QWord n).
Proof. rewrite <- OddCounter.ExitBody_word; apply Skelet17.Word_last. Qed.
Ltac output_last H := destruct H as [a [o [HP <-]]]; apply Skelet17.LastI_app, Skelet17.retire_last.
Lemma U_last n : Skelet17.LastI (U n).
Proof. output_last (Q_pass n). Qed.
Lemma V_last n : Skelet17.LastI (V n).
Proof. output_last (U_pass n). Qed.
Lemma W_last n : Skelet17.LastI (W n).
Proof. output_last (V_pass n). Qed.
Lemma C_last n : Skelet17.LastI (C n).
Proof. output_last (W_pass n). Qed.
Lemma D_last n : Skelet17.LastI (D n).
Proof. output_last (C_pass n). Qed.
Lemma E_last n : Skelet17.LastI (E n).
Proof. output_last (D_pass n). Qed.

Lemma Vtail_last n : Skelet17.LastI (Vtail n).
Proof.
  apply (Skelet17.LastI_suffix [false]); [|apply V_last].
  intro H; apply (f_equal (@length bool)) in H.
  unfold Vtail in H; rewrite !length_app, !Alt_length in H; cbn[length] in H; lia.
Qed.
Lemma Dtail_last n : Skelet17.LastI (Dtail n).
Proof.
  apply (Skelet17.LastI_suffix [false]); [|apply D_last].
  intro H; apply (f_equal (@length bool)) in H.
  unfold Dtail in H; rewrite length_app, Alt_length in H; cbn[length] in H; lia.
Qed.

(* TM8 makes two boundary calls in U, then returns from its flagged edge. *)
Definition Utail n := Doubles 8 n++Alt false (4^n*8)++Alt true (4^n*16)++Alt false (4^n*32-3).
Definition X n := Alt true 4++Doubles 8 n++Alt false (4^n*8)++
  Alt true (4^n*16-1)++Alt true (4^n*32-2).
Definition Xtail n := true::false::(Doubles 8 n++Alt false (4^n*8)++
  Alt true (4^n*16-1)++Alt true (4^n*32-2)).
Definition Y n := true::Alt true 4++Doubles 8 n++Alt false (4^n*8-1)++
  Alt false (4^n*16-1)++Alt false (4^n*32-1).
Definition Z n := false::TM5.Wave 2 (3+n*2) 0.

Lemma U_double_pass n : exists A o, Pass (Utail n) 3 A o /\ o++TM5.retire A=X n.
Proof.
  assert (HP : 4^n<>0) by (apply Nat.pow_nonzero; lia).
  exists (4^n*32-3),(map negb (Doubles 4 n)++Alt true (4^n*4)++Alt false (4^n*8)++Alt true (4^n*16-1)); split.
  - unfold Utail; eapply Pass_cat with (b:=4^n*4-1).
    + applys_eq (@Pass_Doubles_odd n 4 3 ltac:(lia) ltac:(lia) eq_refl eq_refl); flia.
    + eapply Pass_cat with (b:=4^n*8-1); [pass_alt|].
      eapply Pass_cat with (b:=4^n*16-1); pass_alt.
  - replace (4^n*4) with (4*4^n) by lia.
    rewrite !app_assoc, FlipDoubles_shift; rewrite <- !app_assoc.
    unfold X, TM5.retire; replace (4^n*32-3) with (1+(4^n*16-2)*2) by lia; rewrite odd_1; flia.
Qed.

Lemma X_pass n : exists A o, Pass (Xtail n) 2 A o /\ o++TM5.retire A=Y n.
Proof.
  assert (HP : 4^n<>0) by (apply Nat.pow_nonzero; lia).
  exists (4^n*32-2),(true::map negb (Doubles 4 n)++Alt true (4^n*4)++
    Alt false (4^n*8-1)++Alt false (4^n*16-1)); split.
  - unfold Xtail; apply Pass_P, Pass_I; [lia|].
    eapply Pass_cat with (b:=4^n*4-1).
    + applys_eq (@Pass_Doubles_odd n 4 3 ltac:(lia) ltac:(lia) eq_refl eq_refl); flia.
    + eapply Pass_cat with (b:=4^n*8-1); [pass_alt|].
      eapply Pass_cat with (b:=4^n*16-1); pass_alt.
  - replace (4^n*4) with (4*4^n) by lia.
    rewrite !app_assoc, FlipDoubles_shift; rewrite <- !app_assoc.
    unfold Y, TM5.retire; replace (4^n*32-2) with ((4^n*16-1)*2) by lia; rewrite odd_0.
    cbn[app]; rewrite <- ?app_assoc; flia.
Qed.

Lemma Y_pass n : exists A o, Pass (Y n) 1 A o /\ o++TM5.retire A=W n.
Proof.
  assert (HP : 4^n<>0) by (apply Nat.pow_nonzero; lia).
  exists (4^n*32-3),(Alt true 2++Doubles 4 n++Alt false (4^n*4)++Alt true (4^n*8)++Alt false (4^n*16)); split.
  - unfold Y; apply Pass_P.
    eapply Pass_cat with (b:=4); [pass_alt|].
    eapply Pass_cat with (b:=4^n*4).
    + applys_eq (@Pass_Doubles n 4 4 ltac:(lia) ltac:(lia) eq_refl eq_refl); flia.
    + eapply Pass_cat with (b:=4^n*8-1); [pass_alt|].
      eapply Pass_cat with (b:=4^n*16-2); pass_alt.
  - unfold W, TM5.retire; replace (4^n*32-3) with (1+(4^n*16-2)*2) by lia; rewrite odd_1.
    replace (1+n) with (n+1) by lia; rewrite Doubles_snoc, <- !app_assoc; flia.
Qed.

Lemma Wave_odd_shape n : forall b, TM5.Wave b (1+n*2) 0=
  Doubles b n++Alt false (b*4^n)++Alt true (b*4^n*2-1)++Alt true (b*4^n*4).
Proof.
  induction n; intro b.
  - change (Alt false b++(Alt true (b*2-1)++Alt true (b*2*2)++[])=
      []++Alt false (b*1)++Alt true (b*1*2-1)++Alt true (b*1*4)).
    rewrite Nat.mul_1_r, app_nil_r; cbn[app]; rewrite <- ?app_assoc; flia.
  - replace (1+S n*2) with (3+n*2) by lia.
    change (TM5.Wave b (3+n*2) 0) with
      (Alt (negb (Nat.odd (3+n*2))) b++Alt (negb (Nat.odd (2+n*2))) (b*2)++TM5.Wave (b*2*2) (1+n*2) 0).
    replace (3+n*2) with (1+(1+n)*2) by lia; replace (2+n*2) with ((1+n)*2) by lia.
    rewrite odd_1, odd_0; cbn[negb]; rewrite IHn.
    cbn[Doubles Nat.pow]; rewrite <- !app_assoc; flia.
Qed.

Lemma W_one_pass n : exists A o, Pass (W n) 1 A o /\ o++TM5.retire A=Z n.
Proof.
  assert (HP : 4^n<>0) by (apply Nat.pow_nonzero; lia).
  exists (4^n*32-1),(false::Doubles 2 (1+n)++Alt false (4^n*8)++Alt true (4^n*16-1)); split.
  - unfold W; change (false::Doubles 2 (1+n)++Alt false (4^n*8)++Alt true (4^n*16-1)) with
      (Alt false 1++Doubles 2 (1+n)++Alt false (4^n*8)++Alt true (4^n*16-1)).
    eapply Pass_cat with (b:=2); [pass_alt|].
    eapply Pass_cat with (b:=4^n*8).
    + applys_eq (@Pass_Doubles (1+n) 2 2 ltac:(lia) ltac:(lia) eq_refl eq_refl);
        cbn[Nat.pow Nat.add]; flia.
    + eapply Pass_cat with (b:=4^n*16); pass_alt.
  - unfold Z, TM5.retire; replace (4^n*32-1) with (1+(4^n*16-1)*2) by lia; rewrite odd_1.
    replace (3+n*2) with (1+(1+n)*2) by lia; rewrite Wave_odd_shape.
    cbn[app]; rewrite <- ?app_assoc; cbn[Nat.pow Nat.add]; flia.
Qed.

Lemma X_last n : Skelet17.LastI (X n).
Proof. output_last (U_double_pass n). Qed.
Lemma Y_last n : Skelet17.LastI (Y n).
Proof. output_last (X_pass n). Qed.
Lemma Utail_last n : Skelet17.LastI (Utail n).
Proof.
  apply (Skelet17.LastI_suffix [true;true;false;true;false]); [|apply U_last].
  intro H; apply (f_equal (@length bool)) in H.
  unfold Utail in H; rewrite !length_app, !Alt_length in H; cbn[length] in H; lia.
Qed.
Lemma Xtail_last n : Skelet17.LastI (Xtail n).
Proof. apply (Skelet17.LastI_suffix [true;false]); [discriminate|apply X_last]. Qed.

Lemma Ladder_last n : forall b, Nat.odd b=false -> Skelet17.LastI (Ladder false b (1+n)).
Proof.
  induction n; intros b Hb.
  - change (Skelet17.LastI (Alt false (1+b)++[])); rewrite app_nil_r, <- Hb.
    apply Skelet17.retire_last.
  - change (Skelet17.LastI (Alt false (1+b)++Ladder false (b*2) (1+n))).
    apply Skelet17.LastI_app, IHn, odd_0.
Qed.

Lemma Wave_last r : forall b k, b<>0 -> Nat.odd b=false -> Skelet17.LastI (TM5.Wave b r k).
Proof.
  induction r; intros b k Hb Eb; cbn[TM5.Wave].
  - apply Skelet17.LastI_app; destruct k.
    + cbn[Ladder]; rewrite app_nil_r.
      applys_eq (Skelet17.Alt_counter_last 1 0 (b-1)); flia.
    + apply Skelet17.LastI_app, Ladder_last.
      replace (b*4) with ((b*2)*2) by lia; apply odd_0.
  - apply Skelet17.LastI_app, IHr; [lia|apply odd_0].
Qed.

Lemma GWord_zeros n : forall b, Nat.odd b=false ->
  TM5.GWord b 0 (repeat 0 n) 0=Ladder false b (1+n).
Proof.
  induction n; intros b Hb; cbn[TM5.GWord repeat Ladder Nat.add]; rewrite Hb; cbn[xorb Nat.odd].
  - rewrite app_nil_r; flia.
  - rewrite IHn by apply odd_0; flia.
Qed.

Lemma Word_zeros n : TM5.Word (repeat 0 n) 0=Alt true 2++Ladder false 2 n.
Proof.
  destruct n; [reflexivity|].
  change (Alt true 2++TM5.GWord 2 0 (repeat 0 n) 0=Alt true 2++Ladder false 2 (1+n)).
  rewrite GWord_zeros by reflexivity; reflexivity.
Qed.
End OddBoundary.

(* Odd-dimensional counters as complete column lifetimes. *)

Close Scope sym.

Module OddFlow.
Section Cut.
Variable F : Type.
Variable Edge : nat -> list nat -> F -> nat -> list nat -> F -> Prop.

Lemma internal_cut w a xs f b o : xs<>[] -> Pass w a b o -> Skelet17.LastI w ->
  Frontier_Life Edge Skelet17.retire (Skelet17.cut w) (a::xs) f
    (Skelet17.cut (o++TM5.retire b)) xs f.
Proof.
  intros HN HP [u ->]; destruct (Skelet17.Pass_cut u HP) as [q [HQ EQ]].
  rewrite <- EQ, !Skelet17.cut_snoc; constructor; assumption.
Qed.

Lemma border_cut k u a xs f b kids g c o : Edge (a+k) xs f b kids g ->
  Pass u b c o -> Skelet17.LastI u ->
  Frontier_Life Edge Skelet17.retire (Skelet17.cut (repeat true k++false::u)) (a::xs) f
    (Skelet17.cut (o++TM5.retire c)) kids g.
Proof.
  intros HE HP [w ->]; destruct (Skelet17.Pass_cut w HP) as [q [HQ EQ]].
  replace (repeat true k++false::(w++[false])) with
    ((repeat true k++false::w)++[false]) by (rewrite <- app_assoc; reflexivity).
  rewrite <- EQ, !Skelet17.cut_snoc; eapply Frontier_Life_border; eassumption.
Qed.

Lemma double_cut k j u a xs f b mid g c kids h d o : Edge (a+k) xs f b mid g ->
  Edge (b+j) mid g c kids h -> Pass u c d o -> Skelet17.LastI u ->
  Frontier_Life Edge Skelet17.retire
    (Skelet17.cut (repeat true k++false::(repeat true j++false::u))) (a::xs) f
    (Skelet17.cut (o++TM5.retire d)) kids h.
Proof.
  intros HE HE' HP [w ->]; destruct (Skelet17.Pass_cut w HP) as [q [HQ EQ]].
  replace (repeat true k++false::(repeat true j++false::(w++[false]))) with
    ((repeat true k++false::(repeat true j++false::w))++[false])
    by (rewrite <- !app_assoc; cbn[app]; rewrite <- !app_assoc; reflexivity).
  rewrite <- EQ, !Skelet17.cut_snoc; eapply Frontier_Life_double; eassumption.
Qed.
End Cut.

Section Common.
Variable F : Type.
Variable Edge : nat -> list nat -> F -> nat -> list nat -> F -> Prop.
Variable f : F.
Hypothesis Edge_even : forall a, Edge (a*2) [] f (1+a*2) [0;0] f.
Notation Life := (Frontier_Life Edge Skelet17.retire).
Notation Lives := (Frontier_Lives Edge Skelet17.retire).

Lemma Life_even w xs v ys : Flow_Life Skelet17.Edge Skelet17.retire w xs v ys ->
  ys<>[1;0;0] -> Life w xs f v ys f.
Proof.
  intros H HY; destruct H; [apply Frontier_Life_internal; assumption|].
  eapply Frontier_Life_border; [|eassumption].
  destruct H; [apply Edge_even|contradiction HY; reflexivity].
Qed.

Lemma internal_column xs qs r u : Scatter (repeat false (length xs)) xs (0::qs) r ->
  Life (Skelet17.Word xs u) [0;0] f (Skelet17.cut (true::TM5.Word (qs++[u]) r)) [0] f.
Proof. intro H; apply Life_even; [apply Skelet17.internal_column; exact H|discriminate]. Qed.

Lemma parent_column xs qs r u : Scatter (repeat false (length xs)) xs (0::qs) r ->
  Life (Skelet17.cut (true::TM5.Word xs u)) [0] f (Skelet17.Word (qs++[u]) (1+r)) [0;0] f.
Proof. intro H; apply Life_even; [apply Skelet17.parent_column; exact H|discriminate]. Qed.

Lemma Tick_lives N xs u ys v : Tick (repeat false N) false xs u ys v 0 ->
  Lives 2 (Skelet17.Word xs u) [0;0] f (Skelet17.Word ys v) [0;0] f.
Proof.
  intro H; inversion H as [xs0 u0 mid root ys0 v0 a b H1 H2]; subst.
  assert (a=0 /\ b=0) as [-> ->] by lia.
  destruct (Half_length H1) as [EL EM]; rewrite repeat_length in EL.
  destruct (Half_length H2) as [EL' _]; rewrite repeat_length in EL'.
  rewrite <- EL in H1; rewrite <- EL' in H2; clear EL EL' EM.
  inversion H1; subst; inversion H2; subst.
  eapply Frontier_Lives_cons; [apply internal_column; eassumption|].
  eapply Frontier_Lives_cons; [apply parent_column; eassumption|constructor].
Qed.

Lemma Ticks_lives N t xs u ys v : Ticks (repeat false N) false t xs u ys v ->
  Lives (t*2) (Skelet17.Word xs u) [0;0] f (Skelet17.Word ys v) [0;0] f.
Proof.
  intro H; induction H; [constructor|].
  replace ((1+n)*2) with (2+n*2) by lia.
  eapply Frontier_Lives_app; [apply (Tick_lives N); eassumption|assumption].
Qed.

Theorem canonical_word n : Lives ((4^n*24-n-5)*2)
  (Skelet17.Word (repeat 0 (3+n*2)) 0) [0;0] f (Skelet17.cut (OddCounter.QWord n)) [0;0] f.
Proof.
  rewrite <- OddCounter.ExitBody_word; apply (Ticks_lives (3+n*2)), OddCounter.canonical_endpoint.
Qed.

Lemma DWord_zero_step r N : Life
  (Skelet17.cut (Nat.odd (1+r)::TM5.DWord 2 (1+r) (repeat 0 N) 0))
    (if Nat.odd (1+r) then [0;0] else [0]) f
  (Skelet17.cut (Nat.odd r::TM5.DWord 2 r (repeat 0 (1+N)) 0))
    (if Nat.odd r then [0;0] else [0]) f.
Proof.
  apply Life_even; [apply Skelet17.DWord_zero_step|destruct (Nat.odd r); discriminate].
Qed.

Theorem DWord_zeros r : forall N, Lives (1+r)
  (Skelet17.cut (Nat.odd r::TM5.DWord 2 r (repeat 0 N) 0))
    (if Nat.odd r then [0;0] else [0]) f
  (Skelet17.Word (repeat 0 (1+r+N)) 0) [0;0] f.
Proof.
  induction r; intro N.
  - pose proof (Skelet17.DWord_zeros 0 N) as H.
    inversion H; subst.
    match goal with H : Flow_Lives _ _ 0 _ _ _ _ |- _ => inversion H; subst end.
    eapply Frontier_Lives_cons; [apply Life_even; [eassumption|discriminate]|constructor].
  - eapply Frontier_Lives_cons; [apply DWord_zero_step|].
    applys_eq (IHr (1+N)); flia.
Qed.
End Common.
End OddFlow.

(* Machine TM1. *)

Open Scope sym.


Module TM1.
Definition tm := Eval compute in (TM_from_str "1RB1LC_1RC---_0LD1RE_0LA1LD_0RC1RF_0LF0RB").
Notation "c -->* c'" := (c -[tm]->* c') (at level 40).
Notation "c -->+ c'" := (c -[tm]->+ c') (at level 40).
Notation LC := Skelet17.LC.
Definition S1 xs n := LC xs {{C}}> [1;0]^^n *> 0inf.
Definition QL (p:bool) := if p then C else D.

Inductive Edge : nat -> list nat -> unit -> nat -> list nat -> unit -> Prop :=
| Edge_even a : Edge (a*2) [] tt (1+a*2) [0;0]%nat tt
| Edge_zeros : Edge 0%nat [0]%nat tt 1%nat [0;0;0]%nat tt.
Notation LInc := (Frontier_LInc Edge).
Notation Run := (Frontier_Run Edge).
Definition retire := Skelet17.retire.

Lemma Edge_size a xs f b kids g : Edge a xs f b kids g -> length kids<=3.
Proof. intro H; destruct H; cbn; lia. Qed.

Lemma LInc_spec p xs f ys g : LInc p xs f ys g ->
  forall r, LC xs <{{QL p}} [1;0] *> r -->* LC ys {{C}}> r.
Proof.
  intro H; induction H; intro r.
  - cbn[Skelet17.LC QL]; es.
  - destruct (mod2 a) as [k EQ|k EQ]; subst a.
    + rewrite odd_0 in IHFrontier_LInc; destruct k as [|k]; [lia|].
      replace (S k*2) with (2+k*2) by lia.
      cbn[Skelet17.LC QL] in *; es; er; follow IHFrontier_LInc; es.
    + rewrite odd_1 in IHFrontier_LInc; cbn[Skelet17.LC QL] in *.
      es; er; follow IHFrontier_LInc; es.
  - destruct H; cbn[Skelet17.LC QL]; es.
Qed.

Lemma Inc_right n xs f ys g : LInc (negb (Nat.odd n)) xs f ys g ->
  S1 xs (1+n) -->* S1 ys n.
Proof.
  intro H; destruct (mod2 n) as [a EQ|a EQ]; subst n.
  - rewrite odd_0 in H; eapply LInc_spec in H; es; er; follow H; finish.
  - rewrite odd_1 in H; eapply LInc_spec in H; es; er; follow H; finish.
Qed.

Lemma Inc_zero a xs f ys g : LInc (Nat.odd a) xs f ys g ->
  S1 (a::xs) 0 -->+ S1 ys a.
Proof.
  intro H; destruct (mod2 a) as [k EQ|k EQ]; subst a.
  - rewrite odd_0 in H; eapply LInc_spec in H; unfold S1; cbn[Skelet17.LC].
    es; er; follow H; finish.
  - rewrite odd_1 in H; eapply LInc_spec in H; unfold S1; cbn[Skelet17.LC].
    es; er; follow H; finish.
Qed.

Lemma init : c0 -->* S1 [4;1;0]%nat 0.
Proof. unfold S1; esx. Qed.

Close Scope sym.
Lemma Edge_functional a xs f b kids g c kids' h :
  Edge a xs f b kids g -> Edge a xs f c kids' h -> b=c /\ kids=kids' /\ g=h.
Proof. intros H H'; destruct H; inversion H'; subst; repeat split; f_equal; lia. Qed.

Lemma Edge_no_pass a xs f b kids g : Edge a xs f b kids g -> forall ys h,
  a<>0 -> LInc (Nat.odd a) xs f ys h -> False.
Proof. intros H ys h HA HL; destruct H; [inversion HL|contradiction]. Qed.

Lemma LInc_functional p xs f ys g zs h : LInc p xs f ys g ->
  LInc p xs f zs h -> ys=zs /\ g=h.
Proof.
  intro H; revert zs h; induction H; intros zs h HZ; inversion HZ; subst; auto.
  - match goal with H : LInc (Nat.odd a) _ _ _ _ |- _ =>
      destruct (IHFrontier_LInc _ _ H); subst; auto end.
  - exfalso; eapply Edge_no_pass; eassumption.
  - exfalso; eapply Edge_no_pass; eassumption.
  - match goal with H1 : Edge ?a ?xs ?f ?b ?kids ?g, H2 : Edge ?a ?xs ?f ?c ?kids' ?h |- _ =>
      destruct (Edge_functional H1 H2) as [-> [-> ->]]; auto end.
Qed.

Lemma Run_right n xs f ys g : Run (Alt (Nat.odd n) n) xs f ys g ->
  S1 xs n -->* S1 ys 0.
Proof.
  revert xs f; induction n; intros xs f H.
  - inversion H; subst; apply evstep_refl.
  - cbn[Alt] in H; rewrite odd_S, negb_involutive in H.
    inversion H as [|p w source f0 cut g0 target h0 HL HR]; subst.
    follow (Inc_right n HL); eapply IHn; eassumption.
Qed.

Lemma Macro_spec xs f ys g : Frontier_Macro Edge retire xs f ys g ->
  S1 xs 0 -->+ S1 ys 0.
Proof.
  intro H; destruct H; cbn[retire Skelet17.retire] in H.
  inversion H as [|p w source f0 cut g0 target h0 HL HR]; subst.
  follow10 (Inc_zero a HL); eapply Run_right; eassumption.
Qed.

Theorem nonhalt_from_lives : Frontier_InfiniteLife Edge retire [] [4;1;0] tt -> ~halts tm c0.
Proof.
  intro H; eapply multistep_nonhalt; [apply init|].
  assert (HI : Frontier_InfiniteMacro Edge retire [4;1;0] tt).
  { eapply (Frontier_InfiniteLife_sound Edge_size LInc_functional); [exact H|constructor]. }
  eapply progress_nonhalt with (P:=fun c => exists xs f,
    Frontier_InfiniteMacro Edge retire xs f /\ c=S1 xs 0).
  - intros c [xs [f [HX ->]]]; destruct HX as [xs f ys g HM HX].
    exists (S1 ys 0); split; [exists ys,g; auto|apply Macro_spec in HM; exact HM].
  - exists [4;1;0],tt; auto.
Qed.

Ltac pass_constant := cbn[retire Skelet17.retire Alt List.app Nat.odd Nat.even negb Nat.add];
  repeat first [apply Pass_nil | apply Pass_P | apply Pass_I; [discriminate|]].
Ltac internal_constant := eapply Frontier_Lives_cons;
  [eapply Frontier_Life_internal; [discriminate|pass_constant]|].
Ltac terminal_constant prefix value := eapply Frontier_Lives_cons;
  [eapply Frontier_Life_border with (k:=prefix) (b:=value);
    [let n := eval compute in ((value-1)/2) in apply (Edge_even n)|pass_constant]|].

Lemma initial_counter : Frontier_Lives Edge retire 13 [] [4;1;0] tt
  (Skelet17.Word [0;0;0] 0) [0;0] tt.
Proof.
  internal_constant; internal_constant.
  terminal_constant 2 3; internal_constant; terminal_constant 2 3.
  eapply Frontier_Lives_cons;
    [eapply Frontier_Life_border with (k:=0) (b:=1); [apply Edge_zeros|pass_constant]|].
  internal_constant; internal_constant; terminal_constant 0 1.
  internal_constant; terminal_constant 0 1; internal_constant; terminal_constant 0 1.
  cbn[Skelet17.Word Skelet17.cut TM5.Word TM5.GWord Alt List.app removelast Nat.add Nat.odd Nat.even negb].
  constructor.
Qed.
Notation Life := (Frontier_Life Edge retire).
Notation Lives := (Frontier_Lives Edge retire).

Ltac cut_internal pass last :=
  destruct pass as [a [o [HP HE]]]; rewrite <- HE;
  eapply OddFlow.internal_cut; [discriminate|exact HP|apply last].

Lemma Q_to_U n : Life (Skelet17.cut (OddCounter.QWord n)) [0;0] tt
  (Skelet17.cut (OddBoundary.U n)) [0] tt.
Proof. cut_internal (OddBoundary.Q_pass n) OddBoundary.Q_last. Qed.

Lemma U_to_V n : Life (Skelet17.cut (OddBoundary.U n)) [0] tt
  (Skelet17.cut (OddBoundary.V n)) [0;0] tt.
Proof.
  destruct (OddBoundary.U_pass n) as [a [o [HP HE]]]; rewrite <- HE.
  match type of HP with Pass ?u _ _ _ =>
    change (OddBoundary.U n) with (repeat true 2++false::u)
  end.
  eapply OddFlow.border_cut; [apply (Edge_even 1)|exact HP|].
  apply (Skelet17.LastI_suffix [true;true;false]); [discriminate|apply OddBoundary.U_last].
Qed.

Lemma V_to_W n : Life (Skelet17.cut (OddBoundary.V n)) [0;0] tt
  (Skelet17.cut (OddBoundary.W n)) [0;0;0] tt.
Proof.
  destruct (OddBoundary.V_pass n) as [a [o [HP HE]]]; rewrite <- HE.
  eapply OddFlow.border_cut with (k:=0); [apply Edge_zeros|exact HP|apply OddBoundary.Vtail_last].
Qed.

Lemma W_to_C n : Life (Skelet17.cut (OddBoundary.W n)) [0;0;0] tt
  (Skelet17.cut (OddBoundary.C n)) [0;0] tt.
Proof. cut_internal (OddBoundary.W_pass n) OddBoundary.W_last. Qed.
Lemma C_to_D n : Life (Skelet17.cut (OddBoundary.C n)) [0;0] tt
  (Skelet17.cut (OddBoundary.D n)) [0] tt.
Proof. cut_internal (OddBoundary.C_pass n) OddBoundary.C_last. Qed.
Lemma D_to_E n : Life (Skelet17.cut (OddBoundary.D n)) [0] tt
  (Skelet17.cut (OddBoundary.E n)) [0;0] tt.
Proof.
  destruct (OddBoundary.D_pass n) as [a [o [HP HE]]]; rewrite <- HE.
  eapply OddFlow.border_cut with (k:=0); [apply (Edge_even 0)|exact HP|apply OddBoundary.Dtail_last].
Qed.
Lemma E_to_F n : Life (Skelet17.cut (OddBoundary.E n)) [0;0] tt
  (Skelet17.cut (OddBoundary.F n)) [0] tt.
Proof. cut_internal (OddBoundary.E_pass n) OddBoundary.E_last. Qed.

Theorem Q_front n : Lives 7 (Skelet17.cut (OddCounter.QWord n)) [0;0] tt
  (Skelet17.cut (OddBoundary.F n)) [0] tt.
Proof.
  eapply Frontier_Lives_cons; [apply Q_to_U|].
  eapply Frontier_Lives_cons; [apply U_to_V|].
  eapply Frontier_Lives_cons; [apply V_to_W|].
  eapply Frontier_Lives_cons; [apply W_to_C|].
  eapply Frontier_Lives_cons; [apply C_to_D|].
  eapply Frontier_Lives_cons; [apply D_to_E|].
  eapply Frontier_Lives_cons; [apply E_to_F|constructor].
Qed.

Theorem Q_to_zero n : Lives (12+n*2) (Skelet17.cut (OddCounter.QWord n)) [0;0] tt
  (Skelet17.Word (repeat 0 (5+n*2)) 0) [0;0] tt.
Proof.
  pose proof (@OddFlow.DWord_zeros unit Edge tt Edge_even (4+n*2) 0) as H.
  replace (4+n*2) with ((2+n)*2) in H by lia; rewrite odd_0 in H.
  replace (12+n*2) with (7+(5+n*2)) by lia.
  eapply Frontier_Lives_app; [apply Q_front|].
  unfold OddBoundary.F; applys_eq H; flia.
Qed.

Theorem zero_round n : Lives (4^n*48+2) (Skelet17.Word (repeat 0 (3+n*2)) 0) [0;0] tt
  (Skelet17.Word (repeat 0 (3+(1+n)*2)) 0) [0;0] tt.
Proof.
  pose proof (OddCounter.Body_budget (3+n*2) n).
  replace (4^n*48+2) with ((4^n*24-n-5)*2+(12+n*2)) by lia.
  eapply Frontier_Lives_app; [apply (@OddFlow.canonical_word unit Edge tt Edge_even)|].
  applys_eq (Q_to_zero n); flia.
Qed.

Lemma zero_suffix_infinite : forall n t w xs f,
  Lives t w xs f (Skelet17.Word (repeat 0 (3+n*2)) 0) [0;0] tt ->
  Frontier_InfiniteLife Edge retire w xs f.
Proof.
  cofix IH; intros n t w xs f H; destruct t.
  - inversion H; subst; pose proof (zero_round n) as HR.
    replace (4^n*48+2) with (1+(4^n*48+1)) in HR by lia.
    inversion HR; subst; econstructor; [eassumption|eapply (IH (1+n) (4^n*48+1)); eassumption].
  - inversion H; subst; econstructor; [eassumption|eapply (IH n t); eassumption].
Qed.

Theorem nonhalt : ~halts tm c0.
Proof. apply nonhalt_from_lives; eapply (zero_suffix_infinite 0); exact initial_counter. Qed.
End TM1.

(* Machine TM8. *)

Open Scope sym.


Module TM8.
Definition tm := Eval compute in (TM_from_str "1RB1LC_1RC0RF_0LD1RE_0LA1LD_0RC0RB_0RE---").
Notation "c -->* c'" := (c -[tm]->* c') (at level 40).
Notation "c -->+ c'" := (c -[tm]->+ c') (at level 40).
Fixpoint LC (xs:list nat) (f:bool) := match xs with
  | [] => if f then 0inf <* <[1;1;1;0;0;0;0] else 0inf
  | a::xs => LC xs f <* <[1;0]^^a <* <[1] end.
Definition S1 xs f n := LC xs f {{C}}> [1;0]^^n *> 0inf.
Definition QL (p:bool) := if p then C else D.

Inductive Edge : nat -> list nat -> bool -> nat -> list nat -> bool -> Prop :=
| Edge_even a : Edge (a*2) [] false (1+a*2) [0;0]%nat false
| Edge_odd a : Edge (1+a*2) [] false (2+a*2) [1;0;0]%nat false
| Edge_cut a : Edge (2+a*2) [0;0]%nat false (1+a*2) [0]%nat true
| Edge_return a : Edge (1+a*2) [] true (2+a*2) [1;1;0]%nat false.
Notation LInc := (Frontier_LInc Edge).
Notation Run := (Frontier_Run Edge).
Definition retire := Skelet17.retire.

Lemma Edge_size a xs f b kids g : Edge a xs f b kids g -> length kids<=3.
Proof. intro H; destruct H; cbn; lia. Qed.

Lemma LInc_spec p xs f ys g : LInc p xs f ys g ->
  forall r, LC xs f <{{QL p}} [1;0] *> r -->* LC ys g {{C}}> r.
Proof.
  intro H; induction H; intro r.
  - cbn[LC QL]; es.
  - destruct (mod2 a) as [k EQ|k EQ]; subst a.
    + rewrite odd_0 in IHFrontier_LInc; destruct k as [|k]; [lia|].
      replace (S k*2) with (2+k*2) by lia.
      cbn[LC QL] in *; es; er; follow IHFrontier_LInc; es.
    + rewrite odd_1 in IHFrontier_LInc; cbn[LC QL] in *.
      es; er; follow IHFrontier_LInc; es.
  - destruct H; cbn[LC QL]; es.
Qed.

Lemma Inc_right n xs f ys g : LInc (negb (Nat.odd n)) xs f ys g ->
  S1 xs f (1+n) -->* S1 ys g n.
Proof.
  intro H; destruct (mod2 n) as [a EQ|a EQ]; subst n.
  - rewrite odd_0 in H; eapply LInc_spec in H; es; er; follow H; finish.
  - rewrite odd_1 in H; eapply LInc_spec in H; es; er; follow H; finish.
Qed.

Lemma Inc_zero a xs f ys g : LInc (Nat.odd a) xs f ys g ->
  S1 (a::xs) f 0 -->+ S1 ys g a.
Proof.
  intro H; destruct (mod2 a) as [k EQ|k EQ]; subst a.
  - rewrite odd_0 in H; eapply LInc_spec in H; unfold S1; cbn[LC].
    es; er; follow H; finish.
  - rewrite odd_1 in H; eapply LInc_spec in H; unfold S1; cbn[LC].
    es; er; follow H; finish.
Qed.

Lemma init : c0 -->* S1 [2;2]%nat false 0.
Proof. unfold S1; esx. Qed.

Close Scope sym.
Lemma Edge_functional a xs f b kids g c kids' h :
  Edge a xs f b kids g -> Edge a xs f c kids' h -> b=c /\ kids=kids' /\ g=h.
Proof. intros H H'; destruct H; inversion H'; subst; repeat split; f_equal; lia. Qed.

Lemma Edge_no_pass a xs f b kids g : Edge a xs f b kids g -> forall ys h,
  a<>0 -> LInc (Nat.odd a) xs f ys h -> False.
Proof.
  intros H ys h HA HL; destruct H; try (inversion HL; fail).
  replace (2+a*2) with ((1+a)*2) in HL by lia; rewrite odd_0 in HL.
  inversion HL; subst; [lia|].
  match goal with H : Edge 0 [0] _ _ _ _ |- _ => inversion H end.
Qed.

Lemma LInc_functional p xs f ys g zs h : LInc p xs f ys g ->
  LInc p xs f zs h -> ys=zs /\ g=h.
Proof.
  intro H; revert zs h; induction H; intros zs h HZ; inversion HZ; subst; auto.
  - match goal with H : LInc (Nat.odd a) _ _ _ _ |- _ =>
      destruct (IHFrontier_LInc _ _ H); subst; auto end.
  - exfalso; eapply Edge_no_pass; eassumption.
  - exfalso; eapply Edge_no_pass; eassumption.
  - match goal with H1 : Edge ?a ?xs ?f ?b ?kids ?g, H2 : Edge ?a ?xs ?f ?c ?kids' ?h |- _ =>
      destruct (Edge_functional H1 H2) as [-> [-> ->]]; auto end.
Qed.

Lemma Run_right n xs f ys g : Run (Alt (Nat.odd n) n) xs f ys g ->
  S1 xs f n -->* S1 ys g 0.
Proof.
  revert xs f; induction n; intros xs f H.
  - inversion H; subst; apply evstep_refl.
  - cbn[Alt] in H; rewrite odd_S, negb_involutive in H.
    inversion H as [|p w source f0 cut g0 target h0 HL HR]; subst.
    follow (Inc_right n HL); eapply IHn; eassumption.
Qed.

Lemma Macro_spec xs f ys g : Frontier_Macro Edge retire xs f ys g ->
  S1 xs f 0 -->+ S1 ys g 0.
Proof.
  intro H; destruct H; cbn[retire Skelet17.retire] in H.
  inversion H as [|p w source f0 cut g0 target h0 HL HR]; subst.
  follow10 (Inc_zero a HL); eapply Run_right; eassumption.
Qed.

Theorem nonhalt_from_lives : Frontier_InfiniteLife Edge retire [] [2;2] false -> ~halts tm c0.
Proof.
  intro H; eapply multistep_nonhalt; [apply init|].
  assert (HI : Frontier_InfiniteMacro Edge retire [2;2] false).
  { eapply (Frontier_InfiniteLife_sound Edge_size LInc_functional); [exact H|constructor]. }
  eapply progress_nonhalt with (P:=fun c => exists xs f,
    Frontier_InfiniteMacro Edge retire xs f /\ c=S1 xs f 0).
  - intros c [xs [f [HX ->]]]; destruct HX as [xs f ys g HM HX].
    exists (S1 ys g 0); split; [exists ys,g; auto|apply Macro_spec in HM; exact HM].
  - exists [2;2],false; auto.
Qed.

Ltac pass_constant := cbn[retire Skelet17.retire Alt List.app Nat.odd Nat.even negb Nat.add];
  repeat first [apply Pass_nil | apply Pass_P | apply Pass_I; [discriminate|]].
Ltac internal_constant := eapply Frontier_Lives_cons;
  [eapply Frontier_Life_internal; [discriminate|pass_constant]|].
Ltac terminal_constant prefix value := eapply Frontier_Lives_cons;
  [eapply Frontier_Life_border with (k:=prefix) (b:=value);
    [let a := eval compute in ((value-1)/2) in
     let b := eval compute in ((value-2)/2) in
     first [apply (Edge_even a)|apply (Edge_odd b)|apply (Edge_return b)]|pass_constant]|].

Lemma initial_counter : Frontier_Lives Edge retire 13 [] [2;2] false
  (Skelet17.Word [0;0;0] 0) [0;0] false.
Proof.
  internal_constant; terminal_constant 0 3.
  internal_constant; terminal_constant 2 3; internal_constant.
  eapply Frontier_Lives_cons;
    [eapply Frontier_Life_double with (k:=2) (j:=1) (b:=3) (c:=3);
      [apply (Edge_even 1)|apply (Edge_cut 1)|pass_constant]|].
  terminal_constant 1 2; internal_constant; internal_constant.
  terminal_constant 0 1; internal_constant; terminal_constant 1 2; internal_constant.
  cbn[Skelet17.Word Skelet17.cut TM5.Word TM5.GWord Alt List.app removelast Nat.add Nat.odd Nat.even negb].
  constructor.
Qed.
Notation Life := (Frontier_Life Edge retire).
Notation Lives := (Frontier_Lives Edge retire).
Ltac cut_internal pass last :=
  destruct pass as [a [o [HP HE]]]; rewrite <- HE;
  eapply OddFlow.internal_cut; [discriminate|exact HP|apply last].

Lemma Q_to_U n : Life (Skelet17.cut (OddCounter.QWord n)) [0;0] false
  (Skelet17.cut (OddBoundary.U n)) [0] false.
Proof. cut_internal (OddBoundary.Q_pass n) OddBoundary.Q_last. Qed.
Lemma U_to_X n : Life (Skelet17.cut (OddBoundary.U n)) [0] false
  (Skelet17.cut (OddBoundary.X n)) [0] true.
Proof.
  destruct (OddBoundary.U_double_pass n) as [a [o [HP HE]]]; rewrite <- HE.
  change (OddBoundary.U n) with (repeat true 2++false::(repeat true 1++false::OddBoundary.Utail n)).
  eapply OddFlow.double_cut; [apply (Edge_even 1)|apply (Edge_cut 1)|exact HP|apply OddBoundary.Utail_last].
Qed.
Lemma X_to_Y n : Life (Skelet17.cut (OddBoundary.X n)) [0] true
  (Skelet17.cut (OddBoundary.Y n)) [1;1;0] false.
Proof.
  destruct (OddBoundary.X_pass n) as [a [o [HP HE]]]; rewrite <- HE.
  change (OddBoundary.X n) with (repeat true 1++false::OddBoundary.Xtail n).
  eapply OddFlow.border_cut; [apply (Edge_return 0)|exact HP|apply OddBoundary.Xtail_last].
Qed.
Lemma Y_to_W n : Life (Skelet17.cut (OddBoundary.Y n)) [1;1;0] false
  (Skelet17.cut (OddBoundary.W n)) [1;0] false.
Proof. cut_internal (OddBoundary.Y_pass n) OddBoundary.Y_last. Qed.
Lemma W_to_Z n : Life (Skelet17.cut (OddBoundary.W n)) [1;0] false
  (Skelet17.cut (OddBoundary.Z n)) [0] false.
Proof. cut_internal (OddBoundary.W_one_pass n) OddBoundary.W_last. Qed.

Theorem Q_front n : Lives 5 (Skelet17.cut (OddCounter.QWord n)) [0;0] false
  (Skelet17.cut (OddBoundary.Z n)) [0] false.
Proof.
  eapply Frontier_Lives_cons; [apply Q_to_U|].
  eapply Frontier_Lives_cons; [apply U_to_X|].
  eapply Frontier_Lives_cons; [apply X_to_Y|].
  eapply Frontier_Lives_cons; [apply Y_to_W|].
  eapply Frontier_Lives_cons; [apply W_to_Z|constructor].
Qed.

Definition WaveWord r k := Skelet17.cut (negb (Nat.odd r)::TM5.Wave 2 r k).
Definition WaveKids r := if Nat.odd r then [0] else [0;0].

Lemma Wave_step r k : Life (WaveWord (1+r) k) (WaveKids (1+r)) false
  (WaveWord r (1+k)) (WaveKids r) false.
Proof.
  destruct (TM5.Wave_H r k) as [a [o [HP HE]]].
  unfold WaveWord, WaveKids; rewrite odd_S in HE |- *.
  rewrite <- HE; destruct (Nat.odd r); cbn[negb].
  - eapply OddFlow.internal_cut; [discriminate|apply Pass_P; exact HP|].
    apply (Skelet17.LastI_app [true]), OddBoundary.Wave_last; discriminate || reflexivity.
  - eapply OddFlow.border_cut with (k:=0); [apply (Edge_even 0)|exact HP|].
    apply OddBoundary.Wave_last; discriminate || reflexivity.
Qed.

Lemma Wave_run r : forall k, Lives r (WaveWord r k) (WaveKids r) false
  (WaveWord 0 (k+r)) [0;0] false.
Proof.
  induction r; intro k; [rewrite Nat.add_0_r; constructor|].
  eapply Frontier_Lives_cons; [apply Wave_step|].
  applys_eq (IHr (1+k)); flia.
Qed.

Lemma Wave_zero k : Life (WaveWord 0 k) [0;0] false
  (Skelet17.cut (Alt true 2++Ladder false 4 (1+k))) [0] false.
Proof.
  destruct (TM5.Wave_zero_H k) as [a [o [HP HE]]]; rewrite <- HE.
  unfold WaveWord; eapply OddFlow.internal_cut; [discriminate|apply Pass_P; exact HP|].
  apply (Skelet17.LastI_app [true]), OddBoundary.Wave_last; discriminate || reflexivity.
Qed.

Lemma Ladder_birth k : Life (Skelet17.cut (Alt true 2++Ladder false 4 (1+k))) [0] false
  (Skelet17.cut (Ladder false 2 (2+k))) [1;0;0] false.
Proof.
  destruct (Pass_ladder_return (1+k) (t:=2) ltac:(lia)) as [a [o [HP HE]]].
  change (o++TM5.retire a=Ladder false 2 (2+k)) in HE; rewrite <- HE.
  change (Alt true 2++Ladder false 4 (1+k)) with (repeat true 1++false::Ladder false 4 (1+k)).
  eapply OddFlow.border_cut; [apply (Edge_odd 0)|exact HP|apply OddBoundary.Ladder_last; reflexivity].
Qed.

Lemma Ladder_return k : Life (Skelet17.cut (Ladder false 2 (2+k))) [1;0;0] false
  (Skelet17.Word (repeat 0 (2+k)) 0) [0;0] false.
Proof.
  destruct (Pass_ladder_return (2+k) (t:=1) ltac:(lia)) as [a [o [HP HE]]].
  change (o++TM5.retire a=Alt true 2++Ladder false 2 (2+k)) in HE.
  unfold Skelet17.Word; rewrite OddBoundary.Word_zeros, <- HE.
  eapply OddFlow.internal_cut; [discriminate|exact HP|apply OddBoundary.Ladder_last; reflexivity].
Qed.

Theorem Wave_to_zero r : Lives (r+3) (WaveWord r 0) (WaveKids r) false
  (Skelet17.Word (repeat 0 (2+r)) 0) [0;0] false.
Proof.
  eapply Frontier_Lives_app; [apply (Wave_run r 0)|].
  eapply Frontier_Lives_cons; [apply Wave_zero|].
  eapply Frontier_Lives_cons; [apply Ladder_birth|].
  eapply Frontier_Lives_cons; [apply Ladder_return|constructor].
Qed.

Theorem Q_to_zero n : Lives (11+n*2) (Skelet17.cut (OddCounter.QWord n)) [0;0] false
  (Skelet17.Word (repeat 0 (5+n*2)) 0) [0;0] false.
Proof.
  pose proof (Wave_to_zero (3+n*2)) as H.
  unfold WaveWord, WaveKids in H; replace (3+n*2) with (1+(1+n)*2) in H by lia.
  rewrite odd_1 in H; cbn[negb] in H.
  replace (11+n*2) with (5+((3+n*2)+3)) by lia.
  eapply Frontier_Lives_app; [apply Q_front|].
  unfold OddBoundary.Z; applys_eq H; flia.
Qed.

Theorem zero_round n : Lives (4^n*48+1) (Skelet17.Word (repeat 0 (3+n*2)) 0) [0;0] false
  (Skelet17.Word (repeat 0 (3+(1+n)*2)) 0) [0;0] false.
Proof.
  pose proof (OddCounter.Body_budget (3+n*2) n).
  replace (4^n*48+1) with ((4^n*24-n-5)*2+(11+n*2)) by lia.
  eapply Frontier_Lives_app; [apply (@OddFlow.canonical_word bool Edge false Edge_even)|].
  applys_eq (Q_to_zero n); flia.
Qed.

Lemma zero_suffix_infinite : forall n t w xs f,
  Lives t w xs f (Skelet17.Word (repeat 0 (3+n*2)) 0) [0;0] false ->
  Frontier_InfiniteLife Edge retire w xs f.
Proof.
  cofix IH; intros n t w xs f H; destruct t.
  - inversion H; subst; pose proof (zero_round n) as HR.
    replace (4^n*48+1) with (1+4^n*48) in HR by lia.
    inversion HR; subst; econstructor; [eassumption|eapply (IH (1+n) (4^n*48)); eassumption].
  - inversion H; subst; econstructor; [eassumption|eapply (IH n t); eassumption].
Qed.

Theorem nonhalt : ~halts tm c0.
Proof. apply nonhalt_from_lives; eapply (zero_suffix_infinite 0); exact initial_counter. Qed.
End TM8.
