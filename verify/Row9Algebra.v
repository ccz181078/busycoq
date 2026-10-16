From Coq Require Import List Arith Lia.
Import ListNotations.

(* All operator equalities are pointwise; no extensionality axiom is used. *)
Fixpoint power {A : Type} (f : A -> A) (n : nat) (x : A) : A :=
  match n with 0 => x | S n => f (power f n x) end.

Lemma power_add {A} (f:A->A) a b x :
  power f (a+b) x = power f a (power f b x).
Proof. induction a; simpl; congruence. Qed.
Lemma power_succ_r {A} (f:A->A) a x :
  power f (S a) x = power f a (f x).
Proof. induction a; simpl in *; congruence. Qed.
Lemma power_commute {A} (f g:A->A)
  (E:forall x, f(g x)=g(f x)) n x :
  power f n (g x) = g (power f n x).
Proof. induction n; simpl; [reflexivity|]. rewrite IHn,E. reflexivity. Qed.
Lemma power_ext {A} (f g:A->A) (E:forall x,f x=g x) n x :
  power f n x=power g n x.
Proof. induction n; simpl; [reflexivity|]. rewrite IHn,E. reflexivity. Qed.
Lemma power_mul {A} (f:A->A) a b x :
  power f (a*b) x = power (fun y=>power f b y) a x.
Proof. induction a; simpl; [reflexivity|]. rewrite power_add,IHa. reflexivity. Qed.
Lemma power_strict {A} (f:option A->option A) (E:f None=None) n :
  power f n None=None.
Proof. induction n; simpl; congruence. Qed.
Lemma power_halt_mono {A} (f:option A->option A) (E:f None=None) a b x :
  a<=b -> power f a x=None -> power f b x=None.
Proof. intros Hab Ha. replace b with ((b-a)+a) by lia.
  rewrite power_add,Ha. apply power_strict,E. Qed.
Lemma power_injective_none {A} (f:option A->option A)
  (E:forall x,f x=None <-> x=None) n x :
  power f n x=None <-> x=None.
Proof. induction n; simpl; [tauto|]. rewrite E,IHn. tauto. Qed.
Lemma power_product {A} (f g:A->A) (E:forall x,f(g x)=g(f x)) n x :
  power (fun y=>f(g y)) n x=power f n(power g n x).
Proof. induction n; simpl; [reflexivity|]. rewrite IHn.
  rewrite (power_commute f g E n). reflexivity. Qed.

Definition eventually {A} (f:option A->option A) x :=
  exists k, power f k x=None.
Lemma eventually_step {A} (f:option A->option A) (E:f None=None) x :
  eventually f x <-> eventually f (f x).
Proof. split; intros [k Hk].
 - exists k. rewrite <-power_succ_r. eapply (power_halt_mono f E k (S k) x); eauto; lia.
 - exists (S k). now rewrite power_succ_r.
Qed.
Lemma eventually_rotate {A} (f g:option A->option A)
  (Ef:f None=None) (Eg:g None=None) x :
  eventually (fun y=>f(g y)) x <-> eventually (fun y=>g(f y)) (g x).
Proof.
  assert (C:forall k x, power (fun y=>g(f y)) k (g x)=
       g(power (fun y=>f(g y)) k x)).
  { intros k; induction k; intros y; simpl; congruence. }
  split; intros [k E].
  - exists k. rewrite C,E,Eg. reflexivity.
  - exists (S k). rewrite power_succ_r.
    assert (D:forall k x, power (fun y=>f(g y)) k (f x)=
       f(power (fun y=>g(f y)) k x)).
    { intros j; induction j; intros y; simpl; congruence. }
    rewrite D,E,Ef. reflexivity.
Qed.

Section Algebra.
Context {A:Type}.
Variables F Q Z G : option A -> option A.
Hypotheses F_none:F None=None.
Hypotheses G_none:G None=None.
Hypotheses Q_none:forall x,Q x=None <-> x=None.
Hypotheses Z_none:forall x,Z x=None <-> x=None.
Hypotheses FQ:forall x,F(Q x)=Q(F x).
Hypotheses FZ:forall x,F(Z x)=Q(G x).
Hypotheses GQ:forall x,G(Q x)=Z(F x).

Definition phase n x := Z(power F n x).
Definition phaseG n x := G(power F n x).
Definition inert n x := Z(power Q n x).

Lemma F_power_Q n x : power F n(Q x)=Q(power F n x).
Proof. apply power_commute,FQ. Qed.
Lemma F_power_Z n x : power F (S n)(Z x)=Q(power F n(G x)).
Proof. rewrite power_succ_r,FZ,F_power_Q. reflexivity. Qed.
Lemma phaseG_Q n x : phaseG n(Q x)=phase n(F x).
Proof. unfold phaseG,phase. rewrite F_power_Q,GQ.
  now rewrite <-power_succ_r. Qed.
Lemma phaseG_phase n x : 1<=n -> phaseG n(phase n x)=phase n(phaseG n x).
Proof. intros Hn; destruct n; [lia|]. unfold phaseG,phase.
  rewrite F_power_Z,GQ. reflexivity. Qed.
Lemma phaseG_strict n : phaseG n None=None.
Proof. unfold phaseG. rewrite power_strict; auto. Qed.
Lemma phase_strict n : phase n None=None.
Proof. unfold phase. rewrite power_strict; auto. apply Z_none; reflexivity. Qed.
Lemma inert_none n x : inert n x=None <-> x=None.
Proof. unfold inert. rewrite Z_none. apply power_injective_none,Q_none. Qed.

Lemma F_Q_power k x : F(power Q k x)=power Q k(F x).
Proof. symmetry. apply power_commute. intros y; symmetry; apply FQ. Qed.
Lemma transport j l x :
 power F j(Z(power Q (j+l) x))=power Q j(Z(power Q l(power F j x))).
Proof.
 revert l x; induction j; intros l x; simpl; [reflexivity|].
 change (power F (S j)(Z(Q(power Q(j+l)x))) =
          Q(power Q j(Z(power Q l(power F (S j)x))))).
 rewrite F_power_Z,GQ,F_Q_power,IHj.
 now rewrite <-power_succ_r.
Qed.
Lemma phaseG_inert n x : 1<=n -> phaseG n(inert n x)=inert n(phaseG n x).
Proof.
 intros Hn. unfold phaseG,inert.
 replace n with (n+0) at 2 by lia.
 rewrite transport. simpl.
 destruct n; [lia|]. simpl power at 1. rewrite GQ,F_Q_power,FZ.
 rewrite (power_commute Q Q (fun _=>eq_refl) n). reflexivity.
Qed.
Lemma phase_inert n x : phase n(inert n x)=inert n(phase n x).
Proof.
 unfold phase,inert. replace n with(n+0) at 2 by lia.
 rewrite transport. reflexivity.
Qed.
Lemma bounded_factor n j x : 1<=n -> j<=n ->
 power (phase n) (S j) x =
 Z(power Q j(power F(n-j)(power (phaseG n) j x))).
Proof.
 intros Hn. revert x. induction j; intros x Hj.
 - simpl. now rewrite Nat.sub_0_r.
 - rewrite power_succ_r,IHj by lia.
   rewrite (power_commute (phaseG n) (phase n)) by (intro y; apply phaseG_phase;lia).
   unfold phase at 1.
   replace(n-j) with(S(n-S j)) by lia.
   rewrite F_power_Z.
   rewrite <-power_succ_r. reflexivity.
Qed.
Lemma phase_factor n x : 1<=n ->
 power (phase n) (S n) x=inert n(power (phaseG n) n x).
Proof. intros Hn. rewrite bounded_factor by lia.
 unfold inert. rewrite Nat.sub_diag. reflexivity. Qed.
Lemma cofinal_factor n k x : 1<=n ->
 power (phase n) (k*S n) x = power (inert n) k(power (phaseG n)(k*n)x).
Proof.
 intros Hn. rewrite !power_mul.
 rewrite (power_ext (fun y=>power (phase n)(S n)y)
   (fun y=>inert n(power(phaseG n)n y))) by (intro y;apply phase_factor;lia).
 apply power_product. intro y. symmetry. apply power_commute.
 intro z; apply phaseG_inert;lia.
Qed.
Lemma phase_eventually n x : 1<=n ->
 eventually (phase n)x <-> eventually (phaseG n)x.
Proof.
 intros Hn; split; intros [k E].
 - assert (D:power (phase n)(k*S n)x=None).
   { eapply (power_halt_mono (phase n) (phase_strict n) k (k*S n) x); eauto; nia. }
   rewrite cofinal_factor in D by lia.
   apply (proj1 (power_injective_none (inert n) (inert_none n) k _)) in D.
   exists(k*n). exact D.
 - exists(k*S n). rewrite cofinal_factor by lia.
   assert(D:power(phaseG n)(k*n)x=None).
   { eapply (power_halt_mono (phaseG n) (phaseG_strict n) k (k*n) x); eauto; nia. }
   rewrite D. apply power_strict. apply inert_none;reflexivity.
Qed.
Lemma phaseG_Q_power n k x : 1<=n ->
 power(phaseG n)(S k)(Q x)=phase n(power(phaseG n)k(F x)).
Proof. intros Hn. rewrite power_succ_r,phaseG_Q.
 apply power_commute. intro y;apply phaseG_phase;lia. Qed.
Lemma phase_halt_G n x : phase n x=None -> phaseG n x=None.
Proof. unfold phase,phaseG. rewrite Z_none. intro E;now rewrite E. Qed.
Lemma Q_index_nonincrease_abstract n k x : 1<=n ->
 power(phaseG n)k(Q x)=None -> power(phaseG n)k(F x)=None.
Proof.
 intros Hn. destruct k as [|k].
 - simpl power. intro E. apply (proj1(Q_none x)) in E. now rewrite E.
 - rewrite phaseG_Q_power by lia.
   intro E. apply phase_halt_G in E. exact E.
Qed.
Lemma phaseG_Z n x : 1<=n -> phaseG n(Z x)=phase n(G x).
Proof. intro Hn. destruct n;[lia|]. unfold phaseG,phase.
 rewrite F_power_Z,GQ. reflexivity. Qed.
Lemma phaseG_Z_power n k x : 1<=n ->
 power(phaseG n)(S k)(Z x)=phase n(power(phaseG n)k(G x)).
Proof. intros Hn. rewrite power_succ_r,phaseG_Z by lia.
 apply power_commute. intro y;apply phaseG_phase;lia. Qed.
Lemma phaseG_eventually_Q n x : 1<=n ->
 eventually(phaseG n)(Q x) <-> eventually(phaseG n)(F x).
Proof.
 intros Hn; split; intros[k E].
 - exists k. now apply Q_index_nonincrease_abstract.
 - exists(S k). rewrite phaseG_Q_power,E by lia. apply phase_strict.
Qed.
Lemma phaseG_eventually_Z n x : 1<=n ->
 eventually(phaseG n)(Z x) <-> eventually(phaseG n)(G x).
Proof.
 intros Hn;split;intros[k E].
 - destruct k as[|k].
   + simpl in E. apply(proj1(Z_none x)) in E. subst x.
     exists 0. simpl. exact G_none.
   + rewrite phaseG_Z_power in E by lia.
     exists(S k). apply phase_halt_G,E.
 - exists(S k). rewrite phaseG_Z_power,E by lia. apply phase_strict.
Qed.
End Algebra.
