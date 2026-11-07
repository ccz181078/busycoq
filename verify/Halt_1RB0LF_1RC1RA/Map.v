(** The map A(a,b), and its link to the raw machine. *)
From BusyCoq Require Import Individual62.
From BusyCoq.Halt_1RB0LF_1RC1RA Require Import Rules.
Require Import Lia ZArith.
Open Scope Z_scope.

(** One application: next state, and its cost term [r], where 6 * (raw steps) = 2 * (a'^2 - a^2) + r. *)
Definition aStep (a b : Z) : option (Z * Z * Z) :=
  if b =? a+3 then None
  else if a+3 <? b then Some (2*a+6, b-a-3, -30*a+18)
  else if b =? 1 then
    if a mod 4 =? 2 then Some (6, a+7, 2*a*a+39*a+354)
    else Some (22, a-2, 2*a*a+39*a+250)
  else if b =? 3 then
    if a mod 4 =? 2 then Some (6, a+13, 2*a*a+63*a+774)
    else Some (a+8, 2, a+136)
  else if b mod 2 =? 1 then
    if b =? a+1 then Some (6, a+b+2, 8*a*a+30*a+174)
    else if (a-b+5) mod 4 =? 2 then Some (a-b+11, 2*b-4, 4*b*(a+b)-11*a+29*b+13)
    else Some (a-b+19, 2*b-8, 4*b*(a+b)-19*a+37*b-29)
  else if (a-b) mod 4 =? 2 then Some (6, a+b+7, 2*a*a+6*b*b+39*a-9*b+378)
  else Some (22, a+b-2, 2*a*a+6*b*b+39*a-9*b+274).

Inductive Reach : Z -> Z -> Z -> Z -> Z -> Z -> Prop :=
  | Reach_refl a b : Reach a b a b 0 0
  | Reach_step a b a1 b1 r a2 b2 n s :
      aStep a b = Some (a1, b1, r) -> Reach a1 b1 a2 b2 n s -> Reach a b a2 b2 (1+n) (r+s).

Lemma Reach_trans a b a1 b1 n r a2 b2 n' r':
  Reach a b a1 b1 n r -> Reach a1 b1 a2 b2 n' r' -> Reach a b a2 b2 (n+n') (r+r').
Proof.
  induction 1; intros H'.
  - exact H'.
  - replace (1+n+n') with (1+(n+n')) by ring. replace (r+s+r') with (r+(s+r')) by ring.
    econstructor; eauto.
Qed.

Definition inv (a b : Z) := a mod 2 = 0 /\ 6 <= a /\ 1 <= b.
Definition AZ (a b : Z) := AK (Z.to_nat (a/2)) (Z.to_nat b).

Lemma AZ_eq k m a b: a = 2 * Z.of_nat k -> b = Z.of_nat m -> AZ a b = AK k m.
Proof. intros -> ->. unfold AZ. f_equal; lia. Qed.

Local Ltac zl := Z.div_mod_to_equations; lia.
Local Ltac wit x e := set (x := Z.to_nat (e)); assert (Z.of_nat x = e) by zl; clearbody x.
Lemma some3 (x y z x' y' z' : Z): Some (x,y,z) = Some (x',y',z') -> x = x' /\ y = y' /\ z = z'.
Proof. intros H. inversion H. auto. Qed.
Ltac inj H := apply some3 in H; destruct H as (<- & <- & <-).

Lemma aStep_inv a b a1 b1 r: inv a b -> aStep a b = Some (a1, b1, r) -> inv a1 b1.
Proof.
  intros (Ha2 & Ha6 & Hb1) H. unfold aStep, inv in *.
  destruct (Z.eqb_spec b (a+3)) as [|N1]. { discriminate. }
  destruct (Z.ltb_spec (a+3) b) as [L1|L1].
  { inj H. zl. }
  destruct (Z.eqb_spec b 1) as [|N2].
  { destruct (Z.eqb_spec (a mod 4) 2); inj H; zl. }
  destruct (Z.eqb_spec b 3) as [|N3].
  { destruct (Z.eqb_spec (a mod 4) 2); inj H; zl. }
  destruct (Z.eqb_spec (b mod 2) 1) as [O|O].
  { destruct (Z.eqb_spec b (a+1)) as [N4|N4].
    { inj H. zl. }
    destruct (Z.eqb_spec ((a-b+5) mod 4) 2); inj H; zl. }
  destruct (Z.eqb_spec ((a-b) mod 4) 2); inj H; zl.
Qed.

Local Ltac finish_rule R k m k1 m1 :=
  match goal with |- exists st, AZ ?x ?y -->> st / AZ ?x1 ?y1 /\ _ =>
    rewrite (AZ_eq k m x y) by lia; rewrite (AZ_eq k1 m1 x1 y1) by lia end;
  eexists; split; [exact R | repeat (rewrite Nat2Z.inj_add || rewrite Nat2Z.inj_mul); cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; ring].

Lemma aStep_tm a b a1 b1 r: inv a b -> aStep a b = Some (a1, b1, r) ->
  exists st, AZ a b -->> st / AZ a1 b1 /\ 6 * Z.of_nat st = 2 * (a1*a1 - a*a) + r.
Proof.
  intros Hi H. unfold aStep in H. pose proof Hi as Hi'. destruct Hi' as (Ha2 & Ha6 & Hb1).
  destruct (Z.eqb_spec b (a+3)) as [|Ne3]. { discriminate. }
  destruct (Z.ltb_spec (a+3) b) as [Hlt|Hge].
  { inj H.
    wit n (a/2-1). wit d (b-a-3).
    assert (a = 2*Z.of_nat n+2) by zl. subst a.
    assert (b = 2*Z.of_nat n+5+Z.of_nat d) by zl. subst b.
    finish_rule (RuleD n d) (S n) (2*n+5+d)%nat (2*n+5)%nat d. }
  destruct (Z.eqb_spec b 1) as [|Ne1].
  { subst b. destruct (Z.eqb_spec (a mod 4) 2) as [Hm|Hm]; inj H.
    - wit K (a/4). assert (a = 4*Z.of_nat K+2) by zl. subst a.
      finish_rule (RuleP K) (2*K+1)%nat 1%nat 3%nat (4*K+9)%nat.
    - wit K (a/4-1). assert (a = 4*Z.of_nat K+4) by zl. subst a.
      finish_rule (RuleQ K) (2*K+2)%nat 1%nat 11%nat (4*K+2)%nat. }
  destruct (Z.eqb_spec b 3) as [|Ne3'].
  { subst b. destruct (Z.eqb_spec (a mod 4) 2) as [Hm|Hm]; inj H.
    - wit K (a/4-1). assert (a = 4*Z.of_nat K+6) by zl. subst a.
      finish_rule (RuleR K) (2*K+3)%nat 3%nat 3%nat (4*K+19)%nat.
    - wit K (a/4-1). assert (a = 4*Z.of_nat K+4) by zl. subst a.
      replace (2*Z.of_nat K*0) with 0 by ring.
      finish_rule (RuleU 0 K) (2*K+2+0)%nat (2*0+3)%nat (2*K+6)%nat (4*0+2)%nat. }
  destruct (Z.eqb_spec (b mod 2) 1) as [Hodd|Hev].
  { destruct (Z.eqb_spec b (a+1)) as [Hd|Hd].
    { inj H.
      wit t (b/2-1). assert (b = 2*Z.of_nat t+3) by zl. subst b.
      assert (a = 2*Z.of_nat t+2) by zl. subst a.
      finish_rule (RuleT t) (t+1)%nat (2*t+3)%nat 3%nat (4*t+7)%nat. }
    wit t (b/2-1). assert (b = 2*Z.of_nat t+3) by zl. subst b.
    destruct (Z.eqb_spec ((a-(2*Z.of_nat t+3)+5) mod 4) 2) as [Hm|Hm]; inj H.
    - wit K ((a-2*Z.of_nat t-4)/4). assert (a = 4*Z.of_nat K+4+2*Z.of_nat t) by zl. subst a.
      finish_rule (RuleU t K) (2*K+2+t)%nat (2*t+3)%nat (2*K+6)%nat (4*t+2)%nat.
    - wit t' (Z.of_nat t-1). assert (t = (t'+1)%nat) by zl. subst t.
      wit K ((a-2*Z.of_nat t'-8)/4). assert (a = 4*Z.of_nat K+8+2*Z.of_nat t') by zl. subst a.
      replace (2*Z.of_nat (t'+1)+3) with (2*Z.of_nat t'+5) by lia.
      finish_rule (RuleV t' K) (2*K+4+t')%nat (2*t'+5)%nat (2*K+11)%nat (4*t'+2)%nat. }
  wit t (b/2-1). assert (b = 2*Z.of_nat t+2) by zl. subst b.
  destruct (Z.eqb_spec ((a-(2*Z.of_nat t+2)) mod 4) 2) as [Hm|Hm]; inj H.
  - destruct (Z.eq_dec a (2*Z.of_nat t)) as [E|E].
    + wit n (Z.of_nat t-1). assert (t = S n) by zl. subst t. subst a.
      replace (2*Z.of_nat (S n)) with (2*Z.of_nat n+2) in * by lia.
      replace (2*Z.of_nat n+2+2) with (2*Z.of_nat n+4) in * by lia.
      finish_rule (RuleW0 n) (S n) (2*n+4)%nat 3%nat (4*n+13)%nat.
    + wit K ((a-2*Z.of_nat t-4)/4). assert (a = 4*Z.of_nat K+4+2*Z.of_nat t) by zl. subst a.
      finish_rule (RuleW K t) (2*K+2+t)%nat (2*t+2)%nat 3%nat (4*K+4*t+13)%nat.
  - destruct (Z.eq_dec a (2*Z.of_nat t+2)) as [E|E].
    + subst a.
      finish_rule (RuleX0 t) (1+t)%nat (2*t+2)%nat 11%nat (4*t+2)%nat.
    + wit K ((a-2*Z.of_nat t-6)/4). assert (a = 4*Z.of_nat K+6+2*Z.of_nat t) by zl. subst a.
      finish_rule (RuleX K t) (2*K+3+t)%nat (2*t+2)%nat 11%nat (4*K+4*t+6)%nat.
Qed.

Lemma Reach_tm a b a1 b1 n r: Reach a b a1 b1 n r -> inv a b ->
  inv a1 b1 /\ exists st, AZ a b -->> st / AZ a1 b1 /\ 6 * Z.of_nat st = 2 * (a1*a1 - a*a) + r.
Proof.
  induction 1 as [a b|a b a1 b1 r a2 b2 n s Hs _ IH]; intros Hi.
  { split; [exact Hi|]. exists 0%nat. split; [constructor|]. change (Z.of_nat 0) with 0. ring. }
  pose proof (aStep_inv _ _ _ _ _ Hi Hs) as Hi1.
  destruct (aStep_tm _ _ _ _ _ Hi Hs) as (st1 & H1 & E1).
  destruct (IH Hi1) as (Hi2 & st2 & H2 & E2).
  split; [exact Hi2|]. exists (st1+st2)%nat. split.
  - eapply ms_app; eauto.
  - rewrite Nat2Z.inj_add. lia.
Qed.

(** The halt form. *)
Lemma aStep_halt a: inv a (a+3) ->
  exists st ch, AZ a (a+3) -->> st / ch /\ halted tm ch /\ Z.of_nat st = a*a+7*a+41.
Proof.
  intros (Ha2 & Ha6 & Hb1).
  wit n (a/2-1). assert (a = 2*Z.of_nat n+2) by zl. subst a.
  destruct (HaltK (2*n+4)) as (ch & H2 & Hh).
  match goal with |- exists st ch, AZ ?x ?y -->> st / ch /\ _ => rewrite (AZ_eq (S n) (2*n+5+0) x y) by lia end.
  exists ((4*n*n+14*n+25)+(4*(2*n+4)+18))%nat, ch. split; [|split; [exact Hh|]].
  - eapply ms_app; [apply (RuleD n 0)|].
    replace (2*n+5)%nat with (S (2*n+4)) by lia. exact H2.
  - repeat (rewrite Nat2Z.inj_add || rewrite Nat2Z.inj_mul). cbn [Z.of_nat Pos.of_succ_nat Pos.succ]. ring.
Qed.

(** Blank tape to A(6,1). *)
Lemma start_AZ: c0 -->> 35 / AZ 6 1.
Proof. rewrite (AZ_eq 3 1 6 1) by lia. exact Init. Qed.

(** What a checked orbit gives: a halt from the blank tape, in exactly this many steps. *)
Theorem halts_of_Reach a n r: Reach 6 1 a (a+3) n r ->
  exists st, halts_in tm c0 st /\
    6 * Z.of_nat st = 6*35 + 2*(a*a-36) + r + 6*(a*a+7*a+41).
Proof.
  intros H.
  destruct (Reach_tm _ _ _ _ _ _ H) as (Hi & st1 & H1 & E1). { unfold inv; lia. }
  destruct (aStep_halt a Hi) as (st2 & ch & H2 & Hh & E2).
  exists (35+st1+st2)%nat. split.
  - exists ch. split; [|exact Hh].
    eapply ms_app; [eapply ms_app; [apply start_AZ|exact H1]|exact H2].
  - rewrite !Nat2Z.inj_add. rewrite E2. lia.
Qed.
