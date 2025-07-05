From BusyCoq Require Import Eqb.
From BusyCoq Require Import LibTactics.
Require Import PeanoNat.
Require Import NArith.
Require Import Lia.

Lemma feq2{A B C}(f:A->B->C) x y x' y':
  x=x' ->
  y=y' ->
  (f x y) = (f x' y').
Proof.
  congruence.
Qed.

Lemma sub_mod a b c:
  (a>=b ->
  c<>0 ->
  ((a-b) mod c) =
  ((a mod c)+(c-(b mod c))) mod c)%nat.
Proof.
  intros H H0.
  remember (a-b) as d.
  replace a with (d+b) by lia.
  rewrite Nat.Div0.add_mod_idemp_l.
  pose proof (Nat.mod_upper_bound b c H0).
  pose proof (Nat.Div0.mod_le b c).
  replace (d+b+(c-b mod c))%nat with (b+(d+c-(b mod c)))%nat by lia.
  rewrite <-Nat.Div0.add_mod_idemp_l.
  replace (b mod c+(d+c-(b mod c)))%nat with (d+c)%nat by lia.
  rewrite <-Nat.Div0.add_mod_idemp_r.
  rewrite Nat.Div0.mod_same.
  rewrite Nat.add_0_r.
  reflexivity.
Qed.

Lemma div_mod_comm a b c v1:
  b*c=v1 ->
  b<>O ->
  (a/b) mod c =
  (a mod v1)/b.
Proof.
  intros Hv1 Hb; subst.
  rewrite Nat.Div0.mod_mul_r.
  rewrite Nat.mul_comm.
  rewrite Nat.div_add. 2: apply Hb.
  pose proof (Nat.mod_upper_bound a b).
  rewrite (Nat.div_small _ _ (H Hb)).
  reflexivity.
Qed.

Fixpoint remove_factor(x:N)(c:N)(x0:positive):=
(if x mod c =? 0 then
let x:=x/c in
match x0 with
| xH => x
| xI x0 | xO x0 => remove_factor x c x0
end
else x)%N.

Definition phi_0 '(x,y,i):=
(
if x =? 1 then
inr y
else if x <? i*i then
inr (y/x*(x-1))
else
inl (
if x mod i =? 0 then
let x:=remove_factor x i (N.succ_pos x) in
let y:=y/i*(i-1) in
(x,y,N.succ i)
else
(x,y,N.succ i)
))%N.

Definition phi(x:N) :=
match N_iter_until phi_0 (inl (x,x,2%N)) x with
| inl _ => 0%N
| inr x => x
end.

Definition nat_phi(x:nat) :=
  N.to_nat (phi (N.of_nat x)).

Lemma pow_mod a b c c' v1 v2 v3 v4:
  nat_phi c = c' ->
  c' <> O ->
  c <> O ->
  (b mod c') = v1 ->
  (a^v1 mod c) = v2 ->
  (a^c' mod c) = v3 ->
  (v3*v2 mod c) = v4 ->
  b>=v1+c' ->
  v4*v3 mod c = v4 ->
  a^b mod c = v4.
Proof.
  intros Hcc' Hc' Hc Hv1 Hv2 Hv3 Hv4 Hb HE.
  pose proof (Nat.Div0.div_mod b c') as Hb'.
  rewrite Hv1 in Hb'.
  remember (b/c') as d.
  destruct d as [|d].
  1: lia.
  rewrite Nat.mul_succ_r in Hb'.
  rewrite <-Nat.add_assoc in Hb'.
  rewrite Hb'.
  do 2 rewrite Nat.pow_add_r.
  rewrite Nat.Div0.mul_mod.
  rewrite (Nat.Div0.mul_mod (a^c')).
  rewrite Hv2,Hv3,Hv4.
  clear Heqd.
  generalize d.
  intros d0.
  induction d0.
  - rewrite Nat.mul_0_r.
    cbn.
    assert (c=1\/1<c)%nat as [E|E] by lia.
    + subst c.
      cbn.
      pose proof (Nat.mod_upper_bound (v3*v2) _ Hc).
      lia.
    + rewrite (Nat.mod_small 1 c).
      2: apply E.
      rewrite Nat.mul_1_l.
      subst v4.
      apply Nat.Div0.mod_mod.
  - rewrite Nat.mul_succ_r.
    rewrite Nat.pow_add_r.
    rewrite Nat.Div0.mul_mod_idemp_l in *.
    remember (a^(c'*d0)) as c1.
    replace (c1*a^c'*v4) with (c1*v4*a^c') by lia.
    rewrite <-Nat.Div0.mul_mod_idemp_l.
    rewrite IHd0.
    rewrite <-Nat.Div0.mul_mod_idemp_r.
    rewrite Hv3.
    apply HE.
Qed.

Fixpoint N_pow_mod_0(a:N)(b:positive)(c:N):N :=
(match b with
| xH => a mod c
| xI b0 =>
  let x:=N_pow_mod_0 a b0 c in
  let y:=((x*x) mod c) in
  ((y*a) mod c)
| xO b0 =>
  let x:=N_pow_mod_0 a b0 c in
  ((x*x) mod c)
end)%N.

Lemma N_pow_mod_0_spec a b c:
  (N_pow_mod_0 a b c =
  (a^(Npos b)) mod c)%N.
Proof.
  induction b; cbn[N_pow_mod_0].
  - rewrite IHb.
    replace (Npos b~1) with (Npos b + Npos b + 1)%N by lia.
    do 2 rewrite N.pow_add_r.
    rewrite N.pow_1_r.
    rewrite <-N.Div0.mul_mod.
    rewrite N.Div0.mul_mod_idemp_l.
    reflexivity.
  - rewrite IHb.
    replace (Npos b~0) with (Npos b + Npos b)%N by lia.
    rewrite N.pow_add_r.
    rewrite <-N.Div0.mul_mod.
    reflexivity.
  - rewrite N.pow_1_r.
    reflexivity.
Qed.

Definition N_pow_mod_c(a b c:N):N :=
(match b with
| N0 => 1 mod c
| Npos b0 =>
  N_pow_mod_0 a b0 c
end)%N.

Lemma N_pow_mod_c_spec a b c:
  N_pow_mod_c a b c =
  ((a^b) mod c)%N.
Proof.
  destruct b as [|b]; unfold N_pow_mod_c.
  - rewrite N.pow_0_r.
    reflexivity.
  - apply N_pow_mod_0_spec.
Qed.

Lemma mul_mod_c a b c v1:
  N.to_nat ((N.of_nat a)*(N.of_nat b) mod (N.of_nat c))%N = v1 ->
  ((a*b) mod c) = v1.
Proof.
  rewrite Nnat.N2Nat.inj_mod.
  rewrite Nnat.N2Nat.inj_mul.
  repeat rewrite Nat2N.id.
  tauto.
Qed.

Lemma pow_mod_c a b c v1:
  N.to_nat (N_pow_mod_c (N.of_nat a) (N.of_nat b) (N.of_nat c)) = v1 ->
  ((a^b) mod c) = v1.
Proof.
  rewrite N_pow_mod_c_spec.
  rewrite Nnat.N2Nat.inj_mod.
  rewrite Nnat.N2Nat.inj_pow.
  repeat rewrite Nat2N.id.
  tauto.
Qed.


Ltac no_var e :=
match e with
| ?a + ?b => no_var a; no_var b
| ?a - ?b => no_var a; no_var b
| ?a * ?b => no_var a; no_var b
| ?a / ?b => no_var a; no_var b
| ?a mod ?b => no_var a; no_var b
| ?a ^ ?b => no_var a; no_var b
| S ?a => no_var a
| O => idtac
end.

Ltac is_nat_const e :=
match e with
| S ?a => is_nat_const a
| O => idtac
end.

Ltac crefl := vm_compute; reflexivity.

Ltac rw_mod_1 :=
(*
match goal with
| |- ?G => idtac "rw_mod_1"; idtac G
end;*)
match goal with
| |- (_ = _) = _ =>
  apply feq2; rw_mod_0
| |- (?a + ?b) mod ?c = _ =>
  is_nat_const c;
  etransitivity; [ apply Nat.Div0.add_mod | ];
  rw_mod_rec
| |- (?a - ?b) mod ?c = _ =>
  is_nat_const c;
  etransitivity; [ apply sub_mod; [ shelve | congruence ] | ];
  rw_mod_rec
| |- (?a * ?b) mod ?c = _ =>
  is_nat_const c;
  etransitivity; [ apply Nat.Div0.mul_mod | ];
  rw_mod_rec
| |- (?a / ?b) mod ?c = _ =>
  (*idtac "div_mod_comm";*)
  is_nat_const b;
  is_nat_const c;
  etransitivity; [ eapply div_mod_comm; [ crefl | congruence ] | ];
  rw_mod_rec
| |- (?a ^ ?b) mod ?c = _ =>
  is_nat_const a;
  is_nat_const c;
  (
  (is_nat_const b; (*idtac "pow_mod_1";*) rw_mod_2) +
  ( (*idtac "pow_mod_2";
       idtac a; idtac b; idtac c;*)
    etransitivity;
    [ eapply pow_mod;
      [ crefl | | | | | | | | ];
      [ congruence | congruence | | | | | | ];
      [ rw_mod_0 | | | | | ];
      [ rw_mod_0 | | | | ];
      [ rw_mod_0 | | | ];
      [ rw_mod_0 | | ];
      [ shelve | rw_mod_0 ]
    | ];
    rw_mod_rec)
  )
| |- (_ + _ = _) =>
  rw_mod_rec
| |- (_ - _ = _) =>
  rw_mod_rec
| |- (_ * _ = _) =>
  rw_mod_rec
| |- (_ / _ = _) =>
  rw_mod_rec
| |- (_ mod _ = _) =>
  rw_mod_rec
| |- (_ ^ _ = _) =>
  rw_mod_rec
| _ => rw_mod_2
end
with
rw_mod_0 := rw_mod_1
with
rw_mod_rec :=
(*
match goal with
| |- ?G => idtac "rw_mod_rec"; idtac G
end;*)
etransitivity; [ (apply feq2; rw_mod_0) + reflexivity | ]; rw_mod_2
with
rw_mod_2 :=
(*
match goal with
| |- ?G => idtac "rw_mod_2"; idtac G
end;*)
etransitivity;
[
match goal with
| |- (_ * 0 = _) =>
  eapply Nat.mul_0_r
| |- (0 * _ = _) =>
  eapply Nat.mul_0_l
| |- (?a * ?b = _) =>
  reflexivity
| |- (?a ^ ?b = _) =>
  reflexivity
| |- ((?a * ?b) mod ?c = _) =>
  no_var a; no_var b; no_var c;
  eapply mul_mod_c; crefl
| |- ((?a ^ ?b) mod ?c = _) =>
  no_var a; no_var b; no_var c;
  eapply pow_mod_c; crefl
| |- (?e = _) =>
  no_var e; crefl
| _ =>
  reflexivity
end
| 
  (*match goal with
  | |- ?x = _ => idtac "rw_mod_2 ret"; idtac x
  end;*)
  reflexivity
].

Ltac rw_mod :=
match goal with
| |- ?e =>
  eassert (e = _) as Hrw by rw_mod_1;
  rewrite Hrw;
  clear Hrw
end.

Lemma div_mod' a b c:
  (a mod b) = c ->
  a = c+(a/b*b).
Proof.
  intros.
  rewrite Nat.add_comm,Nat.mul_comm,<-H.
  apply Nat.Div0.div_mod.
Qed.



Lemma divc_ge a b c v1:
  b*c=v1 ->
  b<>O ->
  a>=v1 ->
  a/b >= c.
Proof.
  intros Hv1 Hb Ha.
  subst v1.
  pose proof (Nat.Div0.div_mod a b) as Hd.
  remember (a/b) as d.
  pose proof (Nat.mod_upper_bound a b).
  pose proof (Nat.mul_le_mono_l (d+1) c b).
  lia.
Qed.

Lemma mul_ge c1 c2 v1 v2 a b c:
  c1=v1 ->
  c2=v2 ->
  a>=v1 ->
  b>=v2 ->
  v1*v2>=c ->
  a*b>=c.
Proof.
  intros Hv1 Hv2 Ha Hb Hc.
  subst v1 v2.
  pose proof (Nat.mul_le_mono_l c2 b a).
  pose proof (Nat.mul_le_mono_r c1 a c2).
  lia.
Qed.

Lemma add_ge c1 c2 a b c:
  a>=c1 ->
  b>=c2 ->
  c1+c2>=c ->
  a+b>=c.
Proof.
  lia.
Qed.

Lemma addc_ge a b c v1:
  c-b=v1 ->
  c>=b ->
  a>=v1 ->
  a+b>=c.
Proof.
  lia.
Qed.

Lemma cadd_ge a b c v1:
  c-b=v1 ->
  c>=b ->
  a>=v1 ->
  b+a>=c.
Proof.
  lia.
Qed.

Lemma subc_ge a b c v1:
  b+c=v1 ->
  a>=v1 ->
  a-b>=c.
Proof.
  lia.
Qed.

Fixpoint log' a c n :=
(if c<=?1 then O else
if c=?2 then 1 else
let c':=((c+a-1)/a) in
match n with
| O => O
| S n0 => S (log' a c' n0)
end)%nat.

Lemma log'_spec a b c n:
  a>=2 ->
  c<=n ->
  b>=log' a c n ->
  a^b>=c.
Proof.
  gen a c n.
  induction b; intros.
  - rewrite Nat.pow_0_r.
    destruct n as [|n]; cbn in H1;
    destruct (Nat.leb_spec c 1)%nat; try lia.
    destruct (c=?2); lia.
  - cbn.
    destruct n as [|n]; cbn in H1;
    destruct (Nat.leb_spec c 1)%nat; try lia.
    1: pose proof (Nat.pow_nonzero a b); lia.
    destruct (Nat.eqb_spec c 2).
    1: pose proof (Nat.pow_nonzero a b); lia.
    + unshelve epose proof (IHb a ((c+a-1)/a) n _ _ _) as IHb.
      all: try lia.
      * apply (Nat.Div0.div_le_upper_bound).
        destruct a as [|[|a]]; try lia.
        destruct n as [|n]; try lia.
      * remember (a^b) as x.
        assert (a*x<c->False). {
          intro Hlt.
          replace (c+a-1) with ((1+x)*a+(c-(a*x+1))) in IHb by lia.
          rewrite Nat.div_add_l in IHb; lia.
        }
        lia.
Qed.

Lemma powc_ge a b c v1:
  log' a c c = v1 ->
  a>=2 ->
  b>=v1 ->
  a^b>=c.
Proof.
  pose proof (log'_spec a b c c).
  lia.
Qed.


Definition div_up a b := (a+b-1)/b.
Definition sqrt_up a := div_up a (Nat.sqrt a).

Ltac solve_ge :=
match goal with
| |- ?a + ?b >= ?c =>
  no_var b; no_var c;
  eapply addc_ge; [ crefl | lia | ];
  solve_ge
| |- ?a - ?b >= ?c =>
  no_var b; no_var c;
  eapply subc_ge; [ crefl | ];
  solve_ge
| |- ?a * ?b >= ?c =>
  is_nat_const b; no_var c;
  eapply (mul_ge (div_up c b) b); [ crefl | crefl | | | lia ];
  solve_ge
| |- ?a * ?b >= ?c =>
  is_nat_const a; no_var c;
  eapply (mul_ge a (div_up c a)); [ crefl | crefl | | | lia ];
  solve_ge
| |- ?a * ?b >= ?c =>
  no_var c;
  eapply (mul_ge (Nat.sqrt c) (sqrt_up c)); [ crefl | crefl | | | lia ];
  solve_ge
| |- ?a / ?b >= ?c =>
  no_var b; no_var c;
  eapply divc_ge; [ crefl | congruence | ];
  solve_ge
| |- ?a ^ ?b >= ?c =>
  no_var a; no_var c;
  eapply powc_ge; [ crefl | lia | ];
  solve_ge
| _ => try lia
end.


Ltac simpl_N_to_nat_expr e :=
match e with
| N.to_nat ?a =>
  eassert (e = _) as Hrw by (vm_compute; reflexivity);
  rewrite Hrw;
  clear Hrw
| ?a -> ?b =>
  simpl_N_to_nat_expr a ||
  simpl_N_to_nat_expr b
| ?a ?b =>
  simpl_N_to_nat_expr a ||
  simpl_N_to_nat_expr b
end.

Ltac simpl_N_to_nat :=
  repeat (
  rewrite Nnat.N2Nat.inj_add ||
  rewrite Nnat.N2Nat.inj_sub ||
  rewrite Nnat.N2Nat.inj_mul ||
  rewrite Nnat.N2Nat.inj_pow ||
  rewrite Nnat.Nat2N.id);
  repeat
  match goal with
  | |- ?G => simpl_N_to_nat_expr G
  end.

Ltac simpl_small_nat C :=
repeat
match goal with
| |- context[?a+?b] =>
  is_nat_const a;
  is_nat_const b;
  eassert (X:(N.of_nat a + N.of_nat b <? N.of_nat C)%N = true) by (vm_compute; reflexivity);
  clear X;
  eassert (X:a+b=_) by (vm_compute; reflexivity);
  rewrite X; clear X
| |- context[?a-?b] =>
  is_nat_const a;
  is_nat_const b;
  eassert (X:(N.of_nat a <? N.of_nat C)%N = true) by (vm_compute; reflexivity);
  clear X;
  eassert (X:a-b=_) by (vm_compute; reflexivity);
  rewrite X; clear X
| |- context[?a*?b] =>
  is_nat_const a;
  is_nat_const b;
  eassert (X:(N.of_nat a * N.of_nat b <? N.of_nat C)%N = true) by (vm_compute; reflexivity);
  clear X;
  eassert (X:a*b=_) by (vm_compute; reflexivity);
  rewrite X; clear X
| |- context[?a/?b] =>
  is_nat_const a;
  is_nat_const b;
  eassert (X:(N.of_nat a <? N.of_nat C)%N = true) by (vm_compute; reflexivity);
  clear X;
  eassert (X:a/b=_) by (vm_compute; reflexivity);
  rewrite X; clear X
| |- context[?a^?b] =>
  is_nat_const a;
  is_nat_const b;
  eassert (X:(N.of_nat a ^ N.of_nat b <? N.of_nat C)%N = true) by (vm_compute; reflexivity);
  clear X;
  eassert (X:a^b=_) by (vm_compute; reflexivity);
  rewrite X; clear X
end.

