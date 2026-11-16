From BusyCoq Require Import Individual62.

Require Import ZArith ZifyNat Lia.
Require Import String.
Require Import List.
From BusyCoq Require Import Longitudinal DivModCases NatMod_v2.

Ltac esc :=
  (apply BoundedConfig.segRLs_c_spec with (T:=10^3); reflexivity) ||
  (apply BoundedConfig.sideRLs_c_spec with (T:=10^3); reflexivity) ||
  (eapply sideRLs_c_spec with (T:=10^6); [vm_compute; reflexivity | st; reflexivity]).


Module TM5.
Definition tm := Eval compute in (TM_from_str "1RB0LF_1LC0RE_0LA1RD_---1RE_1RC1RA_0RB1RF").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation hR := (B,@nil Sym).
Notation hL := (A,[0;1;0]).
Notation hR' := (C,<[0;0;1]).
Notation hL' := (F,[0;0;1;1;1;1;0]).
Notation h := [(hR,hL)].
Notation w := [1;1;0].
Notation d := [1;1;1].

Notation RC0 := (flat_map (fun a => d++w^^a)).
Notation RC1 := (flat_map (fun a => w^^a++d++w)).

Fixpoint RIncs0 k ls :=
match ls with
| [] => []
| a::ls => k+a::RIncs0 (k*2) ls
end.

Lemma RIncs0_spec k ls:
  segRLs tm (h^^k) (h^^(k*2^(length ls))) (RC0 ls) (RC0 (RIncs0 k ls)).
Proof.
  gen k.
  induction ls; cbn[flat_map RIncs0 length]; intros.
  - rewrite Nat.mul_1_r.
    eapply segRLs_wall''; esc.
  - eapply segRLs_concat.
    2: applys_eq (IHls (k*2)); cbn; flia.
    clear.
    induction k.
    1: esx.
    replace (S k) with (k+1) by lia.
    replace ((k+1)*2) with (k*2+2) by lia.
    eapply segRLs_trans_add.
    1: apply IHk.
    esx.
Qed.

Notation "l <| r" := (l {{{ (hL,L) }}} r) (at level 30).
Notation "l |> r" := (l {{{ (hR,R) }}} r) (at level 30).
Notation "l |c> r" := (l {{{ (hR',R) }}} r) (at level 30).
Notation "l <f| r" := (l {{{ (hL',L) }}} r) (at level 30).

Lemma c_RR l n r:
  l |c> w^^n *> d *> w *> r -->*
  l <* <[0;0] <* <[1]^^(n*3+4) |c> r.
Proof.
  es.
Qed.

Lemma f_LR l n r:
  l <* <[0;0] <* <[1]^^(n*3+4) <f| r -->*
  l <* <[1]^^4 |> RC0 ([0]^^(n+1) ++ [1])%nat *> r.
Proof.
  rewrite flat_map_app,flat_map_lpow.
  es.
Qed.

Lemma LL l r:
  l <* <[1]^^4 <| r -->*
  l <f| r.
Proof.
  es.
Qed.

Notation lh := (0inf<*<[1;1;1;1;0;1]).

Lemma LR r:
  lh <f| r -->+
  lh <* <[0;0] <* <[1]^^(0*3+4) |c> r.
Proof.
  es.
Qed.

Definition RH n :=
match mod3 n with
| mod3eq2 a => d*>w^^a*>w*>0inf
| mod3eq1 a => d*>w^^a*>d*>0inf
| mod3eq0 a => d*>w^^a*>[1]*>0inf
end.

Ltac rp a b := replace a with b in * by lia.

Ltac des_mod3 :=
  repeat
  match goal with
  | |- context[mod3 ?a] => destruct (mod3 a); try lia; subst
  end.

Lemma RH_Inc n:
  sideRLs tm h (RH n) (RH (1+n)).
Proof.
  unfold RH.
  des_mod3.
  - rp a0 a.
    esx.
  - rp a0 a.
    esx.
  - rp a0 (1+a).
    esx.
Qed.

Lemma RH_Incs k n:
  sideRLs tm (h^^k) (RH n) (RH (k+n)).
Proof.
  induction k.
  - esx.
  - eapply sideRLs_trans_S.
    1: apply IHk.
    apply RH_Inc.
Qed.

Definition RH0 n :=
match mod3 n with
| mod3eq2 a => w^^a*>w*>0inf
| mod3eq1 a => w^^a*>d*>0inf
| mod3eq0 a => w^^a*>[1]*>0inf
end.

Lemma RH_RH0 n:
  RH (3+n) = d *> w *> RH0 n.
Proof.
  unfold RH,RH0.
  des_mod3;
  rp a (1+a0); reflexivity.
Qed.

Lemma RH0_RL_0 l n:
  halts tm (l |c> RH0 (n*3)).
Proof.
  unfold RH0.
  des_mod3.
  rp a n.
  esx.
Qed.

Lemma RH0_RL_1 l n:
  l |c> RH0 (1+n*3) -->*
  l <* <[1]^^4 |> RC0 ([O]^^n) *> RH 1.
Proof.
  unfold RH0.
  des_mod3.
  rp a n.
  rewrite flat_map_lpow.
  es.
Qed.

Lemma RH0_RL_2 l n:
  l |c> RH0 (5+n*3) -->*
  l <* <[1]^^4 |> RC0 ([O]^^n) *> RH 1.
Proof.
  unfold RH0.
  des_mod3.
  rp a (1+n).
  rewrite flat_map_lpow.
  es.
Qed.

Lemma rot a r n:
  w^^a *> RC0 (map S r) *> RH (3+n) =
  RC1 (a::r) *> RH0 n.
Proof.
  gen a.
  induction r; intros.
  - rewrite RH_RH0.
    st; reflexivity.
  - specialize (IHr a).
    cbn[map flat_map] in *.
    repeat rewrite Str_app_assoc in *.
    rewrite <-IHr.
    reflexivity.
Qed.

Lemma rot0 r n:
  RC0 (map S r) *> RH (3+n) =
  RC1 (O::r) *> RH0 n.
Proof.
  apply (rot 0 r n).
Qed.

Lemma RC1_RL_0 l r n:
  halts tm (l |c> RC1 r *> RH0 (n*3)).
Proof.
  gen l.
  induction r; intros.
  - apply RH0_RL_0.
  - eapply halts_evstep.
    2:{
      cbn[RC1]; repeat rewrite Str_app_assoc.
      apply c_RR.
    }
    apply IHr.
Qed.

Definition RC2 '(r,n) :=
  RC0 r *> RH n.

Definition RInc2 '(r,n) r0 :=
  (RIncs0 1 (r0++r),n+2^(length (r0++r))).

Fixpoint RIncs2 r0 :=
match r0 with
| [] => ([],1%nat)
| x::r1 => RInc2 (RIncs2 r1) x
end.

Definition S' x :=
  lh <f| RC2 x.

Notation l0s1 := (fun n => [0]^^(n+1)++[1])%nat.

Lemma RInc2_spec l a x:
  l <* <[1]^^4 |> RC0 a *> RC2 x -->*
  l <f| RC2 (RInc2 x a).
Proof.
  unfold RC2,RInc2.
  destruct x as [r n].
  rewrite <-Str_app_assoc.
  rewrite <-flat_map_app.
  epose proof (RIncs0_spec 1 (a++r)) as I1.
  rewrite Nat.mul_1_l in I1.
  epose proof (RH_Incs _ n) as I2.
  eassert (I3:_) by (eapply segRLs_sideRLs_concat; eauto 1).
  clear I1 I2.
  eapply sideRLs_1 in I3.
  follow100 I3.
  follow LL.
  finish.
Qed.

Lemma RC1_RL_1 l r n:
  l |c> RC1 r *> RH0 (1+n*3) -->*
  l <f| RC2 (RIncs2 ((map l0s1 r)++[[O]^^n])).
Proof.
  gen l.
  induction r; intros.
  - follow RH0_RL_1.
    change (RH 1) with (RC2 ([],1%nat)).
    follow RInc2_spec.
    finish.
  - cbn[RC1].
    repeat rewrite Str_app_assoc.
    follow c_RR.
    follow IHr.
    follow f_LR.
    follow RInc2_spec.
    finish.
Qed.

Lemma RC1_RL_2 l r n:
  l |c> RC1 r *> RH0 (5+n*3) -->*
  l <f| RC2 (RIncs2 ((map l0s1 r)++[[O]^^n])).
Proof.
  gen l.
  induction r; intros.
  - follow RH0_RL_2.
    change (RH 1) with (RC2 ([],1%nat)).
    follow RInc2_spec.
    finish.
  - cbn[RC1].
    repeat rewrite Str_app_assoc.
    follow c_RR.
    follow IHr.
    follow f_LR.
    follow RInc2_spec.
    finish.
Qed.

Lemma BigStep0 r n:
  halts tm (S' (map S r,3+n*3)).
Proof.
  unfold S',RC2.
  eapply halts_evstep.
  2:{
    follow100 LR.
    rewrite rot0.
    finish.
  }
  apply RC1_RL_0.
Qed.

Lemma BigStep1 r n:
  S' (map S r,4+n*3) -->+
  S' (RIncs2 ((map l0s1 (O::O::r))++[[O]^^n])).
Proof.
  unfold S',RC2.
  follow10 LR.
  change (4+n*3) with (3+(1+n*3)).
  rewrite rot0.
  follow RC1_RL_1.
  follow f_LR.
  follow RInc2_spec.
  finish.
Qed.

Lemma BigStep2 r n:
  S' (map S r,8+n*3) -->+
  S' (RIncs2 ((map l0s1 (O::O::r))++[[O]^^n])).
Proof.
  unfold S',RC2.
  follow10 LR.
  change (8+n*3) with (3+(5+n*3)).
  rewrite rot0.
  follow RC1_RL_2.
  follow f_LR.
  follow RInc2_spec.
  finish.
Qed.

Lemma init:
  c0 -->*
  S' ([1;3;5],11)%nat.
Proof.
  esx.
Qed.

Inductive Z3 := z0 | z1 | z2.

Definition zadd a b :=
  match a,b with
  | z0,x | x,z0 => x
  | z1,z1 => z2
  | z1,z2 | z2,z1 => z0
  | z2,z2 => z1
  end.

Definition zopp a :=
  match a with z0 => z0 | z1 => z2 | z2 => z1 end.

Record Aff3 := aff3 { positive : bool; shift : Z3 }.

Definition acomp f g :=
  aff3 (Bool.eqb (positive f) (positive g))
    (zadd (shift f) (if positive f then shift g else zopp (shift g))).

Definition aid := aff3 true z0.
Definition aplus := aff3 true z1.
Definition aminus := aff3 true z2.
Definition areflect := aff3 false z1.

Lemma acomp_assoc f g h:
  acomp f (acomp g h) = acomp (acomp f g) h.
Proof.
  destruct f as [[] []],g as [[] []],h as [[] []]; reflexivity.
Qed.

Lemma acomp_id_l f: acomp aid f = f.
Proof. destruct f as [[] []]; reflexivity. Qed.

Lemma acomp_id_r f: acomp f aid = f.
Proof. destruct f as [[] []]; reflexivity. Qed.

Definition gletter (b:bool) := if b then aplus else areflect.
Definition kletter (b:bool) := if b then aminus else areflect.

Fixpoint asum (letter:bool->Aff3) (bs:list bool) : Aff3 :=
  match bs with
  | [] => aid
  | b::bs' => acomp (asum letter bs') (letter b)
  end.

Definition gsum bs := asum gletter bs.
Definition ksum bs := asum kletter bs.

Definition odds xs := map Nat.odd xs.
Definition G xs := gsum (odds xs).
Definition K xs := ksum (odds xs).

Lemma G_cons x xs:
  G (x::xs) = acomp (G xs) (gletter (Nat.odd x)).
Proof. reflexivity. Qed.

Lemma asum_app letter xs ys:
  asum letter (xs++ys) = acomp (asum letter ys) (asum letter xs).
Proof.
  induction xs as [|x xs IH].
  - cbn[asum]. symmetry. apply acomp_id_r.
  - change (acomp (asum letter (xs++ys)) (letter x) =
      acomp (asum letter ys) (acomp (asum letter xs) (letter x))).
    rewrite IH. symmetry. apply acomp_assoc.
Qed.

Lemma odds_app xs ys: odds (xs++ys) = odds xs++odds ys.
Proof. apply map_app. Qed.

Lemma asum_false_repeat letter:
  letter false = areflect ->
  forall n, asum letter (repeat false n) =
    if Nat.even n then aid else areflect.
Proof.
  intros Hletter n. induction n as [|n IH].
  - reflexivity.
  - cbn[repeat asum]. rewrite IH,Hletter,Nat.even_succ.
    unfold Nat.odd. destruct (Nat.even n); reflexivity.
Qed.

Definition normal_bits x := true :: repeat false (x-1) ++ [true].
Definition final_bits q := true :: repeat false (q-1).

Lemma gsum_normal x:
  0<x ->
  gsum (normal_bits x) = if Nat.odd x then aminus else areflect.
Proof.
  intros Hx. destruct x as [|x]; [lia|].
  unfold gsum,normal_bits. cbn[Nat.sub].
  cbn[asum gletter].
  rewrite asum_app,asum_false_repeat by reflexivity.
  cbn[asum gletter]. rewrite acomp_id_l.
  rewrite Nat.sub_0_r.
  rewrite Nat.odd_succ.
  destruct (Nat.even x); reflexivity.
Qed.

Lemma ksum_normal x:
  0<x ->
  ksum (normal_bits x) = if Nat.odd x then aplus else areflect.
Proof.
  intros Hx. destruct x as [|x]; [lia|].
  unfold ksum,normal_bits. cbn[Nat.sub].
  cbn[asum kletter].
  rewrite asum_app,asum_false_repeat by reflexivity.
  cbn[asum kletter]. rewrite acomp_id_l.
  rewrite Nat.sub_0_r.
  rewrite Nat.odd_succ.
  destruct (Nat.even x); reflexivity.
Qed.

Lemma gsum_final q:
  Nat.odd q = true -> gsum (final_bits q) = aplus.
Proof.
  intros Hq. destruct q as [|q]; [discriminate|].
  unfold gsum,final_bits. cbn[Nat.sub asum].
  rewrite asum_false_repeat by reflexivity.
  rewrite Nat.sub_0_r.
  rewrite Nat.odd_succ in Hq.
  rewrite Hq. reflexivity.
Qed.

Lemma ksum_final q:
  Nat.odd q = true -> ksum (final_bits q) = aminus.
Proof.
  intros Hq. destruct q as [|q]; [discriminate|].
  unfold ksum,final_bits. cbn[Nat.sub asum].
  rewrite asum_false_repeat by reflexivity.
  rewrite Nat.sub_0_r.
  rewrite Nat.odd_succ in Hq.
  rewrite Hq. reflexivity.
Qed.

Definition flip_head bs :=
  match bs with
  | [] => []
  | b::bs' => negb b::bs'
  end.

Lemma RIncs0_odds_even k xs:
  Nat.odd k = false -> odds (RIncs0 k xs) = odds xs.
Proof.
  revert k. induction xs as [|x xs IH]; intros k Hk.
  - reflexivity.
  - cbn[RIncs0 odds map]. rewrite Nat.odd_add,Hk. cbn[xorb].
    f_equal. apply IH.
    rewrite Nat.odd_mul,Hk. reflexivity.
Qed.

Lemma RIncs0_odds_1 xs:
  odds (RIncs0 1 xs) = flip_head (odds xs).
Proof.
  destruct xs as [|x xs].
  - reflexivity.
  - cbn[RIncs0 odds flip_head map].
    rewrite Nat.odd_add. cbn[xorb]. f_equal.
    apply RIncs0_odds_even. reflexivity.
Qed.

Lemma RIncs0_length' k xs:
  length (RIncs0 k xs) = length xs.
Proof.
  revert k. induction xs as [|x xs IH]; intros k; cbn[RIncs0 length].
  - reflexivity.
  - f_equal. apply IH.
Qed.

Lemma flip_head_app xs ys:
  xs<>[] -> flip_head (xs++ys) = flip_head xs++ys.
Proof.
  destruct xs; cbn[flip_head].
  - contradiction.
  - reflexivity.
Qed.

Definition block_bits blocks :=
  flat_map (fun b => flip_head (odds b)) blocks.

Lemma RIncs2_bits blocks:
  Forall (fun b => b<>[]) blocks ->
  odds (fst (RIncs2 blocks)) = block_bits blocks.
Proof.
  induction blocks as [|b blocks IH]; intros Hnonempty.
  - reflexivity.
  - inversion Hnonempty as [|? ? Hb Hbs]; subst.
    cbn[RIncs2]. destruct (RIncs2 blocks) as [r n] eqn:E. cbn.
    unfold RInc2. cbn.
    rewrite RIncs0_odds_1,odds_app,flip_head_app.
    2:{ intros Hnil. apply Hb. apply map_eq_nil in Hnil. exact Hnil. }
    specialize (IH Hbs). cbn in IH.
    change (odds r = block_bits blocks) in IH. rewrite IH.
    reflexivity.
Qed.

Definition step_blocks r q :=
  map l0s1 (O::O::r) ++ [lpow [O] q].

Lemma odds_zero_lpow n:
  odds (lpow [O] n) = repeat false n.
Proof.
  induction n; cbn[lpow repeat].
  - reflexivity.
  - rewrite odds_app,IHn. reflexivity.
Qed.

Lemma flip_l0s1 a:
  flip_head (odds (l0s1 a)) = normal_bits (S a).
Proof.
  change (flip_head (odds (lpow [O] (a+1) ++ [S O])) =
    normal_bits (S a)).
  rewrite odds_app,odds_zero_lpow.
  cbn[odds map]. replace (a+1) with (S a) by lia.
  destruct a; reflexivity.
Qed.

Lemma flip_zero_lpow q:
  0<q -> flip_head (odds (lpow [O] q)) = final_bits q.
Proof.
  intros Hq. destruct q as [|q]; [lia|].
  rewrite odds_zero_lpow.
  unfold final_bits. cbn[repeat flip_head Nat.sub].
  rewrite Nat.sub_0_r. reflexivity.
Qed.

Lemma block_bits_l0s1 r:
  block_bits (map l0s1 r) =
  flat_map (fun a => normal_bits (S a)) r.
Proof.
  unfold block_bits.
  induction r as [|a r IH].
  - reflexivity.
  - cbn[flat_map map]. rewrite flip_l0s1,IH. reflexivity.
Qed.

Definition expanded_bits r q :=
  [true;true;true;true] ++
  flat_map normal_bits r ++ final_bits q.

Lemma flat_map_map' {A B C} (f:B->list C) (g:A->B) xs:
  flat_map f (map g xs) = flat_map (fun x => f (g x)) xs.
Proof.
  induction xs; cbn[flat_map map].
  - reflexivity.
  - rewrite IHxs. reflexivity.
Qed.

Lemma block_bits_step_blocks r q:
  0<q ->
  block_bits (step_blocks r q) = expanded_bits (map S r) q.
Proof.
  intros Hq. unfold step_blocks,expanded_bits,block_bits.
  rewrite flat_map_app.
  fold (block_bits (map l0s1 (O::O::r))).
  rewrite block_bits_l0s1.
  cbn[flat_map]. rewrite flip_zero_lpow by exact Hq.
  rewrite flat_map_map'.
  cbn[flat_map map normal_bits Nat.sub].
  repeat rewrite app_nil_r. repeat rewrite app_assoc.
  reflexivity.
Qed.

Lemma l0s1_nonempty a: l0s1 a<>[].
Proof.
  change (lpow [O] (a+1) ++ [S O] <> []).
  intros H. apply app_eq_nil in H. destruct H as [_ H]. discriminate.
Qed.

Lemma step_blocks_nonempty r q:
  0<q -> Forall (fun b => b<>[]) (step_blocks r q).
Proof.
  intros Hq. unfold step_blocks.
  apply Forall_app. split.
  - apply Forall_map. induction (O::O::r); constructor; auto using l0s1_nonempty.
  - constructor.
    + destruct q; [lia|]. cbn[lpow]. discriminate.
    + constructor.
Qed.

Lemma gsum_app xs ys:
  gsum (xs++ys) = acomp (gsum ys) (gsum xs).
Proof. apply asum_app. Qed.

Lemma ksum_app xs ys:
  ksum (xs++ys) = acomp (ksum ys) (ksum xs).
Proof. apply asum_app. Qed.

Lemma gsum_middle xs:
  Forall (fun x => 0<x) xs ->
  gsum (flat_map normal_bits xs) = K xs.
Proof.
  induction xs as [|x xs IH]; intros Hpos.
  - reflexivity.
  - inversion Hpos as [|? ? Hx Hxs]; subst.
    cbn[flat_map]. rewrite gsum_app,gsum_normal by exact Hx.
    rewrite IH by exact Hxs.
    unfold K,ksum,odds. cbn[map asum kletter].
    destruct (Nat.odd x); reflexivity.
Qed.

Lemma ksum_middle xs:
  Forall (fun x => 0<x) xs ->
  ksum (flat_map normal_bits xs) = G xs.
Proof.
  induction xs as [|x xs IH]; intros Hpos.
  - reflexivity.
  - inversion Hpos as [|? ? Hx Hxs]; subst.
    cbn[flat_map]. rewrite ksum_app,ksum_normal by exact Hx.
    rewrite IH by exact Hxs.
    unfold G,gsum,odds. cbn[map asum gletter].
    destruct (Nat.odd x); reflexivity.
Qed.

Lemma expanded_summaries xs q:
  Forall (fun x => 0<x) xs -> Nat.odd q=true ->
  gsum (expanded_bits xs q) = acomp aplus (acomp (K xs) aplus) /\
  ksum (expanded_bits xs q) = acomp aminus (acomp (G xs) aminus).
Proof.
  intros Hpos Hq. unfold expanded_bits.
  rewrite !gsum_app,!ksum_app.
  rewrite gsum_final,ksum_final by exact Hq.
  rewrite gsum_middle,ksum_middle by exact Hpos.
  cbn[gsum ksum asum gletter kletter].
  change (acomp (acomp aplus (K xs)) aplus =
      acomp aplus (acomp (K xs) aplus) /\
    acomp (acomp aminus (G xs)) aminus =
      acomp aminus (acomp (G xs) aminus)).
  split; rewrite <-acomp_assoc; reflexivity.
Qed.

Lemma RIncs2_step_summaries r q:
  0<q -> Nat.odd q=true ->
  let y := RIncs2 (step_blocks r q) in
  G (fst y) = acomp aplus (acomp (K (map S r)) aplus) /\
  K (fst y) = acomp aminus (acomp (G (map S r)) aminus).
Proof.
  intros Hqpos Hqodd. destruct (RIncs2 (step_blocks r q)) as [r' n'] eqn:E.
  cbn. pose proof (RIncs2_bits (step_blocks r q)
    (step_blocks_nonempty r q Hqpos)) as Hbits.
  rewrite E in Hbits. cbn in Hbits.
  pose proof (block_bits_step_blocks r q Hqpos) as Hexpanded.
  assert (Hpos:Forall (fun x => 0<x) (map S r)).
  { apply Forall_forall. intros x Hin.
    apply in_map_iff in Hin. destruct Hin as [a [<- _]]. lia. }
  pose proof (expanded_summaries (map S r) q Hpos Hqodd) as Hsum.
  change (odds r' = block_bits (step_blocks r q)) in Hbits.
  rewrite Hexpanded in Hbits.
  destruct Hsum as [HG HK]. split.
  - change (gsum (odds r') =
      acomp aplus (acomp (K (map S r)) aplus)).
    rewrite Hbits. exact HG.
  - change (ksum (odds r') =
      acomp aminus (acomp (G (map S r)) aminus)).
    rewrite Hbits. exact HK.
Qed.

Lemma RIncs0_positive k xs:
  0<k -> Forall (fun x => 0<x) (RIncs0 k xs).
Proof.
  revert k. induction xs as [|x xs IH]; intros k Hk.
  - constructor.
  - cbn[RIncs0]. constructor.
    + lia.
    + apply IH. nia.
Qed.

Lemma RIncs2_positive blocks:
  Forall (fun x => 0<x) (fst (RIncs2 blocks)).
Proof.
  destruct blocks as [|b blocks].
  - constructor.
  - cbn[RIncs2]. destruct (RIncs2 blocks) as [r n]. cbn.
    apply RIncs0_positive. lia.
Qed.

Lemma RIncs2_snd_odd blocks:
  Forall (fun b => b<>[]) blocks ->
  Nat.odd (snd (RIncs2 blocks)) = true.
Proof.
  induction blocks as [|b blocks IH]; intros Hnonempty.
  - reflexivity.
  - inversion Hnonempty as [|? ? Hb Hblocks]; subst.
    cbn[RIncs2]. destruct (RIncs2 blocks) as [r n] eqn:E. cbn.
    unfold RInc2. cbn. rewrite Nat.odd_add.
    rewrite Nat.odd_pow.
    2:{ rewrite length_app. destruct b; [contradiction|cbn; lia]. }
    specialize (IH Hblocks). cbn in IH. rewrite IH. reflexivity.
Qed.

Lemma positive_mapS xs:
  Forall (fun x => 0<x) xs -> exists r, xs=map S r.
Proof.
  intros H. induction H as [|x xs Hx Hxs [r Hr]].
  - exists ([]:list nat). reflexivity.
  - destruct x as [|x]; [lia|]. exists (x::r). cbn[map]. now rewrite Hr.
Qed.

Definition zsucc x := zadd z1 x.

Fixpoint znat (n:nat) :=
  match n with O => z0 | S n' => zsucc (znat n') end.

Lemma zsucc_add a b:
  zsucc (zadd a b) = zadd (zsucc a) b.
Proof. destruct a,b; reflexivity. Qed.

Lemma znat_add a b:
  znat (a+b) = zadd (znat a) (znat b).
Proof.
  induction a as [|a IH].
  - reflexivity.
  - change (zsucc (znat (a+b)) = zadd (zsucc (znat a)) (znat b)).
    rewrite IH. apply zsucc_add.
Qed.

Lemma znat_pow2 n:
  znat (2^n) = if Nat.odd n then z2 else z1.
Proof.
  induction n as [|n IH].
  - reflexivity.
  - rewrite Nat.pow_succ_r'. replace (2*2^n) with (2^n+2^n) by lia.
    rewrite znat_add,IH,Nat.odd_succ. unfold Nat.odd.
    destruct (Nat.even n); reflexivity.
Qed.

Fixpoint total_len (blocks:list (list nat)) : nat :=
  match blocks with [] => O | b::bs => length b + total_len bs end.

Fixpoint block_num (blocks:list (list nat)) : nat :=
  match blocks with
  | [] => S O
  | b::bs => block_num bs + 2^(length b + total_len bs)
  end.

Lemma RIncs2_length blocks:
  length (fst (RIncs2 blocks)) = total_len blocks.
Proof.
  induction blocks as [|b blocks IH].
  - reflexivity.
  - cbn[RIncs2]. destruct (RIncs2 blocks) as [r n] eqn:E. cbn.
    unfold RInc2. cbn. rewrite RIncs0_length',length_app.
    cbn in IH. lia.
Qed.

Lemma RIncs2_snd blocks:
  snd (RIncs2 blocks) = block_num blocks.
Proof.
  induction blocks as [|b blocks IH].
  - reflexivity.
  - cbn[RIncs2]. destruct (RIncs2 blocks) as [r n] eqn:E. cbn.
    unfold RInc2. cbn. cbn in IH.
    pose proof (RIncs2_length blocks) as Hlen. rewrite E in Hlen. cbn in Hlen.
    rewrite IH,length_app,Hlen. reflexivity.
Qed.

Definition powres n := if Nat.odd n then z2 else z1.

Fixpoint block_res (blocks:list (list nat)) :=
  match blocks with
  | [] => z1
  | b::bs => zadd (block_res bs) (powres (length b + total_len bs))
  end.

Lemma znat_block_num blocks:
  znat (block_num blocks) = block_res blocks.
Proof.
  induction blocks as [|b blocks IH].
  - reflexivity.
  - cbn[block_num block_res]. rewrite znat_add,znat_pow2,IH. reflexivity.
Qed.

Lemma RIncs2_snd_res blocks:
  znat (snd (RIncs2 blocks)) = block_res blocks.
Proof. rewrite RIncs2_snd. apply znat_block_num. Qed.

Definition zmul a b :=
  match a,b with
  | z0,_ | _,z0 => z0
  | z1,x | x,z1 => x
  | z2,z2 => z1
  end.

Definition asign f := if positive f then z1 else z2.

Lemma zmul_assoc a b c:
  zmul a (zmul b c) = zmul (zmul a b) c.
Proof. destruct a,b,c; reflexivity. Qed.

Lemma zmul_comm a b: zmul a b = zmul b a.
Proof. destruct a,b; reflexivity. Qed.

Lemma asign_acomp f g:
  asign (acomp f g) = zmul (asign f) (asign g).
Proof. destruct f as [[] []],g as [[] []]; reflexivity. Qed.

Lemma powres_add a b:
  powres (a+b) = zmul (powres a) (powres b).
Proof.
  unfold powres. rewrite Nat.odd_add.
  destruct (Nat.odd a),(Nat.odd b); reflexivity.
Qed.

Lemma length_zero_lpow n:
  length (lpow [O] n) = n.
Proof.
  induction n; cbn[lpow length].
  - reflexivity.
  - rewrite length_app,IHn. cbn. lia.
Qed.

Lemma powres_length_l0s1 a:
  powres (length (l0s1 a)) = asign (gletter (Nat.odd (S a))).
Proof.
  change (powres (length (lpow [O] (a+1) ++ [S O])) =
    asign (gletter (Nat.odd (S a)))).
  rewrite length_app,length_zero_lpow. cbn[length].
  unfold powres,asign,gletter.
  replace (a+1+1) with (S (S a)) by lia.
  rewrite !Nat.odd_succ,Nat.even_succ. unfold Nat.odd.
  destruct (Nat.even a); reflexivity.
Qed.

Definition data_blocks r q := map l0s1 r ++ [lpow [O] q].

Lemma total_len_data r q:
  powres (total_len (data_blocks r q)) =
  zmul (asign (G (map S r))) (powres q).
Proof.
  induction r as [|a r IH].
  - unfold data_blocks. cbn[map total_len List.app].
    rewrite Nat.add_0_r.
    change (powres (length (lpow [O] q)) =
      zmul (asign aid) (powres q)).
    rewrite length_zero_lpow.
    change (powres q = zmul z1 (powres q)).
    destruct (powres q); reflexivity.
  - unfold data_blocks in *. cbn[map total_len List.app].
    rewrite powres_add,powres_length_l0s1,IH.
    unfold G,odds,gsum. cbn[map asum]. rewrite asign_acomp.
    rewrite zmul_assoc. f_equal. apply zmul_comm.
Qed.

Lemma block_res_data r q:
  Nat.odd q=true ->
  block_res (data_blocks r q) =
  zadd z1 (zadd (zopp (asign (G (map S r))))
    (zopp (shift (G (map S r))))).
Proof.
  intros Hq. induction r as [|a r IH].
  - unfold data_blocks. cbn[map block_res total_len List.app].
    rewrite Nat.add_0_r,length_zero_lpow. unfold powres. rewrite Hq.
    change (zadd z1 z2 = z0). reflexivity.
  - change (block_res (l0s1 a::data_blocks r q) =
      zadd z1 (zadd (zopp (asign (G (map S (a::r)))))
        (zopp (shift (G (map S (a::r))))))).
    cbn[block_res].
    rewrite IH,powres_add,powres_length_l0s1,total_len_data.
    unfold powres. rewrite Hq.
    cbn[map]. rewrite G_cons.
    rewrite Nat.odd_succ. unfold Nat.odd.
    destruct (G (map S r)) as [[] []];
      destruct (Nat.even a); reflexivity.
Qed.

Lemma block_res_step r q:
  Nat.odd q=true ->
  block_res (step_blocks r q) =
  zadd z1 (zopp (shift (G (map S r)))).
Proof.
  intros Hq.
  change (block_res (l0s1 O::l0s1 O::data_blocks r q) =
    zadd z1 (zopp (shift (G (map S r))))).
  cbn[block_res total_len].
  rewrite block_res_data by exact Hq.
  rewrite !powres_add,!powres_length_l0s1,total_len_data.
  unfold powres. rewrite Hq.
  destruct (G (map S r)) as [[] []]; reflexivity.
Qed.

Lemma RIncs2_step_snd_res r q:
  Nat.odd q=true ->
  znat (snd (RIncs2 (step_blocks r q))) =
  zadd z1 (zopp (shift (G (map S r)))).
Proof. intros Hq. rewrite RIncs2_snd_res. apply block_res_step,Hq. Qed.

Lemma pow2_ge2 n:
  0<n -> 2<=2^n.
Proof.
  intros Hn. change (2^1 <= 2^n).
  apply Nat.pow_le_mono_r; lia.
Qed.

Lemma block_num_lower blocks:
  Forall (fun b => b<>[]) blocks ->
  1+2*length blocks <= block_num blocks.
Proof.
  induction blocks as [|b blocks IH]; intros Hnonempty.
  - reflexivity.
  - inversion Hnonempty as [|? ? Hb Hblocks]; subst.
    cbn[block_num length]. specialize (IH Hblocks).
    assert (0 < length b + total_len blocks).
    { destruct b; [contradiction|cbn; lia]. }
    pose proof (pow2_ge2 (length b + total_len blocks) H) as Hpow.
    lia.
Qed.

Lemma RIncs2_step_lower r q:
  0<q -> 7<=snd (RIncs2 (step_blocks r q)).
Proof.
  intros Hq. rewrite RIncs2_snd.
  pose proof (block_num_lower (step_blocks r q)
    (step_blocks_nonempty r q Hq)) as Hlower.
  assert (3<=length (step_blocks r q)).
  { unfold step_blocks. rewrite length_app,length_map. cbn[length]. lia. }
  lia.
Qed.

Lemma znat_add3 n: znat (n+3) = znat n.
Proof.
  rewrite znat_add. change (zadd (znat n) z0 = znat n).
  destruct (znat n); reflexivity.
Qed.

Lemma znat_mul3 a: znat (a*3) = z0.
Proof.
  induction a as [|a IH].
  - reflexivity.
  - replace (S a*3) with (a*3+3) by lia. rewrite znat_add3,IH. reflexivity.
Qed.

Lemma znat_mod1 a: znat (1+a*3) = z1.
Proof. rewrite znat_add,znat_mul3. reflexivity. Qed.

Lemma znat_mod2 a: znat (2+a*3) = z2.
Proof. rewrite znat_add,znat_mul3. reflexivity. Qed.

Lemma znat_eq1 n:
  znat n=z1 -> exists a, n=1+a*3.
Proof.
  intros H. destruct (mod3 n); subst n.
  - rewrite znat_mul3 in H. discriminate.
  - eauto.
  - rewrite znat_mod2 in H. discriminate.
Qed.

Lemma znat_eq2 n:
  znat n=z2 -> exists a, n=2+a*3.
Proof.
  intros H. destruct (mod3 n); subst n.
  - rewrite znat_mul3 in H. discriminate.
  - rewrite znat_mod1 in H. discriminate.
  - eauto.
Qed.

Lemma shape_mod1 n:
  7<=n -> znat n=z1 -> exists a, n=4+a*3.
Proof.
  intros Hn Hz. destruct (znat_eq1 n Hz) as [a ->].
  exists (a-1). lia.
Qed.

Lemma shape_mod2 n:
  7<=n -> znat n=z2 -> exists a, n=8+a*3.
Proof.
  intros Hn Hz. destruct (znat_eq2 n Hz) as [a ->].
  exists (a-2). lia.
Qed.

Lemma odd_param1 a:
  Nat.odd (4+a*3)=true -> Nat.odd a=true.
Proof.
  intros H. rewrite Nat.odd_add,Nat.odd_mul in H.
  cbn in H. destruct (Nat.odd a); [reflexivity|discriminate].
Qed.

Lemma odd_param2 a:
  Nat.odd (8+a*3)=true -> Nat.odd a=true.
Proof.
  intros H. rewrite Nat.odd_add,Nat.odd_mul in H.
  cbn in H. destruct (Nat.odd a); [reflexivity|discriminate].
Qed.

Definition Inv '(r,n) :=
  Forall (fun x => 0<x) r /\
  7<=n /\ Nat.odd n=true /\
  ((znat n=z2 /\ G r=aid /\ K r=aid) \/
   (znat n=z1 /\ G r=aminus /\ K r=aplus)).

Lemma inv_progress x:
  Inv x -> exists y, S' x -->+ S' y /\ Inv y.
Proof.
  destruct x as [xs n].
  intros [Hpos [Hlower [Hodd Hphase]]].
  destruct Hphase as [[Hz [HG HK]]|[Hz [HG HK]]].
  - destruct (positive_mapS xs Hpos) as [r Hr]. subst xs.
    destruct (shape_mod2 n Hlower Hz) as [q Hn]. subst n.
    assert (Hqodd:Nat.odd q=true) by (apply odd_param2; exact Hodd).
    assert (Hqpos:0<q) by (destruct q; [discriminate|lia]).
    destruct (RIncs2 (step_blocks r q)) as [r' n'] eqn:E.
    exists (r',n'). split.
    + rewrite <-E. apply BigStep2.
    + unfold Inv. cbn.
      pose proof (RIncs2_positive (step_blocks r q)) as Hp.
      pose proof (RIncs2_step_lower r q Hqpos) as Hl.
      pose proof (RIncs2_snd_odd (step_blocks r q)
        (step_blocks_nonempty r q Hqpos)) as Ho.
      pose proof (RIncs2_step_summaries r q Hqpos Hqodd) as Hs.
      pose proof (RIncs2_step_snd_res r q Hqodd) as Hz'.
      rewrite E in Hp,Hl,Ho,Hs,Hz'. cbn in Hp,Hl,Ho,Hs,Hz'.
      rewrite HG,HK in Hs. rewrite HG in Hz'.
      change (G r'=aminus /\ K r'=aplus) in Hs.
      change (znat n'=z1) in Hz'.
      repeat split; try assumption. right. tauto.
  - destruct (positive_mapS xs Hpos) as [r Hr]. subst xs.
    destruct (shape_mod1 n Hlower Hz) as [q Hn]. subst n.
    assert (Hqodd:Nat.odd q=true) by (apply odd_param1; exact Hodd).
    assert (Hqpos:0<q) by (destruct q; [discriminate|lia]).
    destruct (RIncs2 (step_blocks r q)) as [r' n'] eqn:E.
    exists (r',n'). split.
    + rewrite <-E. apply BigStep1.
    + unfold Inv. cbn.
      pose proof (RIncs2_positive (step_blocks r q)) as Hp.
      pose proof (RIncs2_step_lower r q Hqpos) as Hl.
      pose proof (RIncs2_snd_odd (step_blocks r q)
        (step_blocks_nonempty r q Hqpos)) as Ho.
      pose proof (RIncs2_step_summaries r q Hqpos Hqodd) as Hs.
      pose proof (RIncs2_step_snd_res r q Hqodd) as Hz'.
      rewrite E in Hp,Hl,Ho,Hs,Hz'. cbn in Hp,Hl,Ho,Hs,Hz'.
      rewrite HG,HK in Hs. rewrite HG in Hz'.
      change (G r'=aid /\ K r'=aid) in Hs.
      change (znat n'=z2) in Hz'.
      repeat split; try assumption. left. tauto.
Qed.

Lemma init_inv: Inv ([1;3;5],11)%nat.
Proof.
  unfold Inv. cbn.
  split; [repeat constructor; lia|].
  split; [lia|]. split; [reflexivity|].
  left. vm_compute. tauto.
Qed.

Theorem nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt with (c':=S' ([1;3;5],11)%nat).
  - apply init.
  - eapply progress_nonhalt_cond with (P:=Inv).
    + apply inv_progress.
    + apply init_inv.
Qed.

End TM5.

