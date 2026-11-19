(** * Four shift-overflow counters halt: #229, #412, #636 and #145

  The four machines run a counter of binary words (digits 0001 / 0101, least significant first) separated by 011;
  a separator turns one carry into three increments of the word above it. Their tables share eight short step
  facts ([Facts]), from which one Section proves the INCREMENT (an increment entering a region it fits in, with the
  result computed by the chain law [add] in N) and the OVERFLOW (an increment that does not fit walks to the region's
  end, leaving the closed form [pend]). Each machine is then run from the blank tape by a checker made of plain
  steps, these two macros and a lazy run of separators whose remaining capacity is kept in base 3; [check_halts]
  proves that a run of the checker ending in a halt is a halt of the machine.

  At the halt the tape holds 31,259 / 31,260 / 22,451 / 46,185 ones in a span of 100,065 / 100,065 / 71,940 /
  147,950 cells (#229 / #412 / #636 / #145); an independently written simulator ends on the same tapes, cell for
  cell. - Claude (Heron) *)

From BusyCoq Require Import Individual62 BigUint Eqb Permute.
From Coq Require Import List NArith ZArith Lia PrimInt63.
Import ListNotations.
Set Default Goal Selector "!".

(* ---- tokens and the chain law *)
Local Open Scope sym_scope.
Inductive tok := T0 | T1 | TS.

Definition tw (t : tok) : list Sym :=
  match t with T0 => [0;0;0;1] | T1 => [0;1;0;1] | TS => [0;1;1] end.

Fixpoint tcells (ts : list tok) : list Sym :=
  match ts with [] => [] | t :: u => tw t ++ tcells u end.

Lemma tcells_app a b : tcells (a ++ b) = tcells a ++ tcells b.
Proof. induction a as [|t a IH]; cbn; [reflexivity|]. rewrite IH, app_assoc. reflexivity. Qed.

Local Open Scope N_scope.

(* x increments entering ts: digits are binary, least significant first; a separator triples the carry *)
Fixpoint add (x : N) (ts : list tok) : option (list tok) :=
  match x with
  | N0 => Some ts
  | Npos _ =>
    match ts with
    | [] => None
    | T0 :: u => option_map (cons (if N.odd x then T1 else T0)) (add (N.div2 x) u)
    | T1 :: u => option_map (cons (if N.odd x then T0 else T1)) (add (N.div2 (N.succ x)) u)
    | TS :: u => option_map (cons TS) (add (3 * x) u)
    end
  end.

Fixpoint cap (ts : list tok) : N :=
  match ts with
  | [] => 0
  | T0 :: u => 2 * cap u + 1
  | T1 :: u => 2 * cap u
  | TS :: u => cap u / 3
  end.

Definition tok_eq_dec (a b : tok) : {a = b} + {a <> b}.
Proof. decide equality. Defined.

Definition dig (n : N) : tok := if N.odd n then T1 else T0.
Definition dv (t : tok) : N := match t with T1 => 1 | _ => 0 end.

Lemma add_0 ts : add 0 ts = Some ts.
Proof. destruct ts; reflexivity. Qed.
Lemma add_nil x : x <> 0 -> add x [] = None.
Proof. destruct x; [lia|]. reflexivity. Qed.
Lemma add_TS x u : x <> 0 -> add x (TS :: u) = option_map (cons TS) (add (3 * x) u).
Proof. destruct x; [lia|]. reflexivity. Qed.
Lemma add_dig x t u : x <> 0 -> t <> TS ->
  add x (t :: u) = option_map (cons (dig (dv t + x))) (add ((dv t + x) / 2) u).
Proof.
  intros Hx Ht. destruct x as [|p]; [lia|]. destruct t; [| |congruence]; cbn [add dv].
  - rewrite N.add_0_l, N.div2_div. reflexivity.
  - replace (N.div2 (N.succ (N.pos p))) with ((1 + N.pos p) / 2) by (rewrite N.div2_div; f_equal; lia).
    unfold dig. rewrite N.odd_add. destruct (N.odd (N.pos p)); reflexivity.
Qed.

Lemma dig_ne n : dig n <> TS.
Proof. unfold dig. destruct (N.odd n); discriminate. Qed.
Lemma dv_dig n : dv (dig n) = n mod 2.
Proof.
  unfold dig. pose proof (N.div2_odd n) as E. rewrite N.div2_div in E.
  pose proof (N.div_mod n 2 ltac:(lia)). pose proof (N.mod_lt n 2 ltac:(lia)).
  destruct (N.odd n); cbn [dv N.b2n] in *; lia.
Qed.
Lemma mod2_odd n : n mod 2 = if N.odd n then 1 else 0.
Proof.
  pose proof (N.div2_odd n) as E. rewrite N.div2_div in E.
  pose proof (N.div_mod n 2 ltac:(lia)). pose proof (N.mod_lt n 2 ltac:(lia)).
  destruct (N.odd n); cbn [N.b2n] in E; lia.
Qed.
Lemma dig_mod n b : dig (n mod 2 + b) = dig (n + b).
Proof. unfold dig. rewrite !N.odd_add, mod2_odd. destruct (N.odd n); reflexivity. Qed.
Lemma cap_dig t u : t <> TS -> cap (t :: u) = 2 * cap u + 1 - dv t.
Proof. intro Ht. destruct t; [| |congruence]; cbn; lia. Qed.
Lemma dv_le t : dv t <= 1.
Proof. destruct t; cbn; lia. Qed.

Lemma le_div3 x c : x <= c / 3 <-> 3 * x <= c.
Proof. pose proof (N.div_mod c 3 ltac:(lia)). pose proof (N.mod_lt c 3 ltac:(lia)). lia. Qed.

Lemma option_map_ne {A B} (f : A -> B) o : option_map f o <> None <-> o <> None.
Proof. destruct o; cbn; split; congruence. Qed.

Lemma add_cap ts : forall x, add x ts <> None <-> x <= cap ts.
Proof.
  induction ts as [|t u IH]; intro x;
    (destruct (N.eq_dec x 0) as [->|Hx]; [rewrite add_0; split; [lia|discriminate]|]).
  - rewrite add_nil by exact Hx. cbn. split; [tauto|lia].
  - destruct (tok_eq_dec t TS) as [->|Ht].
    { rewrite add_TS, option_map_ne, IH by exact Hx; cbn [cap]; rewrite le_div3; lia. }
    rewrite add_dig, option_map_ne, IH, cap_dig by assumption;
    pose proof (dv_le t); pose proof (N.div_mod (dv t + x) 2 ltac:(lia));
    pose proof (N.mod_lt (dv t + x) 2 ltac:(lia)); split; lia.
Qed.

Lemma add_none x ts : add x ts = None -> cap ts < x.
Proof. intro H. destruct (N.le_gt_cases x (cap ts)) as [Hl|Hl]; [|exact Hl].
  exfalso. apply (proj2 (add_cap ts x) Hl). exact H. Qed.

Lemma add_some x ts : x <= cap ts -> exists u, add x ts = Some u.
Proof. intro H. apply add_cap in H. destruct (add x ts) as [u|]; [eauto|congruence]. Qed.

(* unfold one step of [add] in a hypothesis [add x (t :: ts) = Some u] *)
Ltac add_step H Hx :=
  match type of H with
  | add _ (TS :: _) = _ => rewrite add_TS in H by exact Hx
  | add _ (?t :: _) = _ => rewrite add_dig in H by (exact Hx || assumption || discriminate)
  end;
  match type of H with
  | option_map _ (add ?y ?v) = _ =>
    let E := fresh "E" in destruct (add y v) eqn:E; cbn [option_map] in H; [injection H as <-|discriminate]
  end.

Lemma add_length ts : forall x u, add x ts = Some u -> length u = length ts.
Proof.
  induction ts as [|t ts IH]; intros x u H;
    (destruct (N.eq_dec x 0) as [->|Hx]; [rewrite add_0 in H; injection H as <-; reflexivity|]).
  - rewrite add_nil in H; congruence.
  - destruct t; add_step H Hx; cbn; f_equal; eapply IH; eassumption.
Qed.

(* additivity: the chain law is an action of N *)
Lemma add_add ts : forall a b u, add a ts = Some u -> add b u = add (a + b) ts.
Proof.
  induction ts as [|t ts IH]; intros a b u H;
    (destruct (N.eq_dec a 0) as [->|Ha]; [rewrite add_0 in H; injection H as <-; reflexivity|]).
  - rewrite add_nil in H; congruence.
  - destruct (N.eq_dec b 0) as [->|Hb]; [rewrite add_0, N.add_0_r; congruence|].
    destruct (tok_eq_dec t TS) as [->|Ht].
    { add_step H Ha; rewrite !add_TS by lia; rewrite (IH _ _ _ E); do 2 f_equal; lia. }
    add_step H Ha;
      rewrite !add_dig by (lia || apply dig_ne || assumption);
      rewrite dv_dig, (IH _ _ _ E), dig_mod, N.add_assoc; f_equal; f_equal;
      pose proof (N.div_mod (dv t + a) 2 ltac:(lia));
      pose proof (N.div_mod (dv t + a + b) 2 ltac:(lia));
      pose proof (N.div_mod ((dv t + a) mod 2 + b) 2 ltac:(lia));
      pose proof (N.mod_lt (dv t + a) 2 ltac:(lia));
      pose proof (N.mod_lt (dv t + a + b) 2 ltac:(lia));
      pose proof (N.mod_lt ((dv t + a) mod 2 + b) 2 ltac:(lia)); lia.
Qed.

Lemma cap_add ts : forall x u, add x ts = Some u -> cap u = cap ts - x.
Proof.
  induction ts as [|t ts IH]; intros x u H;
    (destruct (N.eq_dec x 0) as [->|Hx]; [rewrite add_0 in H; injection H as <-; lia|]).
  - rewrite add_nil in H; congruence.
  - assert (Hc : x <= cap (t :: ts)) by (apply add_cap; congruence).
    destruct (tok_eq_dec t TS) as [->|Ht].
    { add_step H Hx; cbn [cap] in *; rewrite (IH _ _ E);
      rewrite le_div3 in Hc;
      pose proof (N.div_mod (cap ts) 3 ltac:(lia)); pose proof (N.mod_lt (cap ts) 3 ltac:(lia));
      pose proof (N.div_mod (cap ts - 3 * x) 3 ltac:(lia)); pose proof (N.mod_lt (cap ts - 3 * x) 3 ltac:(lia));
      lia. }
    add_step H Hx;
      rewrite cap_dig in * by (apply dig_ne || assumption);
      rewrite (cap_dig t ts Ht), dv_dig, (IH _ _ E);
      assert ((dv t + x) / 2 <= cap ts) by (apply add_cap; congruence);
      pose proof (dv_le t); pose proof (N.div_mod (dv t + x) 2 ltac:(lia));
      pose proof (N.mod_lt (dv t + x) 2 ltac:(lia)); lia.
Qed.

(* a run of k separators multiplies by 3^k *)
Lemma add_seps k : forall x ts,
  add x (repeat TS k ++ ts) = option_map (app (repeat TS k)) (add (3 ^ N.of_nat k * x) ts).
Proof.
  induction k as [|k IH]; intros x ts.
  - cbn [repeat app]. rewrite N.pow_0_r, N.mul_1_l. destruct (add x ts); reflexivity.
  - destruct (N.eq_dec x 0) as [->|Hx]; [rewrite N.mul_0_r, !add_0; reflexivity|].
    cbn [repeat app]. rewrite add_TS by exact Hx. rewrite IH.
    replace (3 ^ N.of_nat (S k) * x) with (3 ^ N.of_nat k * (3 * x))
      by (rewrite Nat2N.inj_succ, N.pow_succ_r'; lia).
    destruct (add _ ts); reflexivity.
Qed.

(* the cells an OVERFLOWING increment leaves: digits pending (1010), separators in their sending state *)
Definition sst (c : N) : list Sym :=
  match (c mod 3)%N with N0 => [S1;S0;S0] | Npos xH => [S1;S1;S0] | _ => [S0;S1;S0] end.

Fixpoint pend (ts : list tok) : list Sym :=
  match ts with
  | [] => []
  | TS :: u => sst (cap u) ++ pend u
  | _ :: u => [S1;S0;S1;S0] ++ pend u
  end.

Lemma pend_dig t u : t <> TS -> pend (t :: u) = [S1;S0;S1;S0] ++ pend u.
Proof. intro Ht. destruct t; [reflexivity|reflexivity|congruence]. Qed.

Lemma pend_add ts : forall x u, add x ts = Some u -> pend u = pend ts.
Proof.
  induction ts as [|t ts IH]; intros x u H;
    (destruct (N.eq_dec x 0) as [->|Hx]; [rewrite add_0 in H; injection H as <-; reflexivity|]).
  - rewrite add_nil in H; congruence.
  - destruct (tok_eq_dec t TS) as [->|Ht].
    { add_step H Hx; cbn [pend]; rewrite (IH _ _ E); f_equal; unfold sst; rewrite (cap_add _ _ _ E);
      assert (Hc : 3 * x <= cap ts) by (apply add_cap; congruence);
      replace ((cap ts - 3 * x) mod 3) with (cap ts mod 3); [reflexivity|];
      rewrite <- (N.mod_add (cap ts - 3 * x) x 3) by lia; f_equal; lia. }
    add_step H Hx; rewrite !pend_dig by (apply dig_ne || assumption);
      rewrite (IH _ _ E); reflexivity.
Qed.

(* capacity in one pass from the top, and the overflow cells the same way (head-outward order) *)
Definition cstep (t : tok) (c : N) : N := match t with T0 => 2 * c + 1 | T1 => 2 * c | TS => c / 3 end.
Fixpoint capr (racc : list tok) (c : N) : N := match racc with [] => c | t :: r => capr r (cstep t c) end.
Fixpoint capg (ts : list tok) (c : N) : N := match ts with [] => c | t :: u => cstep t (capg u c) end.
Lemma capg_app a b c : capg (a ++ b) c = capg a (capg b c).
Proof. induction a as [|t a IH]; cbn; [reflexivity|]. rewrite IH. reflexivity. Qed.
Lemma capr_spec r : forall c, capr r c = capg (rev r) c.
Proof. induction r as [|t r IH]; intro c; [reflexivity|]. cbn. rewrite IH, capg_app. reflexivity. Qed.
Lemma capg_cap ts : capg ts 0 = cap ts.
Proof. induction ts as [|t ts IH]; [reflexivity|]. cbn. rewrite IH. destruct t; reflexivity. Qed.

Definition tpend (t : tok) (c : N) : list Sym := match t with TS => sst c | _ => [S1;S0;S1;S0] end.
Fixpoint pendg (ts : list tok) (c : N) : list Sym :=
  match ts with [] => [] | t :: u => tpend t (capg u c) ++ pendg u c end.
Fixpoint pendr (rts : list tok) (c : N) : list Sym :=
  match rts with [] => [] | t :: r => rev (tpend t c) ++ pendr r (cstep t c) end.

Lemma pendg_pend ts : pendg ts 0 = pend ts.
Proof. induction ts as [|t ts IH]; [reflexivity|]. cbn [pendg pend]. rewrite IH, capg_cap. destruct t; reflexivity. Qed.

Lemma pendr_app a : forall b c, pendr (a ++ b) c = pendr a c ++ pendr b (capr a c).
Proof. induction a as [|t a IH]; intros b c; [reflexivity|]. cbn. rewrite IH, app_assoc. reflexivity. Qed.

Lemma pendr_rev ts : forall c, pendr (rev ts) c = rev (pendg ts c).
Proof.
  induction ts as [|t ts IH]; intro c; [reflexivity|]. cbn [rev pendg].
  rewrite pendr_app, IH, capr_spec, rev_involutive, rev_app_distr. cbn. rewrite app_nil_r. reflexivity.
Qed.

Lemma pendr_spec ts : pendr (rev ts) 0 = rev (pend ts).
Proof. rewrite pendr_rev, pendg_pend. reflexivity. Qed.

(* ---- the capacity in base 3 *)
Local Open Scope N_scope.

Inductive trit := g0 | g1 | g2.
Definition tv (t : trit) : N := match t with g0 => 0 | g1 => 1 | g2 => 2 end.
Definition triN (n : N) : trit := match n with N0 => g0 | Npos xH => g1 | _ => g2 end.

(* Hi: least significant first; Lo: most significant first; C = vhi Hi * 3^|Lo| + vlo Lo *)
Fixpoint vhi (h : list trit) : N := match h with [] => 0 | t :: h' => tv t + 3 * vhi h' end.
Fixpoint vlo (l : list trit) : N := match l with [] => 0 | t :: l' => tv t * 3 ^ N.of_nat (length l') + vlo l' end.
Definition cval (lo hi : list trit) : N := vhi hi * 3 ^ N.of_nat (length lo) + vlo lo.

Lemma tv_le t : tv t <= 2.
Proof. destruct t; cbn; lia. Qed.
Lemma tv_triN n : n < 3 -> tv (triN n) = n.
Proof. intro H. destruct n as [|[p|p|]]; cbn; lia. Qed.

(* a cons onto Hi that keeps it free of trailing zeros *)
Definition hcons (t : trit) (h : list trit) : list trit := match t, h with g0, [] => [] | _, _ => t :: h end.
Lemma vhi_hcons t h : vhi (hcons t h) = tv t + 3 * vhi h.
Proof. destruct t, h; cbn; lia. Qed.

(* subtract c from vhi h *)
Fixpoint subh (c : N) (h : list trit) : option (list trit) :=
  match c with
  | N0 => Some h
  | Npos _ =>
    match h with
    | [] => None
    | t :: h' =>
      if c mod 3 <=? tv t then option_map (hcons (triN (tv t - c mod 3))) (subh (c / 3) h')
      else option_map (hcons (triN (tv t + 3 - c mod 3))) (subh (c / 3 + 1) h')
    end
  end.

Lemma subh_spec h : forall c h', subh c h = Some h' -> vhi h' + c = vhi h.
Proof.
  induction h as [|t h IH]; intros c h' H.
  - destruct c; cbn in H; [injection H as <-; reflexivity|discriminate].
  - destruct c as [|p]; [cbn in H; injection H as <-; lia|].
    cbn [subh] in H. pose proof (N.mod_lt (N.pos p) 3 ltac:(lia)) as M3.
    pose proof (N.div_mod (N.pos p) 3 ltac:(lia)) as D3. pose proof (tv_le t).
    destruct (N.pos p mod 3 <=? tv t) eqn:Le;
      [apply N.leb_le in Le | apply N.leb_gt in Le];
      (destruct (subh _ h) as [h''|] eqn:E; [|discriminate]); cbn in H; injection H as <-;
      rewrite vhi_hcons, tv_triN by lia; specialize (IH _ _ E); cbn [vhi]; lia.
Qed.

Lemma vlo_app a b : vlo (a ++ b) = vlo a * 3 ^ N.of_nat (length b) + vlo b.
Proof.
  induction a as [|t a IH]; cbn [app vlo length]; [lia|].
  rewrite IH, length_app, Nat2N.inj_add, N.pow_add_r. lia.
Qed.

Lemma vhi_app a b : vhi (a ++ b) = vhi a + 3 ^ N.of_nat (length a) * vhi b.
Proof.
  induction a as [|t a IH]; cbn [app vhi length]; [lia|].
  rewrite IH, Nat2N.inj_succ, N.pow_succ_r'. lia.
Qed.

Lemma vlo_rev h : vlo (rev h) = vhi h.
Proof.
  induction h as [|t h IH]; cbn [rev vhi]; [reflexivity|].
  rewrite vlo_app, IH. cbn [vlo length]. rewrite N.pow_0_r. lia.
Qed.

(* moving one trit across the split keeps the value *)
Lemma cval_unpack t lo hi : cval (t :: lo) hi = cval lo (hcons t hi).
Proof.
  unfold cval. cbn [vlo length]. rewrite vhi_hcons, Nat2N.inj_succ, N.pow_succ_r'. lia.
Qed.

Definition hhd (h : list trit) : trit := match h with [] => g0 | t :: _ => t end.
Lemma vhi_hd_tl h : vhi h = tv (hhd h) + 3 * vhi (tl h).
Proof. destruct h; cbn; lia. Qed.

Lemma cval_repack lo hi : cval (hhd hi :: lo) (tl hi) = cval lo hi.
Proof.
  unfold cval. cbn [vlo length]. rewrite (vhi_hd_tl hi), Nat2N.inj_succ, N.pow_succ_r'. lia.
Qed.

(* the value split at level k: Lo gets exactly k trits *)
Fixpoint hnorm (h : list trit) : list trit := match h with [] => [] | t :: h' => hcons t (hnorm h') end.
Lemma vhi_hnorm h : vhi (hnorm h) = vhi h.
Proof. induction h as [|t h IH]; cbn; [reflexivity|]. rewrite vhi_hcons, IH. reflexivity. Qed.

Fixpoint splitk (k : nat) (t : list trit) (lo : list trit) : list trit * list trit :=
  match k with
  | O => (lo, hnorm t)
  | S k' => match t with [] => splitk k' [] (g0 :: lo) | d :: t' => splitk k' t' (d :: lo) end
  end.

Lemma splitk_spec k : forall t lo, length (fst (splitk k t lo)) = (k + length lo)%nat /\
  cval (fst (splitk k t lo)) (snd (splitk k t lo)) = vhi t * 3 ^ N.of_nat (length lo) + vlo lo.
Proof.
  induction k as [|k IH]; intros t lo.
  - cbn. split; [reflexivity|]. unfold cval. rewrite vhi_hnorm. reflexivity.
  - destruct t as [|d t]; cbn [splitk];
      [destruct (IH [] (g0 :: lo)) as [IH1 IH2] | destruct (IH t (d :: lo)) as [IH1 IH2]];
      rewrite IH1, IH2; cbn [length vhi vlo]; (split; [lia|]);
      rewrite Nat2N.inj_succ, N.pow_succ_r'; cbn [tv]; lia.
Qed.

(* conversions through BigUint, 5 trits (one base-243 digit) at a time *)
Definition tri5 (n : N) : list trit :=
  [triN (n mod 3); triN ((n / 3) mod 3); triN ((n / 9) mod 3); triN ((n / 27) mod 3); triN (n / 81)].

Lemma tri5_spec n : n < 243 -> length (tri5 n) = 5%nat /\ vhi (tri5 n) = n.
Proof.
  intro H. split; [reflexivity|]. unfold tri5. cbn [vhi].
  rewrite !tv_triN by (try apply N.mod_lt; try lia; apply N.Div0.div_lt_upper_bound; lia).
  pose proof (N.div_mod n 3 ltac:(lia)). pose proof (N.div_mod (n / 3) 3 ltac:(lia)).
  pose proof (N.div_mod (n / 9) 3 ltac:(lia)). pose proof (N.div_mod (n / 27) 3 ltac:(lia)).
  rewrite N.Div0.div_div in H1, H2, H3 by lia. cbn in H1, H2, H3. lia.
Qed.

Fixpoint b2t (fuel : nat) (b : BigUint) : option (list trit) :=
  if is0 b then Some [] else
  match fuel with
  | O => None
  | S f => let (q, r) := divmodc b 243 in option_map (app (tri5 (Z.to_N (Uint63.to_Z r)))) (b2t f q)
  end.

Fixpoint blen (b : BigUint) : nat := match b with BigUintNil => O | BigUintCons _ b' => S (blen b') end.

Definition trits (c : N) : option (list trit) := let b := ofZ (Z.of_N c) in b2t (7 * blen b + 1) b.

Lemma b2t_spec fuel : forall b t, b2t fuel b = Some t -> vhi t = Z.to_N (toZ b).
Proof.
  induction fuel as [|f IH]; intros b t H; cbn [b2t] in H; revert H;
    (destruct (is0_spec b) as [Hz|Hz]; intro H; [injection H as <-; cbn; rewrite Hz; reflexivity|]).
  - discriminate.
  - pose proof (divmodc_spec b 243 eq_refl eq_refl) as D. destruct (divmodc b 243) as [q r].
    destruct (b2t f q) as [t'|] eqn:E; [|discriminate]. cbn [option_map] in H. injection H as <-.
    destruct D as [D1 D2]. pose proof (toZ_ge0 b). pose proof (toZ_ge0 q).
    assert (Hr : (Z.to_N (Uint63.to_Z r) < 243)%N)
      by (rewrite D2; change (Uint63.to_Z 243) with 243%Z; pose proof (Z.mod_pos_bound (toZ b) 243); lia).
    destruct (tri5_spec _ Hr) as [L5 V5].
    transitivity (vhi (tri5 (Z.to_N (Uint63.to_Z r)) ++ t')); [reflexivity|].
    rewrite vhi_app, L5, V5, (IH _ _ E).
    change (Uint63.to_Z 243) with 243%Z in D1, D2.
    pose proof (Z.mod_pos_bound (toZ b) 243 ltac:(lia)).
    pose proof (Z.div_mod (toZ b) 243 ltac:(lia)).
    change (3 ^ N.of_nat 5)%N with 243%N. lia.
Qed.

Lemma trits_spec c t : trits c = Some t -> vhi t = c.
Proof. unfold trits. intro H. rewrite (b2t_spec _ _ _ H), ofZ_spec by lia. lia. Qed.

(* back: Horner, most significant first, base 243 where possible *)
Definition chunk (a b c d e : trit) : int := Uint63.of_Z (Z.of_N (81 * tv a + 27 * tv b + 9 * tv c + 3 * tv d + tv e)).
Definition tvi (t : trit) : int := match t with g0 => 0%uint63 | g1 => 1%uint63 | g2 => 2%uint63 end.

Fixpoint h5 (s : list trit) (acc : BigUint) : BigUint :=
  match s with
  | a :: b :: c :: d :: e :: s' => h5 s' (muladdc acc 243 (chunk a b c d e))
  | t :: s' => h5 s' (muladdc acc 3 (tvi t))
  | [] => acc
  end.

Lemma chunk_spec a b c d e : Uint63.to_Z (chunk a b c d e) = Z.of_N (81 * tv a + 27 * tv b + 9 * tv c + 3 * tv d + tv e).
Proof.
  unfold chunk. rewrite Uint63.of_Z_spec. apply Z.mod_small.
  pose proof (tv_le a); pose proof (tv_le b); pose proof (tv_le c); pose proof (tv_le d); pose proof (tv_le e).
  change Uint63.wB with (2 ^ 63)%Z. lia.
Qed.
Lemma tvi_spec t : Uint63.to_Z (tvi t) = Z.of_N (tv t).
Proof. destruct t; reflexivity. Qed.
Lemma chunk_le a b c d e : PrimInt63.leb (chunk a b c d e) 511%uint63 = true.
Proof.
  apply Uint63.leb_spec. rewrite chunk_spec. change (Uint63.to_Z 511) with 511%Z.
  pose proof (tv_le a); pose proof (tv_le b); pose proof (tv_le c); pose proof (tv_le d); pose proof (tv_le e).
  lia.
Qed.
Lemma tvi_le t : PrimInt63.leb (tvi t) 511%uint63 = true.
Proof. destruct t; reflexivity. Qed.

Lemma h5_spec n : forall s acc, (length s <= n)%nat ->
  toZ (h5 s acc) = (toZ acc * 3 ^ Z.of_nat (length s) + Z.of_N (vlo s))%Z.
Proof.
  induction n as [|n IH]; intros s acc Hn.
  { destruct s; [cbn; lia|cbn in Hn; lia]. }
  pose proof tv_le as TV.
  destruct s as [|a [|b [|c [|d [|e s']]]]]; cbn [h5].
  1: cbn; lia.
  5: { rewrite IH by (cbn in Hn; lia). rewrite muladdc_spec by (reflexivity || apply chunk_le).
       rewrite chunk_spec. cbn [length vlo].
       pose proof (TV a); pose proof (TV b); pose proof (TV c); pose proof (TV d); pose proof (TV e).
       rewrite !Nat2Z.inj_succ, !Z.pow_succ_r by lia. rewrite !Nat2N.inj_succ, !N.pow_succ_r'.
       change (Uint63.to_Z 243) with 243%Z. lia. }
  all: repeat (rewrite muladdc_spec by (reflexivity || apply tvi_le)); rewrite ?tvi_spec;
       change (Uint63.to_Z 3) with 3%Z; cbn [length vlo]; cbn [N.of_nat Z.of_nat];
       repeat match goal with t : trit |- _ => pose proof (TV t); generalize dependent t end; intros;
       cbn - [N.mul N.add Z.mul Z.add toZ tv]; lia.
Qed.

Definition cvalc (lo hi : list trit) : N := Z.to_N (toZ' (h5 (rev_append hi lo) BigUintNil)).

Lemma cvalc_spec lo hi : cvalc lo hi = cval lo hi.
Proof.
  unfold cvalc. rewrite toZ'_spec, (h5_spec (length (rev_append hi lo))) by lia. cbn [toZ].
  rewrite rev_append_rev, vlo_app, vlo_rev. unfold cval. lia.
Qed.

(* ---- the two macros, from eight step facts *)
Local Open Scope sym_scope.
(* the eight step facts a table needs *)
Definition Facts (tm : TM) : Prop :=
  (forall l r, (l << 0) {{A}}> [0;0;0;1] *> r -[ tm ]->+ l <{{A}} 1 >> [0;1;0;1] *> r) /\
  (forall l r, (l << 0) {{A}}> [0;1;0;1] *> 0 >> r -[ tm ]->+ (l << 0 << 1 << 0 << 1 << 0) {{A}}> 0 >> r) /\
  (forall l r, (l << 0 << 1 << 0 << 1) <{{A}} 1 >> r -[ tm ]->+ l <{{A}} 1 >> [0;0;0;1] *> r) /\
  (forall l r, (l << 0) {{A}}> [0;1;1] *> 0 >> r -[ tm ]->+ (l << 0 << 1 << 0 << 0) {{A}}> 0 >> r) /\
  (forall l r, (l << 0 << 1 << 0) <{{A}} 1 >> 0 >> r -[ tm ]->+ (l << 0 << 1 << 1 << 0) {{A}}> 0 >> r) /\
  (forall l r, (l << 0 << 1 << 1) <{{A}} 1 >> 0 >> r -[ tm ]->+ (l << 0 << 0 << 1 << 0) {{A}}> 0 >> r) /\
  (forall l r, (l << 0 << 0 << 1) <{{A}} 1 >> r -[ tm ]->+ l <{{A}} 1 >> [0;1;1] *> r) /\
  (forall l r, l {{B}}> 1 >> 0 >> r -[ tm ]->+ (l << 0) {{A}}> 0 >> r).

Section Macro.
Variable tm : TM.
Local Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Local Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Hypothesis HF : Facts tm.

Lemma tcells_hd ts r : ts <> [] -> exists r', tcells ts *> r = 0 >> r'.
Proof. destruct ts as [|t ts]; [congruence|]. intros _. destruct t; eexists; reflexivity. Qed.

Lemma add1_nonempty ts u : add 1 ts = Some u -> ts <> [] /\ u <> [].
Proof.
  intro H. destruct ts as [|t ts]; [discriminate|]. split; [discriminate|].
  pose proof (add_length _ _ _ H) as L. destruct u; [discriminate|discriminate].
Qed.

Lemma add_three ts u : add 3 ts = Some u ->
  exists u1 u2, add 1 ts = Some u1 /\ add 1 u1 = Some u2 /\ add 1 u2 = Some u.
Proof.
  intro H. assert (Hc : (3 <= cap ts)%N) by (apply add_cap; congruence).
  destruct (add_some 1 ts ltac:(lia)) as [u1 H1].
  destruct (add_some 1 u1) as [u2 H2]; [rewrite (cap_add _ _ _ H1); lia|].
  exists u1, u2. repeat split; [exact H1|exact H2|].
  rewrite (add_add _ _ _ _ H2), (add_add _ _ _ _ H1). exact H.
Qed.

(* one increment entering a clean region that absorbs it *)
Lemma inc_A0 n : forall ts u l r, (length ts <= n)%nat -> add 1 ts = Some u ->
  (l << 0) {{A}}> tcells ts *> r -->+ l <{{A}} 1 >> tcells u *> r.
Proof.
  pose proof HF as (K0inc & K1go & K1back & TSs1 & TSs2 & TSs3 & TSfin & B1A0).
  induction n as [|n IH]; intros ts u l r Hn H.
  { destruct ts; [discriminate|cbn in Hn; lia]. }
  destruct ts as [|t ts]; [discriminate|]. cbn [length] in Hn.
  destruct t.
  - cbn in H. rewrite add_0 in H. injection H as <-.
    cbn [tcells tw]. rewrite !Str_app_assoc. apply K0inc.
  - cbn in H. destruct (add 1 ts) as [u'|] eqn:E; [|discriminate]. injection H as <-.
    destruct (tcells_hd ts r (proj1 (add1_nonempty _ _ E))) as [r' Hr].
    cbn [tcells tw]. rewrite !Str_app_assoc.
    eapply progress_trans. { rewrite Hr. apply K1go. }
    rewrite <- Hr. eapply progress_trans. { apply (IH ts u' (l << 0 << 1 << 0 << 1) r); [lia|exact E]. }
    apply K1back.
  - cbn in H. destruct (add 3 ts) as [u3|] eqn:E; [|discriminate]. injection H as <-.
    destruct (add_three _ _ E) as (u1 & u2 & E1 & E2 & E3).
    pose proof (add_length _ _ _ E1) as L1. pose proof (add_length _ _ _ E2) as L2.
    cbn [tcells tw]. rewrite !Str_app_assoc.
    destruct (tcells_hd ts r (proj1 (add1_nonempty _ _ E1))) as [r0 Hr0].
    destruct (tcells_hd u1 r (proj1 (add1_nonempty _ _ E2))) as [r1 Hr1].
    destruct (tcells_hd u2 r (proj1 (add1_nonempty _ _ E3))) as [r2 Hr2].
    eapply progress_trans. { rewrite Hr0. apply TSs1. }
    rewrite <- Hr0. eapply progress_trans. { apply (IH ts u1 (l << 0 << 1 << 0) r); [lia|exact E1]. }
    eapply progress_trans. { rewrite Hr1. apply TSs2. }
    rewrite <- Hr1. eapply progress_trans. { apply (IH u1 u2 (l << 0 << 1 << 1) r); [lia|exact E2]. }
    eapply progress_trans. { rewrite Hr2. apply TSs3. }
    rewrite <- Hr2. eapply progress_trans. { apply (IH u2 u3 (l << 0 << 0 << 1) r); [lia|exact E3]. }
    apply TSfin.
Qed.

(* one increment entering a region of capacity 0 walks to its end *)
Lemma ovf_A0 n : forall ts l r, (length ts <= n)%nat -> cap ts = 0%N ->
  (l << 0) {{A}}> tcells ts *> 0 >> r -->* (l << 0) <* rev (pend ts) {{A}}> 0 >> r.
Proof.
  pose proof HF as (K0inc & K1go & K1back & TSs1 & TSs2 & TSs3 & TSfin & B1A0).
  induction n as [|n IH]; intros ts l r Hn H.
  { destruct ts; [apply evstep_refl|cbn in Hn; lia]. }
  destruct ts as [|t ts]; [apply evstep_refl|]. cbn [length] in Hn.
  destruct t; cbn [cap] in H.
  - lia.
  - assert (Hc : cap ts = 0%N) by lia.
    cbn [tcells tw pend]. rewrite !Str_app_assoc, rev_app_distr, Str_app_assoc.
    assert (Hr : exists r', tcells ts *> 0 >> r = 0 >> r')
      by (destruct ts as [|t' ts']; [eexists; reflexivity|apply tcells_hd; discriminate]).
    destruct Hr as [r' Hr].
    eapply evstep_trans. { apply progress_evstep. rewrite Hr. apply K1go. }
    rewrite <- Hr. apply (IH ts (l << 0 << 1 << 0 << 1) r); [lia|exact Hc].
  - (* the separator sends cap ts + 1 times; the last send overflows *)
    assert (Hc : (cap ts < 3)%N) by (pose proof (N.div_mod (cap ts) 3 ltac:(lia)); lia).
    cbn [tcells tw pend]. rewrite !Str_app_assoc, rev_app_distr, Str_app_assoc.
    assert (Hr : forall v, exists r', tcells v *> 0 >> r = 0 >> r')
      by (intro v; destruct v as [|t' v']; [eexists; reflexivity|apply tcells_hd; discriminate]).
    destruct (Hr ts) as [r0 Hr0].
    eapply evstep_trans. { apply progress_evstep. rewrite Hr0. apply TSs1. }
    rewrite <- Hr0. unfold sst.
    destruct (N.eq_dec (cap ts) 0) as [C0|C0].
    { rewrite C0. cbn. apply (IH ts (l << 0 << 1 << 0) r); [lia|exact C0]. }
    destruct (add_some 1 ts ltac:(lia)) as [u1 E1].
    pose proof (add_length _ _ _ E1) as L1.
    eapply evstep_trans. { apply progress_evstep. apply (inc_A0 (length ts) ts u1 (l << 0 << 1 << 0)); [lia|exact E1]. }
    destruct (Hr u1) as [r1 Hr1].
    eapply evstep_trans. { apply progress_evstep. rewrite Hr1. apply TSs2. }
    rewrite <- Hr1.
    destruct (N.eq_dec (cap ts) 1) as [C1|C1].
    { rewrite C1. cbn. rewrite <- (pend_add _ _ _ E1).
      apply (IH u1 (l << 0 << 1 << 1) r); [lia|rewrite (cap_add _ _ _ E1); lia]. }
    destruct (add_some 1 u1) as [u2 E2]; [rewrite (cap_add _ _ _ E1); lia|].
    pose proof (add_length _ _ _ E2) as L2.
    eapply evstep_trans. { apply progress_evstep. apply (inc_A0 (length u1) u1 u2 (l << 0 << 1 << 1)); [lia|exact E2]. }
    destruct (Hr u2) as [r2 Hr2].
    eapply evstep_trans. { apply progress_evstep. rewrite Hr2. apply TSs3. }
    rewrite <- Hr2.
    replace (cap ts mod 3)%N with 2%N by (rewrite N.mod_small by lia; lia). cbn.
    rewrite <- (pend_add _ _ _ E1), <- (pend_add _ _ _ E2).
    apply (IH u2 (l << 0 << 0 << 1) r); [lia|rewrite (cap_add _ _ _ E2), (cap_add _ _ _ E1); lia].
Qed.

(* the same from the B1 entry (state B on a 1, the region right of it) *)
Lemma inc_B1 ts u l r : add 1 ts = Some u ->
  l {{B}}> 1 >> tcells ts *> r -->+ l <{{A}} 1 >> tcells u *> r.
Proof.
  pose proof HF as (K0inc & K1go & K1back & TSs1 & TSs2 & TSs3 & TSfin & B1A0).
  intro H. destruct (tcells_hd ts r (proj1 (add1_nonempty _ _ H))) as [r' Hr].
  eapply progress_trans. { rewrite Hr. apply B1A0. }
  rewrite <- Hr. apply (inc_A0 (length ts)); [lia|exact H].
Qed.

Lemma ovf_B1 ts l r : cap ts = 0%N ->
  l {{B}}> 1 >> tcells ts *> 0 >> r -->+ (l << 0) <* rev (pend ts) {{A}}> 0 >> r.
Proof.
  pose proof HF as (K0inc & K1go & K1back & TSs1 & TSs2 & TSs3 & TSfin & B1A0).
  intro H. assert (Hr : exists r', tcells ts *> 0 >> r = 0 >> r')
    by (destruct ts as [|t' ts']; [eexists; reflexivity|apply tcells_hd; discriminate]).
  destruct Hr as [r' Hr].
  eapply progress_evstep_trans. { rewrite Hr. apply B1A0. }
  rewrite <- Hr. apply (ovf_A0 (length ts)); [lia|exact H].
Qed.

End Macro.

(* ---- the checker *)
Local Open Scope nat_scope.
Local Open Scope bool_scope.
(* ---- the chain law over cells *)
Definition tok_of (M : list Sym) : option (tok * list Sym) :=
  match M with
  | S0 :: S0 :: S0 :: S1 :: M' => Some (T0, M')
  | S0 :: S1 :: S0 :: S1 :: M' => Some (T1, M')
  | S0 :: S1 :: S1 :: M' => Some (TS, M')
  | _ => None
  end.

Lemma tok_of_spec M t M' : tok_of M = Some (t, M') -> M = tw t ++ M'.
Proof.
  destruct M as [|[] [|[] [|[] [|[] M]]]]; cbn; intro H; try discriminate; injection H as <- <-; reflexivity.
Qed.

(* the cell after a non-token is decided: 0 and at least 4 cells, or nothing follows (bl) *)
Definition stop (bl : bool) (M : list Sym) : bool :=
  match M with [] => bl | S0 :: _ :: _ :: _ :: _ => true | S0 :: _ => bl | _ => false end.

Lemma stop_spec bl M : stop bl M = true -> (bl = true /\ M = []) \/ exists M', M = S0 :: M'.
Proof. destruct M as [|[] [|? [|? [|? M]]]]; cbn; intro H; try discriminate; eauto. Qed.

Definition tnew (t : tok) (x : N) : tok := match t with TS => TS | _ => dig (dv t + x) end.
Definition tcar (t : tok) (x : N) : N := match t with TS => 3 * x | _ => (dv t + x) / 2 end.

Lemma add_cons x t u : x <> 0%N -> add x (t :: u) = option_map (cons (tnew t x)) (add (tcar t x) u).
Proof.
  intro Hx. destruct (tok_eq_dec t TS) as [->|Ht]; [apply add_TS; exact Hx|].
  rewrite add_dig by assumption. destruct t; [reflexivity|reflexivity|congruence].
Qed.

Inductive mres := MInc (M' : list Sym) | MExit (M' : list Sym) (c : N) | MOvf (ts : list tok) (rest : list Sym) | MNo.

Definition mcons (w : list Sym) (t : tok) (r : mres) : mres :=
  match r with
  | MInc M' => MInc (w ++ M') | MExit M' c => MExit (w ++ M') c
  | MOvf ts rest => MOvf (t :: ts) rest | MNo => MNo
  end.

Fixpoint addm (bl : bool) (x : N) (M : list Sym) : mres :=
  match x with
  | N0 => MInc M
  | Npos _ =>
    match M with
    | S0 :: S0 :: S0 :: S1 :: M' => mcons (tw (dig x)) T0 (addm bl (x / 2) M')
    | S0 :: S1 :: S0 :: S1 :: M' => mcons (tw (dig (1 + x))) T1 (addm bl ((1 + x) / 2) M')
    | S0 :: S1 :: S1 :: M' => mcons [S0;S1;S1] TS (addm bl (3 * x) M')
    | [] => if bl then MOvf [] [] else MExit [] x
    | _ => if stop bl M then MOvf [] M else MNo
    end
  end.

Lemma addm_eq bl x M : x <> 0%N -> addm bl x M =
  match tok_of M with
  | Some (t, M') => mcons (tw (tnew t x)) t (addm bl (tcar t x) M')
  | None => match M with [] => if bl then MOvf [] [] else MExit [] x | _ => if stop bl M then MOvf [] M else MNo end
  end.
Proof. intro Hx. destruct x as [|p]; [lia|]. destruct M as [|[] [|[] [|[] [|[] M]]]]; reflexivity. Qed.

Lemma addm_0 bl M : addm bl 0 M = MInc M.
Proof. destruct M as [|[] [|[] [|[] [|[] M]]]]; reflexivity. Qed.

Lemma option_map_app_nil (o : option (list tok)) : option_map (app []) o = o.
Proof. destruct o; reflexivity. Qed.

Lemma addm_spec bl n : forall M x, (length M <= n)%nat ->
  match addm bl x M with
  | MInc M' => exists ts u rest, M = tcells ts ++ rest /\ M' = tcells u ++ rest /\ add x ts = Some u
  | MExit M' c => bl = false /\ exists ts u, M = tcells ts /\ M' = tcells u /\
                  forall v, add x (ts ++ v) = option_map (app u) (add c v)
  | MOvf ts rest => M = tcells ts ++ rest /\ add x ts = None /\
                    ((bl = true /\ rest = []) \/ exists rest', rest = S0 :: rest')
  | MNo => True
  end.
Proof.
  induction n as [|n IH]; intros M x Hn;
    (destruct (N.eq_dec x 0) as [->|Hx];
     [rewrite addm_0; exists (@nil tok), (@nil tok), M; split; [reflexivity|split; reflexivity]|]).
  - destruct M; [|cbn in Hn; lia]. rewrite addm_eq by exact Hx. cbn.
    destruct bl; [|split; [reflexivity|]]; [split; [reflexivity|]; rewrite add_nil by exact Hx; auto|].
    exists (@nil tok), (@nil tok). repeat split. intro v. cbn. rewrite option_map_app_nil. reflexivity.
  - rewrite addm_eq by exact Hx. destruct (tok_of M) as [[t M']|] eqn:T.
    + apply tok_of_spec in T. subst M. rewrite length_app in Hn.
      assert (Lt : (length M' <= n)%nat) by (destruct t; cbn in Hn; lia).
      specialize (IH M' (tcar t x) Lt).
      destruct (addm bl (tcar t x) M') as [M2|M2 c|ts rest|]; cbn [mcons].
      * destruct IH as (ts & u & rest & -> & -> & E). exists (t :: ts), (tnew t x :: u), rest.
        rewrite add_cons, E by exact Hx. cbn [tcells]. rewrite !app_assoc.
        split; [reflexivity|]. split; [destruct t; reflexivity|reflexivity].
      * destruct IH as (Hbl & ts & u & -> & -> & E). split; [exact Hbl|].
        exists (t :: ts), (tnew t x :: u). split; [reflexivity|]. split; [destruct t; reflexivity|].
        intro v. cbn [app]. rewrite add_cons by exact Hx. rewrite E. destruct (add c v); reflexivity.
      * destruct IH as (-> & E & R). split; [cbn [tcells]; rewrite app_assoc; reflexivity|].
        rewrite add_cons, E by exact Hx. split; [reflexivity|exact R].
      * exact I.
    + destruct M as [|a M0].
      * destruct bl; [split; [reflexivity|]; rewrite add_nil by exact Hx; auto|].
        split; [reflexivity|]. exists (@nil tok), (@nil tok). repeat split. intro v. cbn. rewrite option_map_app_nil. reflexivity.
      * destruct (stop bl (a :: M0)) eqn:Sp; [|exact I].
        split; [reflexivity|]. rewrite add_nil by exact Hx. split; [reflexivity|].
        destruct (stop_spec _ _ Sp) as [[_ ?]|?]; [discriminate|right; exact H].
Qed.

(* ---- separators, tokenizing, capacity *)
Fixpoint ks (k : nat) : list Sym := match k with O => [] | S k' => S0 :: S1 :: S1 :: ks k' end.

Lemma ks_tcells k : ks k = tcells (repeat TS k).
Proof. induction k as [|k IH]; [reflexivity|]. cbn. rewrite IH. reflexivity. Qed.
Lemma ks_S_r k : ks (S k) = ks k ++ [S0;S1;S1].
Proof.
  induction k as [|k IH]; [reflexivity|].
  change (ks (S (S k))) with (S0 :: S1 :: S1 :: ks (S k)). rewrite IH at 1. reflexivity.
Qed.

Fixpoint leadks (cs : list Sym) (k : nat) : nat * list Sym :=
  match cs with S0 :: S1 :: S1 :: cs' => leadks cs' (S k) | _ => (k, cs) end.
Lemma leadks_spec : forall cs k, ks k ++ cs = ks (fst (leadks cs k)) ++ snd (leadks cs k).
Proof.
  fix IH 1. intros cs k. destruct cs as [|[] [|[] [|[] cs]]]; try reflexivity.
  cbn [leadks]. rewrite <- IH, ks_S_r, <- app_assoc. reflexivity.
Qed.

Fixpoint toks (cs : list Sym) (racc : list tok) : list tok * list Sym :=
  match cs with
  | S0 :: S0 :: S0 :: S1 :: cs' => toks cs' (T0 :: racc)
  | S0 :: S1 :: S0 :: S1 :: cs' => toks cs' (T1 :: racc)
  | S0 :: S1 :: S1 :: cs' => toks cs' (TS :: racc)
  | _ => (racc, cs)
  end.
Lemma toks_eq cs racc : toks cs racc =
  match tok_of cs with Some (t, cs') => toks cs' (t :: racc) | None => (racc, cs) end.
Proof. destruct cs as [|[] [|[] [|[] [|[] cs]]]]; reflexivity. Qed.

Lemma toks_spec n : forall cs racc, (length cs <= n)%nat ->
  tcells (rev racc) ++ cs = tcells (rev (fst (toks cs racc))) ++ snd (toks cs racc).
Proof.
  induction n as [|n IH]; intros cs racc Hn; rewrite toks_eq;
    (destruct (tok_of cs) as [[t cs']|] eqn:T; [|reflexivity]);
    apply tok_of_spec in T; subst cs; rewrite length_app in Hn.
  - destruct t; cbn in Hn; lia.
  - rewrite <- IH by (destruct t; cbn in Hn; lia). cbn [rev]. rewrite tcells_app, <- app_assoc.
    cbn [tcells]. rewrite app_nil_r. reflexivity.
Qed.

Definition lead6 (M : list Sym) : bool :=
  match M with
  | S0::S1::S1::S0::S1::S1::S0::S1::S1::S0::S1::S1::S0::S1::S1::S0::S1::S1::_ => true
  | _ => false
  end.

(* ---- the checker state *)
Record st := mkst { sq : Q; sL : list Sym; sh : Sym; sM : list Sym; sLo : list trit; sHi : list trit;
                    sRt : list tok; sRr : list Sym; scp : N }.

Definition regv (s : st) : list tok :=
  match add (scp s - cval (sLo s) (sHi s)) (sRt s) with Some u => u | None => [] end.
Definition rside (s : st) : list Sym := sM s ++ ks (length (sLo s)) ++ tcells (regv s) ++ sRr s.
Definition conf (s : st) : Q * tape := (sq s, (sL s *> 0inf, sh s, rside s *> 0inf)).
Definition WF (s : st) : Prop := (cval (sLo s) (sHi s) <= scp s /\ scp s = cap (sRt s))%N.

Definition regc (s : st) : list Sym :=
  tcells (match add (scp s - cvalc (sLo s) (sHi s)) (sRt s) with Some u => u | None => [] end) ++ sRr s.
Definition rsidec (s : st) : list Sym := sM s ++ ks (length (sLo s)) ++ regc s.
Lemma rsidec_spec s : rsidec s = rside s.
Proof. unfold rsidec, rside, regc, regv. rewrite cvalc_spec, app_assoc. reflexivity. Qed.

Lemma WF_add s : WF s -> add (scp s - cval (sLo s) (sHi s)) (sRt s) = Some (regv s).
Proof.
  intros [H1 H2]. unfold regv. destruct (add_some (scp s - cval (sLo s) (sHi s)) (sRt s)) as [u E]; [lia|].
  rewrite E. reflexivity.
Qed.

Definition blank (s : st) : bool := match sLo s, sRt s, sRr s with [], [], [] => true | _, _, _ => false end.
Lemma blank_spec s : WF s -> blank s = true -> rside s = sM s.
Proof.
  intros [H1 H2] B. unfold blank in B. destruct (sLo s) eqn:Lo, (sRt s) eqn:Rt, (sRr s) eqn:Rr; try discriminate.
  unfold rside, regv. rewrite Lo, Rt, Rr. cbn [cap] in H2. rewrite H2. cbn. rewrite !app_nil_r. reflexivity.
Qed.

(* ---- plain moves *)
Definition mvR (s : st) (w : Sym) (q' : Q) : st :=
  match sM s with
  | x :: M' => mkst q' (w :: sL s) x M' (sLo s) (sHi s) (sRt s) (sRr s) (scp s)
  | [] =>
    match sLo s with
    | t :: Lo' => mkst q' (w :: sL s) S0 [S1;S1] Lo' (hcons t (sHi s)) (sRt s) (sRr s) (scp s)
    | [] =>
      match regc s with
      | x :: cs => mkst q' (w :: sL s) x cs [] [] [] [] 0
      | [] => mkst q' (w :: sL s) S0 [] [] [] [] [] 0
      end
    end
  end.

Definition is11 (M : list Sym) : bool := match M with [S1; S1] => true | _ => false end.
Lemma is11_spec M : is11 M = true -> M = [S1; S1].
Proof. destruct M as [|[] [|[] [|? ?]]]; cbn; intro H; try congruence; reflexivity. Qed.
Definition is0 (w : Sym) : bool := match w with S0 => true | S1 => false end.
Lemma is0_spec w : is0 w = true -> w = S0.
Proof. destruct w; cbn; intro H; congruence. Qed.

Definition mvL (s : st) (w : Sym) (q' : Q) : st :=
  let x := match sL s with x :: _ => x | [] => S0 end in
  let L' := match sL s with _ :: L' => L' | [] => [] end in
  if is0 w && is11 (sM s) then mkst q' L' x [] (hhd (sHi s) :: sLo s) (tl (sHi s)) (sRt s) (sRr s) (scp s)
  else mkst q' L' x (w :: sM s) (sLo s) (sHi s) (sRt s) (sRr s) (scp s).

(* ---- re-splitting the right side at the end of a long separator run *)
Definition retarget (s : st) (own : bool) : st :=
  let cs := rsidec s in
  let (k, rest) := leadks (if own then S0 :: cs else cs) O in
  let (racc, rr) := toks rest [] in
  let cp := capr racc 0 in
  match (if own then match k with O => None | S k' => Some k' end else Some k), trits cp with
  | Some K, Some t =>
    let (lo, hi) := splitk K t [] in
    mkst (sq s) (sL s) (sh s) (if own then [S1;S1] else []) lo hi (rev_append racc []) rr cp
  | _, _ => s
  end.

(* ---- the macros at B1 (B reads 1) and A0 (A reads 0 next to a 0) *)
Definition macroB (s : st) (x : Sym) (L' : list Sym) : option st :=
  match sM s with
  | [] => option_map (fun H' => mkst A L' x [S1] (sLo s) H' (sRt s) (sRr s) (scp s)) (subh 1 (sHi s))
  | M =>
    if lead6 M then Some (retarget s false) else
    match addm (blank s) 1 M with
    | MInc M' => Some (mkst A L' x (S1 :: M') (sLo s) (sHi s) (sRt s) (sRr s) (scp s))
    | MExit M' c => option_map (fun H' => mkst A L' x (S1 :: M') (sLo s) H' (sRt s) (sRr s) (scp s)) (subh c (sHi s))
    | MOvf [] _ | MNo => None
    | MOvf ts rest =>
      Some (mkst A (pendr (rev_append ts []) 0%N ++ S0 :: sL s) (hd S0 rest) (tl rest) (sLo s) (sHi s) (sRt s) (sRr s) (scp s))
    end
  end.

Definition macroA (s : st) (y : Sym) (L' : list Sym) : option st :=
  if is11 (sM s) then
    match sHi s with
    | t :: H2 => option_map (fun H2' => mkst A L' y [S1] (t :: sLo s) H2' (sRt s) (sRr s) (scp s)) (subh 1 H2)
    | [] => None
    end
  else
    if lead6 (S0 :: sM s) then Some (retarget s true) else
    match addm (blank s) 1 (S0 :: sM s) with
    | MInc M' => Some (mkst A L' y (S1 :: M') (sLo s) (sHi s) (sRt s) (sRr s) (scp s))
    | MExit M' c => option_map (fun H' => mkst A L' y (S1 :: M') (sLo s) H' (sRt s) (sRr s) (scp s)) (subh c (sHi s))
    | MOvf [] _ | MNo => None
    | MOvf ts rest =>
      Some (mkst A (pendr (rev_append ts []) 0%N ++ sL s) (hd S0 rest) (tl rest) (sLo s) (sHi s) (sRt s) (sRr s) (scp s))
    end.

Definition macro (s : st) : option st :=
  match sq s, sh s, sL s with
  | B, S1, x :: L' => macroB s x L'
  | A, S0, S0 :: y :: L' => macroA s y L'
  | _, _, _ => None
  end.

Definition step (tm : TM) (s : st) : st + unit :=
  match macro s with
  | Some s' => inl s'
  | None =>
    match tm (sq s, sh s) with
    | None => inr tt
    | Some (w, R, q') => inl (mvR s w q')
    | Some (w, L, q') => inl (mvL s w q')
    end
  end.

(* ---- its soundness *)
(* ---- the representation, without the machine *)
Definition regv' (lo hi : list trit) (rt : list tok) (cp : N) : list tok :=
  match add (cp - cval lo hi) rt with Some u => u | None => [] end.

Lemma regv_eq s : regv s = regv' (sLo s) (sHi s) (sRt s) (scp s).
Proof. reflexivity. Qed.

Lemma rside_mk q L h M lo hi rt rr cp :
  rside (mkst q L h M lo hi rt rr cp) = M ++ ks (length lo) ++ tcells (regv' lo hi rt cp) ++ rr.
Proof. reflexivity. Qed.

Lemma WF_add' lo hi rt cp : (cval lo hi <= cp)%N -> cp = cap rt ->
  add (cp - cval lo hi) rt = Some (regv' lo hi rt cp).
Proof.
  intros H1 H2. unfold regv'. destruct (add_some (cp - cval lo hi) rt) as [u E]; [lia|]. rewrite E. reflexivity.
Qed.

(* the lazy region at level K takes c * 3^K more *)
Lemma lazy_add lo hi hi' rt cp c : (cval lo hi <= cp)%N -> cp = cap rt -> subh c hi = Some hi' ->
  (cval lo hi' <= cp)%N /\
  add (3 ^ N.of_nat (length lo) * c) (regv' lo hi rt cp) = Some (regv' lo hi' rt cp).
Proof.
  intros H1 H2 H3. apply subh_spec in H3.
  assert (E : (cval lo hi' + 3 ^ N.of_nat (length lo) * c = cval lo hi)%N)
    by (unfold cval; rewrite <- H3; ring).
  split; [lia|].
  rewrite (add_add _ _ _ _ (WF_add' lo hi rt cp H1 H2)).
  replace (cp - cval lo hi + 3 ^ N.of_nat (length lo) * c)%N with (cp - cval lo hi')%N by lia.
  apply WF_add'; [lia|exact H2].
Qed.

(* ... and at level K+1 (A0 on the run's first separator), the level-K trit moving down *)
Lemma lazy_add1 lo t h2 h2' rt cp : (cval lo (t :: h2) <= cp)%N -> cp = cap rt -> subh 1 h2 = Some h2' ->
  (cval (t :: lo) h2' <= cp)%N /\
  add (3 ^ N.of_nat (length (t :: lo))) (regv' lo (t :: h2) rt cp) = Some (regv' (t :: lo) h2' rt cp).
Proof.
  intros H1 H2 H3. apply subh_spec in H3.
  assert (E : (cval (t :: lo) h2' + 3 ^ N.of_nat (length (t :: lo)) = cval lo (t :: h2))%N).
  { unfold cval. cbn [vhi vlo length]. rewrite Nat2N.inj_succ, N.pow_succ_r', <- H3. ring. }
  split; [lia|].
  rewrite (add_add _ _ _ _ (WF_add' lo (t :: h2) rt cp H1 H2)).
  replace (cp - cval lo (t :: h2) + 3 ^ N.of_nat (length (t :: lo)))%N with (cp - cval (t :: lo) h2')%N by lia.
  apply WF_add'; [lia|exact H2].
Qed.

Lemma ks_seps k : ks k = tcells (repeat TS k).
Proof. apply ks_tcells. Qed.

Lemma lazy_cells K u : tcells (repeat TS K ++ u) = ks K ++ tcells u.
Proof. rewrite tcells_app, ks_seps. reflexivity. Qed.

(* re-splitting keeps the configuration *)
Lemma retarget_spec s own : WF s ->
  WF (retarget s own) /\ sq (retarget s own) = sq s /\ sL (retarget s own) = sL s /\
  sh (retarget s own) = sh s /\ rside (retarget s own) = rside s.
Proof.
  intro HW. unfold retarget. rewrite rsidec_spec.
  pose proof (leadks_spec (if own then S0 :: rside s else rside s) O) as LK.
  destruct (leadks (if own then S0 :: rside s else rside s) O) as [k rest] eqn:EK. cbn [fst snd ks app] in LK.
  pose proof (toks_spec (length rest) rest [] (le_n _)) as TK.
  destruct (toks rest []) as [racc rr] eqn:ET. cbn [fst snd rev tcells app] in TK.
  destruct (if own then match k with O => None | S k' => Some k' end else Some k) as [K|] eqn:EKK;
    [|split; [exact HW|repeat split]].
  destruct (trits (capr racc 0%N)) as [t|] eqn:Etr; [|split; [exact HW|repeat split]].
  pose proof (splitk_spec K t []) as SP. destruct (splitk K t []) as [lo hi] eqn:ES.
  cbn [fst snd length vlo] in SP. destruct SP as [SL SC].
  rewrite (trits_spec _ _ Etr), N.pow_0_r, N.mul_1_r, N.add_0_r in SC.
  rewrite <- rev_alt.
  assert (Hcap : capr racc 0%N = cap (rev racc)) by (rewrite capr_spec, capg_cap; reflexivity).
  assert (Hreg : regv' lo hi (rev racc) (capr racc 0%N) = rev racc).
  { unfold regv'. rewrite SC, N.sub_diag, add_0. reflexivity. }
  split; [unfold WF; cbn [sLo sHi scp sRt]; split; [lia|exact Hcap]|].
  cbn [sq sL sh]. repeat split.
  rewrite rside_mk, Hreg, SL, PeanoNat.Nat.add_0_r, <- TK.
  destruct own.
  - destruct k as [|k']; [discriminate|]. injection EKK as <-. cbn in LK. injection LK as LK.
    rewrite LK. reflexivity.
  - injection EKK as <-. rewrite LK. reflexivity.
Qed.

(* plain moves *)
Lemma mvR_spec s w q' : WF s ->
  WF (mvR s w q') /\ sq (mvR s w q') = q' /\ sL (mvR s w q') = w :: sL s /\
  sh (mvR s w q') = Streams.hd (rside s *> 0inf) /\ rside (mvR s w q') *> 0inf = Streams.tl (rside s *> 0inf).
Proof.
  intro HW. unfold mvR. destruct (sM s) as [|x M'] eqn:EM.
  - destruct (sLo s) as [|t Lo'] eqn:ELo.
    + assert (Hr : rside s = regc s) by (rewrite <- rsidec_spec; unfold rsidec; rewrite EM, ELo; reflexivity).
      rewrite Hr. destruct (regc s) as [|x cs] eqn:ER.
      * split; [split; reflexivity|]. repeat split; try (symmetry; apply const_unfold).
      * split; [split; reflexivity|]. repeat split;
          try (rewrite rside_mk; unfold regv'; cbn; rewrite ?app_nil_r; reflexivity).
    + assert (Hv : cval Lo' (hcons t (sHi s)) = cval (sLo s) (sHi s)) by (rewrite ELo, cval_unpack; reflexivity).
      destruct HW as [W1 W2]. split; [split; cbn [sLo sHi scp sRt]; [lia|exact W2]|]. repeat split;
        try (unfold rside; rewrite EM, ELo; reflexivity);
        try (rewrite rside_mk; unfold regv'; rewrite Hv; unfold rside, regv; rewrite EM, ELo; reflexivity).
  - destruct HW as [W1 W2]. split; [split; assumption|]. repeat split;
      try (unfold rside; rewrite EM; reflexivity);
      try (rewrite rside_mk; unfold rside; rewrite EM; reflexivity).
Qed.

Lemma mvL_spec s w q' : WF s ->
  WF (mvL s w q') /\ sq (mvL s w q') = q' /\ sL (mvL s w q') *> 0inf = Streams.tl (sL s *> 0inf) /\
  sh (mvL s w q') = Streams.hd (sL s *> 0inf) /\ rside (mvL s w q') = w :: rside s.
Proof.
  intro HW. destruct HW as [W1 W2].
  assert (HLx : (match sL s with _ :: L' => L' | [] => [] end) *> 0inf = Streams.tl (sL s *> 0inf) /\
                (match sL s with x :: _ => x | [] => S0 end) = Streams.hd (sL s *> 0inf))
    by (destruct (sL s); split; reflexivity).
  destruct HLx as [HL Hx].
  unfold mvL. destruct (is0 w) eqn:E0; [destruct (is11 (sM s)) eqn:E1|]; cbn [andb].
  - apply is0_spec in E0. apply is11_spec in E1. subst w.
    assert (Hv : cval (hhd (sHi s) :: sLo s) (tl (sHi s)) = cval (sLo s) (sHi s)) by apply cval_repack.
    split; [split; cbn [sLo sHi scp sRt]; lia|]. cbn [sq sL sh]. repeat split; try assumption;
      try (rewrite rside_mk; unfold regv'; rewrite Hv; unfold rside, regv; rewrite E1; reflexivity).
  - split; [split; assumption|]. cbn [sq sL sh]. repeat split; try assumption.
  - split; [split; assumption|]. cbn [sq sL sh]. repeat split; try assumption.
Qed.

Lemma blank_facts s : blank s = true -> sLo s = [] /\ sRt s = [] /\ sRr s = [].
Proof. unfold blank. destruct (sLo s), (sRt s), (sRr s); cbn; intro H; try discriminate; auto. Qed.

Lemma rside_blank s : WF s -> blank s = true -> rside s = sM s.
Proof. apply blank_spec. Qed.

Lemma pendr_rev_append ts : pendr (rev_append ts []) 0%N = rev (pend ts).
Proof. rewrite <- rev_alt. apply pendr_spec. Qed.

Lemma cap0_of_none ts : add 1 ts = None -> cap ts = 0%N.
Proof. intro H. apply add_none in H. lia. Qed.

Local Open Scope sym_scope.
Section Sound.
Variable tm : TM.
Local Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Local Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Hypothesis incA : forall ts u l r, add 1 ts = Some u ->
  (l << 0) {{A}}> tcells ts *> r -->+ l <{{A}} 1 >> tcells u *> r.
Hypothesis ovfA : forall ts l r, cap ts = 0%N ->
  (l << 0) {{A}}> tcells ts *> 0 >> r -->* (l << 0) <* rev (pend ts) {{A}}> 0 >> r.
Hypothesis incB : forall ts u l r, add 1 ts = Some u ->
  l {{B}}> 1 >> tcells ts *> r -->+ l <{{A}} 1 >> tcells u *> r.
Hypothesis ovfB : forall ts l r, cap ts = 0%N ->
  l {{B}}> 1 >> tcells ts *> 0 >> r -->+ (l << 0) <* rev (pend ts) {{A}}> 0 >> r.

Lemma use_incB s s' ts u rr : sq s = B -> sh s = S1 -> rside s *> 0inf = (tcells ts ++ rr) *> 0inf ->
  add 1 ts = Some u -> sq s' = A -> sL s' *> 0inf = Streams.tl (sL s *> 0inf) -> sh s' = Streams.hd (sL s *> 0inf) ->
  rside s' *> 0inf = (S1 :: tcells u ++ rr) *> 0inf -> conf s -->* conf s'.
Proof.
  intros H1 H2 H3 H4 H5 H6 H7 H8. unfold conf. rewrite H1, H2, H3, H5, H6, H7, H8.
  cbn [Str_app]. rewrite !Str_app_assoc. apply progress_evstep. apply incB. exact H4.
Qed.

Lemma use_ovfB s s' ts rr : sq s = B -> sh s = S1 -> rside s *> 0inf = (tcells ts ++ S0 :: rr) *> 0inf ->
  cap ts = 0%N -> sq s' = A -> sL s' = rev (pend ts) ++ S0 :: sL s -> sh s' = S0 ->
  rside s' *> 0inf = rr *> 0inf -> conf s -->* conf s'.
Proof.
  intros H1 H2 H3 H4 H5 H6 H7 H8. unfold conf. rewrite H1, H2, H3, H5, H6, H7, H8.
  rewrite !Str_app_assoc. cbn [Str_app]. apply progress_evstep. apply ovfB. exact H4.
Qed.

Lemma use_incA s s' ts u y L' rr : sq s = A -> sL s = S0 :: y :: L' ->
  (sh s :: rside s) *> 0inf = (tcells ts ++ rr) *> 0inf -> add 1 ts = Some u ->
  sq s' = A -> sL s' = L' -> sh s' = y ->
  rside s' *> 0inf = (S1 :: tcells u ++ rr) *> 0inf -> conf s -->* conf s'.
Proof.
  intros H1 H2 H3 H4 H5 H6 H7 H8. unfold conf. rewrite H1, H2, H5, H6, H7, H8.
  replace (sh s) with (Streams.hd ((tcells ts ++ rr) *> 0inf)) by (rewrite <- H3; reflexivity).
  replace (rside s *> 0inf) with (Streams.tl ((tcells ts ++ rr) *> 0inf)) by (rewrite <- H3; reflexivity).
  cbn [Str_app]. rewrite !Str_app_assoc. apply progress_evstep. exact (incA ts u ((y :: L') *> 0inf) _ H4).
Qed.

Lemma use_ovfA s s' ts rr : sq s = A -> (exists L0, sL s = S0 :: L0) ->
  (sh s :: rside s) *> 0inf = (tcells ts ++ S0 :: rr) *> 0inf -> cap ts = 0%N ->
  sq s' = A -> sL s' = rev (pend ts) ++ sL s -> sh s' = S0 ->
  rside s' *> 0inf = rr *> 0inf -> conf s -->* conf s'.
Proof.
  intros H1 [L0 H2] H3 H4 H5 H6 H7 H8. unfold conf. rewrite H1, H5, H6, H7, H8.
  replace (sh s) with (Streams.hd ((tcells ts ++ S0 :: rr) *> 0inf)) by (rewrite <- H3; reflexivity).
  replace (rside s *> 0inf) with (Streams.tl ((tcells ts ++ S0 :: rr) *> 0inf)) by (rewrite <- H3; reflexivity).
  rewrite H2, !Str_app_assoc. cbn [Str_app]. exact (ovfA ts (L0 *> 0inf) _ H4).
Qed.

Lemma conf_same s s' : sq s' = sq s -> sL s' = sL s -> sh s' = sh s -> rside s' = rside s -> conf s -->* conf s'.
Proof. intros H1 H2 H3 H4. unfold conf. rewrite H1, H2, H3, H4. apply evstep_refl. Qed.

Lemma retarget_ok s own : WF s -> WF (retarget s own) /\ conf s -->* conf (retarget s own).
Proof.
  intro HW. destruct (retarget_spec s own HW) as (W & E1 & E2 & E3 & E4).
  split; [exact W|]. apply conf_same; assumption.
Qed.

Ltac leq := f_equal; cbn [app]; rewrite <- ?app_assoc; reflexivity.

Lemma macroB_spec s x L' s' : WF s -> sq s = B -> sh s = S1 -> sL s = x :: L' ->
  macroB s x L' = Some s' -> WF s' /\ conf s -->* conf s'.
Proof.
  intros HW Eq Eh EL H. pose proof HW as [W1 W2]. unfold macroB in H.
  assert (Etl : L' *> 0inf = Streams.tl (sL s *> 0inf)) by (rewrite EL; reflexivity).
  assert (Ehd : x = Streams.hd (sL s *> 0inf)) by (rewrite EL; reflexivity).
  destruct (sM s) as [|a M0] eqn:EM.
  - (* lazy: the region is the run *)
    destruct (subh 1 (sHi s)) as [H'|] eqn:ES; [|discriminate]. cbn in H. injection H as <-.
    destruct (lazy_add _ _ _ _ _ _ W1 W2 ES) as [Wc Hadd]. rewrite N.mul_1_r in Hadd.
    split; [split; assumption|].
    eapply (use_incB s _ (repeat TS (length (sLo s)) ++ regv s)
                         (repeat TS (length (sLo s)) ++ regv' (sLo s) H' (sRt s) (scp s)) (sRr s));
      [exact Eq | exact Eh
      | unfold rside; rewrite EM, lazy_cells; leq
      | rewrite add_seps, N.mul_1_r, regv_eq, Hadd; reflexivity
      | reflexivity | exact Etl | exact Ehd
      | rewrite rside_mk, lazy_cells; leq].
  - destruct (lead6 (a :: M0)) eqn:L6.
    { injection H as <-. apply retarget_ok. exact HW. }
    pose proof (addm_spec (blank s) (length (a :: M0)) (a :: M0) 1 (le_n _)) as AS.
    destruct (addm (blank s) 1 (a :: M0)) as [M'|M' c|ts rest|] eqn:EA.
    + (* absorbed inside M *)
      injection H as <-. destruct AS as (ts & u & rest & HM & -> & Hadd).
      split; [split; assumption|].
      eapply (use_incB s _ ts u (rest ++ ks (length (sLo s)) ++ tcells (regv s) ++ sRr s));
        [exact Eq | exact Eh
        | unfold rside; rewrite EM, HM; leq
        | exact Hadd | reflexivity | exact Etl | exact Ehd
        | rewrite rside_mk, <- regv_eq; leq].
    + (* the carry leaves M into the run *)
      destruct (subh c (sHi s)) as [H'|] eqn:ES; [|discriminate]. cbn in H. injection H as <-.
      destruct AS as (Hbl & ts & u & HM & -> & Hc).
      destruct (lazy_add _ _ _ _ _ _ W1 W2 ES) as [Wc Hadd].
      split; [split; assumption|].
      eapply (use_incB s _ (ts ++ repeat TS (length (sLo s)) ++ regv s)
                           (u ++ repeat TS (length (sLo s)) ++ regv' (sLo s) H' (sRt s) (scp s)) (sRr s));
        [exact Eq | exact Eh
        | unfold rside; rewrite EM, HM, !tcells_app, <- ks_seps; leq
        | rewrite Hc, add_seps, regv_eq, Hadd; reflexivity
        | reflexivity | exact Etl | exact Ehd
        | rewrite rside_mk, !tcells_app, <- ks_seps; leq].
    + (* overflow: the head jumps to the region's end *)
      destruct ts as [|t ts']; [discriminate|]. injection H as <-.
      destruct AS as (HM & Hn & Hr). apply cap0_of_none in Hn.
      split; [split; assumption|].
      destruct Hr as [[Hbl ->]|[rest' ->]].
      * destruct (blank_facts s Hbl) as (B1 & B2 & B3).
        eapply (use_ovfB s _ (t :: ts') []);
          [exact Eq | exact Eh
          | rewrite (rside_blank s HW Hbl), EM, HM, app_nil_r, Str_app_assoc; f_equal; apply const_unfold
          | exact Hn | reflexivity
          | cbn [sL]; change (rev_append ts' [t]) with (rev_append (t :: ts') []); rewrite pendr_rev_append; reflexivity
          | reflexivity
          | rewrite rside_mk, B1, B2, B3; unfold regv'; rewrite W2, B2; reflexivity].
      * eapply (use_ovfB s _ (t :: ts') (rest' ++ ks (length (sLo s)) ++ tcells (regv s) ++ sRr s));
          [exact Eq | exact Eh
          | unfold rside; rewrite EM, HM; leq
          | exact Hn | reflexivity
          | cbn [sL]; change (rev_append ts' [t]) with (rev_append (t :: ts') []); rewrite pendr_rev_append; reflexivity
          | reflexivity
          | rewrite rside_mk; reflexivity].
    + discriminate.
Qed.

Lemma macroA_spec s y L' s' : WF s -> sq s = A -> sh s = S0 -> sL s = S0 :: y :: L' ->
  macroA s y L' = Some s' -> WF s' /\ conf s -->* conf s'.
Proof.
  intros HW Eq Eh EL H. pose proof HW as [W1 W2]. unfold macroA in H.
  destruct (is11 (sM s)) eqn:E11.
  - (* lazy at level K+1: the head is on the run's first separator *)
    apply is11_spec in E11.
    destruct (sHi s) as [|t H2] eqn:EH; [discriminate|].
    destruct (subh 1 H2) as [H2'|] eqn:ES; [|discriminate]. cbn in H. injection H as <-.
    pose proof W1 as W1'.
    destruct (lazy_add1 _ _ _ _ _ _ W1' W2 ES) as [Wc Hadd]. cbn [length] in Hadd.
    split; [split; assumption|].
    eapply (use_incA s _ (repeat TS (S (length (sLo s))) ++ regv s)
                         (repeat TS (S (length (sLo s))) ++ regv' (t :: sLo s) H2' (sRt s) (scp s)) y L' (sRr s));
      [exact Eq | exact EL
      | rewrite Eh; unfold rside; rewrite E11, lazy_cells; leq
      | rewrite add_seps, N.mul_1_r, regv_eq, EH, Hadd; reflexivity
      | reflexivity | reflexivity | reflexivity
      | rewrite rside_mk, lazy_cells; leq].
  - destruct (lead6 (S0 :: sM s)) eqn:L6.
    { injection H as <-. apply retarget_ok. exact HW. }
    pose proof (addm_spec (blank s) (length (S0 :: sM s)) (S0 :: sM s) 1 (le_n _)) as AS.
    destruct (addm (blank s) 1 (S0 :: sM s)) as [M'|M' c|ts rest|] eqn:EA.
    + injection H as <-. destruct AS as (ts & u & rest & HM & -> & Hadd).
      assert (HM' : @cons Sym S0 (sM s) = tcells ts ++ rest) by exact HM.
      split; [split; assumption|].
      eapply (use_incA s _ ts u y L' (rest ++ ks (length (sLo s)) ++ tcells (regv s) ++ sRr s));
        [exact Eq | exact EL
        | rewrite Eh; unfold rside; rewrite app_comm_cons, HM'; leq
        | exact Hadd | reflexivity | reflexivity | reflexivity
        | rewrite rside_mk, <- regv_eq; leq].
    + destruct (subh c (sHi s)) as [H'|] eqn:ES; [|discriminate]. cbn in H. injection H as <-.
      destruct AS as (Hbl & ts & u & HM & -> & Hc).
      assert (HM' : @cons Sym S0 (sM s) = tcells ts) by exact HM.
      destruct (lazy_add _ _ _ _ _ _ W1 W2 ES) as [Wc Hadd].
      split; [split; assumption|].
      eapply (use_incA s _ (ts ++ repeat TS (length (sLo s)) ++ regv s)
                           (u ++ repeat TS (length (sLo s)) ++ regv' (sLo s) H' (sRt s) (scp s)) y L' (sRr s));
        [exact Eq | exact EL
        | rewrite Eh; unfold rside; rewrite app_comm_cons, HM', !tcells_app, <- ks_seps; leq
        | rewrite Hc, add_seps, regv_eq, Hadd; reflexivity
        | reflexivity | reflexivity | reflexivity
        | rewrite rside_mk, !tcells_app, <- ks_seps; leq].
    + destruct ts as [|t ts']; [discriminate|]. injection H as <-.
      destruct AS as (HM & Hn & Hr). apply cap0_of_none in Hn.
      assert (HM' : @cons Sym S0 (sM s) = tcells (t :: ts') ++ rest) by exact HM.
      split; [split; assumption|].
      destruct Hr as [[Hbl ->]|[rest' ->]].
      * destruct (blank_facts s Hbl) as (B1 & B2 & B3).
        eapply (use_ovfA s _ (t :: ts') []);
          [exact Eq | exists (y :: L'); exact EL
          | rewrite Eh, (rside_blank s HW Hbl), HM', app_nil_r, Str_app_assoc; f_equal; apply const_unfold
          | exact Hn | reflexivity
          | cbn [sL]; change (rev_append ts' [t]) with (rev_append (t :: ts') []); rewrite pendr_rev_append;
            reflexivity
          | reflexivity
          | rewrite rside_mk, B1, B2, B3; unfold regv'; rewrite W2, B2; reflexivity].
      * eapply (use_ovfA s _ (t :: ts') (rest' ++ ks (length (sLo s)) ++ tcells (regv s) ++ sRr s));
          [exact Eq | exists (y :: L'); exact EL
          | rewrite Eh; unfold rside; rewrite app_comm_cons, HM'; leq
          | exact Hn | reflexivity
          | cbn [sL]; change (rev_append ts' [t]) with (rev_append (t :: ts') []); rewrite pendr_rev_append;
            reflexivity
          | reflexivity
          | rewrite rside_mk; reflexivity].
    + discriminate.
Qed.

Lemma macro_spec s s' : WF s -> macro s = Some s' -> WF s' /\ conf s -->* conf s'.
Proof.
  intros HW H. unfold macro in H.
  destruct (sq s) eqn:Eq; destruct (sh s) eqn:Eh; destruct (sL s) as [|x [|y L']] eqn:EL;
    first [ discriminate H
          | exact (macroB_spec s _ _ s' HW Eq Eh EL H)
          | destruct x; first [ exact (macroA_spec s _ _ s' HW Eq Eh EL H) | discriminate H ] ].
Qed.

Lemma step_spec s : WF s ->
  match step tm s with inl s' => WF s' /\ conf s -->* conf s' | inr _ => halted tm (conf s) end.
Proof.
  intro HW. unfold step. destruct (macro s) as [s'|] eqn:EM; [exact (macro_spec s s' HW EM)|].
  destruct (tm (sq s, sh s)) as [[[w d] q']|] eqn:ET; [destruct d|].
  - destruct (mvL_spec s w q' HW) as (W & E1 & E2 & E3 & E4). split; [exact W|].
    eapply evstep_step; [unfold conf; exact (step_left ET)|].
    apply evstep_refl'. unfold conf. rewrite E1, E2, E3, E4. reflexivity.
  - destruct (mvR_spec s w q' HW) as (W & E1 & E2 & E3 & E4). split; [exact W|].
    eapply evstep_step; [unfold conf; exact (step_right ET)|].
    apply evstep_refl'. unfold conf. rewrite E1, E2, E3, E4. reflexivity.
  - unfold halted, conf. exact ET.
Qed.

Theorem check_halts s0 T : WF s0 -> N_iter_until (step tm) (inl s0) T = inr tt -> halts tm (conf s0).
Proof.
  intros HW H.
  pose proof (N_iter_until_spec (f := step tm) (x := inl s0) (T := T)
    (fun s => WF s /\ conf s0 -->* conf s) (fun _ => halts tm (conf s0))) as NI.
  rewrite H in NI. apply NI.
  - intros s [HWs Hr]. pose proof (step_spec s HWs) as SS. destruct (step tm s) as [s'|[]].
    + destruct SS as [HW' Hs]. split; [exact HW'|]. eapply evstep_trans; eassumption.
    + eapply halts_evstep; [|exact Hr]. apply halted_halts. exact SS.
  - split; [exact HW|apply evstep_refl].
Qed.

End Sound.

Definition s0 (q : Q) : st := mkst q [] S0 [] [] [] [] [] 0%N.
Lemma WF0 q : WF (s0 q).
Proof. split; cbn; lia. Qed.

Theorem halts_of_run tm s0 T : Facts tm -> WF s0 -> N_iter_until (step tm) (inl s0) T = inr tt ->
  halts tm (conf s0).
Proof.
  intro HF.
  apply (check_halts tm (fun ts u l r H => inc_A0 tm HF (List.length ts) ts u l r (le_n _) H)
    (fun ts l r H => ovf_A0 tm HF (List.length ts) ts l r (le_n _) H) (inc_B1 tm HF) (ovf_B1 tm HF)).
Qed.

(* ---- the four machines *)
(* String only now: it shadows [length] *)
From Coq Require Import String.
Local Open Scope sym_scope.

Module TM1. (* #229 *)
Definition tm := Eval compute in (TM_from_str "1RB0LE_1LC0RE_0RA0LD_1LA0LF_0LC0RE_0LB---").
Lemma facts : Facts tm.
Proof. repeat split; intros; execute. Qed.
Lemma run : N_iter_until (step tm) (inl (s0 A)) (2 ^ 32)%N = inr tt.
Proof. native_check_eq. Time Qed.
Theorem halt : halts tm c0.
Proof. exact (halts_of_run tm _ _ facts (WF0 A) run). Qed.
End TM1.

Module TM2. (* #412 *)
Definition tm := Eval compute in (TM_from_str "1RB0LE_1LC0RE_0RA0LD_1LA1LF_0LC0RA_1LB---").
Lemma facts : Facts tm.
Proof. repeat split; intros; execute. Qed.
Lemma run : N_iter_until (step tm) (inl (s0 A)) (2 ^ 32)%N = inr tt.
Proof. native_check_eq. Time Qed.
Theorem halt : halts tm c0.
Proof. exact (halts_of_run tm _ _ facts (WF0 A) run). Qed.
End TM2.

Module TM3. (* #636: TM2's table mirrored, started in TM2's state F *)
Definition tm := Eval compute in (TM_from_str "1RB---_1RC0LE_0LD0RF_1LB0RE_0RC0LD_1RD1RA").
Lemma run : N_iter_until (step TM2.tm) (inl (s0 F)) (2 ^ 28)%N = inr tt.
Proof. native_check_eq. Time Qed.
Definition ren (q : Q) : Q := match q with A => D | B => B | C => C | D => F | E => E | F => A end.
Lemma ren_perm : Perm (flip TM2.tm) tm ren.
Proof.
  split.
  - intros [] [] H; unfold flip in H; cbn in H; try discriminate; reflexivity.
  - intros [] [] s' d q' H; unfold flip in H; cbn in H; inversion H; reflexivity.
Qed.
Theorem halt : halts tm c0.
Proof.
  exact (perm_halts _ _ ren F tape0 ren_perm
    (flip_halts TM2.tm (F;; tape0) (halts_of_run TM2.tm _ _ TM2.facts (WF0 F) run))).
Qed.
End TM3.

Module TM4. (* #145, run as [tmc]: the same table with its states renamed so that [Facts] holds *)
Definition tm := Eval compute in (TM_from_str "1RB0LF_0LC---_0LA0RD_1RE0LC_1LA0RC_1LD0LB").
Definition tmc :=
  Eval compute in (TM_from_str "1RB0LE_1LC0RE_1RF0LD_1LA0LF_0LC0RA_0LE---").
Lemma facts : Facts tmc.
Proof. repeat split; intros; execute. Qed.
Lemma run : N_iter_until (step tmc) (inl (s0 C)) (2 ^ 32)%N = inr tt.
Proof. native_check_eq. Time Qed.
Definition ren (q : Q) : Q := match q with A => D | B => E | C => A | D => F | E => C | F => B end.
Lemma ren_perm : Perm tmc tm ren.
Proof.
  split.
  - intros [] [] H; cbn in H; try discriminate; reflexivity.
  - intros [] [] s' d q' H; cbn in H; inversion H; reflexivity.
Qed.
Theorem halt : halts tm c0.
Proof. exact (perm_halts _ _ ren C tape0 ren_perm (halts_of_run tmc _ _ facts (WF0 C) run)). Qed.
End TM4.

Print Assumptions TM1.halt.
Print Assumptions TM2.halt.
Print Assumptions TM3.halt.
Print Assumptions TM4.halt.
