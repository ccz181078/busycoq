(* 1RB0LF_0RC---_1RD0RA_1LE0RC_0LA0LE_1LE1LB never halts.

   Spread-digit binary bouncer counter.  A left bouncer lead a feeds a right binary counter whose
   digits b 100 01 (100)^g sit at unary gaps g; at the right end of the counter a block of gap-1
   digits (the R block) is followed by a finite "tail".  At each overflow the carry runs into the
   tail, which answers either S (the counter wraps silently) or N (the left part freezes into a
   wall that a long pause eats two increments at a time, rebuilding every gap and inserting new
   digits).  See the accompanying write-up (1RB0LF_0RC---_1RD0RA_1LE0RC_0LA0LE_1LE1LB_writeup.md) for the full mechanism.

   Adapted from verify/CounterClass3v2.v, Module TM1 (a hand-written multi-level counter: sweep
   lemmas, a carry lemma by induction on the carry depth, macro lemmas, then nonhalt by an
   invariant).

   Structure of this file.
   - Token view (write-up section 0): right of the lead the tape is a word over T0 = 00, T1 = 01,
     TZ = 100; processed tokens are P = (10), PZ = (010).  ctr gs v is the counter, LSB first.
   - Window lemmas by es; Csweep, IncC, IncL (one increment), Inc1/Incs (normal mode), and the
     pause rules as three generic wall lemmas TwoInc (P100, P010, WX, ZXP1), ZXg (ZX, ZXN),
     ZXP2g.
   - The overflow return is the finite token transducer retf (retf_spec), so the write-up's
     16,384-entry tail table is not needed: TailRet + Tail10, Tail0z, Tail11 (one leaf per
     position of the first 0 of the tail, plus the end-unit carry Tail11_end) give the tail's
     answer for every tail in L* (Lst) and the TAILFRONT closure.
   - OvN1, OvN0, OvS1: sweep, tail, R-block return (RB_* lemmas), boundary.  NOrb, POrb,
     SILENT, SILENTP add the wall bookkeeping and the zone rebuild (Zones).
   - pathS, pathP1, pathP1S, pathP3: the four paths between normal-mode overflows; INV is the
     interval invariant of write-up section 5.3 (M = 4 * 2 ^ (length G + r1)); step shows INV is
     closed; init is the 92,299-step initial segment; nonhalt by progress_nonhalt_cond.

   Formalized with Claude Code (AI-assisted).
   Checked: compiles against unmodified busycoq BB6 (commit 0940bb9) with Coq 8.20.1;
   Print Assumptions nonhalt: Closed under the global context. *)

From BusyCoq Require Import Individual62.
Require Import Lia.
Require Import String.
Require Import List.
Require Import Arith.

Definition tm := Eval compute in (TM_from_str "1RB0LF_0RC---_1RD0RA_1LE0RC_0LA0LE_1LE1LB").

Notation "c --> c'" := (c -[ tm ]-> c')   (at level 40).
Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Open Scope list.

(** ** Tokens *)
Inductive tok := T0 | T1 | TZ.
Definition tokw (t : tok) : list Sym :=
  match t with T0 => [0;0] | T1 => [0;1] | TZ => [1;0;0] end.
Fixpoint tw (ts : list tok) : list Sym :=
  match ts with [] => [] | t :: ts => tokw t ++ tw ts end.

Inductive ptok := P | PZ.
Definition pw (p : ptok) : list Sym := match p with P => [0;1] | PZ => [0;1;0] end.
Fixpoint pl (ps : list ptok) : list Sym :=
  match ps with [] => [] | p :: ps => pw p ++ pl ps end.
Definition proc (t : tok) : ptok := match t with TZ => PZ | _ => P end.

Lemma tw_app xs ys : tw (xs ++ ys) = tw xs ++ tw ys.
Proof. induction xs; cbn; [reflexivity|]. rewrite IHxs, app_assoc. reflexivity. Qed.
Lemma tw_cons x xs : tw (x :: xs) = tokw x ++ tw xs.
Proof. reflexivity. Qed.
Lemma pl_app xs ys : pl (xs ++ ys) = pl xs ++ pl ys.
Proof. induction xs; cbn; [reflexivity|]. rewrite IHxs, app_assoc. reflexivity. Qed.

(** ** Window lemmas *)
Lemma AT0 l r : l {{A}}> [0;0] *> r -->* l <* [0;1] {{C}}> r.  Proof. es. Qed.
Lemma CT1 l r : l {{C}}> [0;1] *> r -->* l <* [0;1] {{C}}> r.  Proof. es. Qed.
Lemma CTZ l r : l {{C}}> [1;0;0] *> r -->* l <* [0;1;0] {{C}}> r.  Proof. es. Qed.
Lemma CT0 l r : l {{C}}> [0;0] *> r -->* l <{{E}} [0;1] *> r.  Proof. es. Qed.
Lemma EPZ l r : l <* [0;1;0] <{{E}} r -->* l <{{E}} [1;0;0] *> r.  Proof. es. Qed.
Lemma EP l r : l <* [0;1] <{{E}} r -->* l <{{F}} [0;0] *> r.  Proof. es. Qed.
Lemma FP l r : l <* [0;1] <{{F}} r -->* l <{{E}} [0;1] *> r.  Proof. es. Qed.
Lemma FPZP l r : l <* [0;1] <* [0;1;0] <{{F}} [0;0] *> r -->*
  l <{{E}} [0;0] *> [1;0;0] *> [0;1] *> r.  Proof. es. Qed.
Lemma ENDl l r : l <* [0;0] <{{F}} r -->* l <{{A}} [0;1] *> r.  Proof. es. Qed.
Lemma B1 l r : l <* [1;0] <{{F}} r -->* l <* [0;0] {{A}}> r.  Proof. es. Qed.
Lemma BN l r : l <* [0;1;0;0;1;0] <{{F}} [0;0] *> r -->* l <{{A}} [0;0;0;1;0;0;0;1] *> r.  Proof. es. Qed.
Lemma ENDZX l r : l <* [0;0;1;0;0;1;0;1;0;0;1;0] <{{F}} r -->* l <{{A}} [0;0;0;1;0;0;0;1;1;0;0;1] *> r.  Proof. es. Qed.

(** ** C sweep over T1/TZ tokens *)
Fixpoint noT0 (ts : list tok) : Prop :=
  match ts with [] => True | T0 :: _ => False | _ :: ts => noT0 ts end.
Definition prc (ts : list tok) : list ptok := rev (map proc ts).

Lemma Csweep ts : noT0 ts -> forall l r,
  l {{C}}> tw ts *> r -->* l <* pl (prc ts) {{C}}> r.
Proof.
  induction ts as [|t ts IH]; intros H l r; [finish|].
  unfold prc. cbn [map rev]. rewrite pl_app. cbn [tw].
  rewrite Str_app_assoc.
  destruct t; cbn in H; [contradiction| |].
  - follow CT1. follow (IH H). cbn [pl proc]. rewrite Str_app_assoc. finish.
  - follow CTZ. follow (IH H). cbn [pl proc]. rewrite Str_app_assoc. finish.
Qed.

(** ** The leftward return over processed tokens *)
Fixpoint retf (m : Q) (ps : list ptok) (rs : list tok) {struct ps} : Q * list ptok * list tok :=
  match m, ps with
  | E, PZ :: ps' => retf E ps' (TZ :: rs)
  | E, P :: ps' => retf F ps' (T0 :: rs)
  | F, P :: ps' => retf E ps' (T1 :: rs)
  | F, PZ :: P :: ps' =>
      match rs with
      | T0 :: rs' => retf E ps' (T0 :: TZ :: T1 :: rs')
      | _ => (m, ps, rs)
      end
  | _, _ => (m, ps, rs)
  end.

Lemma retf_spec_n n : forall ps, length ps <= n -> forall m rs m' ps' rs',
  retf m ps rs = (m', ps', rs') -> forall l r,
  l <* pl ps <{{m}} tw rs *> r -->* l <* pl ps' <{{m'}} tw rs' *> r.
Proof.
  induction n as [|n IH]; intros ps Hn m rs m' ps' rs' Hr l r.
  - destruct ps; [|cbn in Hn; lia].
    destruct m; cbn in Hr; inversion Hr; subst; finish.
  - destruct ps as [|p ps].
    { destruct m; cbn in Hr; inversion Hr; subst; finish. }
    cbn in Hn.
    destruct m, p; cbn in Hr; try (inversion Hr; subst; solve [finish]).
    + (* E, P *)
      cbn [pl]. rewrite Str_app_assoc. cbn [pw].
      follow EP. apply (IH ps ltac:(lia) _ _ _ _ _ Hr).
    + (* E, PZ *)
      cbn [pl]. rewrite Str_app_assoc. cbn [pw].
      follow EPZ. apply (IH ps ltac:(lia) _ _ _ _ _ Hr).
    + (* F, P *)
      cbn [pl]. rewrite Str_app_assoc. cbn [pw].
      follow FP. apply (IH ps ltac:(lia) _ _ _ _ _ Hr).
    + (* F, PZ *)
      destruct ps as [|[|] ps]; try (inversion Hr; subst; solve [finish]).
      destruct rs as [|[| |] rs]; try (inversion Hr; subst; solve [finish]).
      cbn [pl tw]. rewrite !Str_app_assoc. cbn [pw tokw].
      cbn in Hn.
      follow FPZP.
      assert (H := IH ps ltac:(lia) _ _ _ _ _ Hr l r).
      cbn [tw] in H. rewrite !Str_app_assoc in H. exact H.
Qed.

Lemma retf_spec ps m rs m' ps' rs' :
  retf m ps rs = (m', ps', rs') -> forall l r,
  l <* pl ps <{{m}} tw rs *> r -->* l <* pl ps' <{{m'}} tw rs' *> r.
Proof. intros. eapply retf_spec_n; [apply le_n|eassumption]. Qed.

(** ** Shift rules *)
Lemma CTZ' l r : l <* [] {{C}}> [1;0;0] *> r -->* l <* [0;1;0] <* [] {{C}}> r.  Proof. es. Qed.
Definition CTZs := shift_rule_R _ _ _ _ _ CTZ'.
Lemma EPZ' l r : l <* [0;1;0] <{{E}} [] *> r -->* l <{{E}} [] *> [1;0;0] *> r.  Proof. es. Qed.
Definition EPZs := shift_rule_L _ _ _ _ _ EPZ'.

Lemma tw_Z g : tw (repeat TZ g) = [1;0;0]^^g.
Proof. induction g; cbn; [reflexivity|]. rewrite IHg. reflexivity. Qed.

(** ** The counter: digits b Z 1 Z^g, LSB first; the last digit is its bit only *)
Definition bit (v : nat) : tok := if Nat.odd v then T1 else T0.
Fixpoint ctr (gs : list nat) (v : nat) : list tok :=
  match gs with
  | [] => [bit v]
  | g :: gs' => bit v :: TZ :: T1 :: repeat TZ g ++ ctr gs' (Nat.div2 v)
  end.

Lemma bit_even w : bit (2*w) = T0.
Proof. unfold bit. rewrite Nat.odd_even. reflexivity. Qed.
Lemma bit_odd w : bit (S (2*w)) = T1.
Proof. unfold bit. replace (S (2*w)) with (2*w+1) by lia. rewrite Nat.odd_odd. reflexivity. Qed.

Lemma ctr_even g gs w : ctr (g :: gs) (2*w) = T0 :: TZ :: T1 :: repeat TZ g ++ ctr gs w.
Proof. cbn [ctr]. rewrite bit_even, Nat.div2_double. reflexivity. Qed.
Lemma ctr_odd g gs w : ctr (g :: gs) (S (2*w)) = T1 :: TZ :: T1 :: repeat TZ g ++ ctr gs w.
Proof. cbn [ctr]. rewrite bit_odd, Nat.div2_succ_double. reflexivity. Qed.

Lemma ctr_hd_even gs w : exists rest, ctr gs (2*w) = T0 :: rest /\ ctr gs (S (2*w)) = T1 :: rest.
Proof.
  destruct gs as [|g gs].
  - exists (@nil tok). cbn [ctr]. rewrite bit_even, bit_odd. auto.
  - eexists. rewrite ctr_even, ctr_odd. split; reflexivity.
Qed.

Lemma pow2S n : 2 ^ S n = 2 * 2 ^ n.
Proof. apply Nat.pow_succ_r'. Qed.

Lemma IncC gs : forall v, S v < 2 ^ S (length gs) -> forall l r t,
  l {{C}}> tw (ctr gs v ++ t) *> r -->* l <{{E}} tw (ctr gs (S v) ++ t) *> r.
Proof.
  induction gs as [|g gs IH]; intros v Hv l r t;
  destruct (Nat.Even_or_Odd v) as [[w ->]|[w ->]].
  - cbn [ctr app tw]. rewrite bit_even. replace (S (2*w)) with (2*w+1) by lia.
    unfold bit. rewrite Nat.odd_odd. cbn [tokw]. rewrite !Str_app_assoc. apply CT0.
  - cbn [length] in Hv. rewrite pow2S in Hv. cbn in Hv. lia.
  - destruct (ctr_hd_even (g :: gs) w) as (rest & E0 & E1).
    rewrite E0, E1. cbn [app tw]. rewrite !Str_app_assoc. apply CT0.
  - replace (2*w+1) with (S (2*w)) by lia. rewrite ctr_odd.
    replace (S (S (2*w))) with (2 * S w) by lia. rewrite ctr_even.
    cbn [length] in Hv. rewrite !pow2S in Hv.
    cbn [app]. rewrite <- !app_assoc. cbn [tw].
    rewrite !(tw_app (repeat TZ g)), tw_Z, !Str_app_assoc. cbn [tokw].
    follow CT1. follow CTZ. follow CT1.
    follow CTZs.
    follow (IH w ltac:(rewrite pow2S; lia)).
    follow EPZs. follow EP. follow FPZP. finish.
Qed.

Lemma IncL gs v a : S v < 2 ^ S (length gs) -> forall l r t,
  l {{A}}> tw (T0 :: repeat TZ a ++ ctr gs v ++ t) *> r -->*
  l <{{F}} tw (T0 :: repeat TZ a ++ ctr gs (S v) ++ t) *> r.
Proof.
  intros Hv l r t.
  cbn [tw]. rewrite !(tw_app (repeat TZ a)), tw_Z, !Str_app_assoc. cbn [tokw].
  follow AT0. follow CTZs.
  follow (IncC gs v Hv).
  follow EPZs. follow EP. finish.
Qed.

(** ** The left bounce: F at the edge adds one 100 to the lead and returns to A *)
Lemma Bnc X : (const 0) <{{F}} [0;0] *> [1;0;0] *> X -->*
  (const 0) {{A}}> [0;0] *> [1;0;0] *> [1;0;0] *> X.
Proof. rewrite (const_unfold _ 0) at 1. es. Qed.

(** ** Normal-mode increment: one bounce, lead a -> a+1, counter v -> v+1 *)
Lemma Inc gs v a : S v < 2 ^ S (length gs) -> forall t,
  (const 0) {{A}}> tw (T0 :: repeat TZ (S a) ++ ctr gs v ++ t) *> (const 0) -->*
  (const 0) {{A}}> tw (T0 :: repeat TZ (S (S a)) ++ ctr gs (S v) ++ t) *> (const 0).
Proof.
  intros Hv t.
  follow (IncL gs v (S a) Hv).
  (* 0inf <F tw(T0 :: 100^(S a) ++ ctr(Sv) ++ t) ; peel 00 100 and bounce *)
  cbn [repeat app]. rewrite !tw_cons. cbn [tokw]. rewrite !Str_app_assoc.
  follow Bnc. finish.
Qed.

(** ** Overflow return: C sweeps a T0-free word, turns at the next 0, then retf returns.
    This is the whole tail table T(f) of the write-up, with no 2^14-entry table: the head
    stops at the first 0 of the tail and the leftward return is the finite automaton [retf]. *)
Lemma OvRet w rest : noT0 w ->
  forall m' ps' rs', retf E (prc w ++ [P]) (T1 :: rest) = (m', ps', rs') ->
  forall l r,
  l {{A}}> tw (T0 :: w ++ T0 :: rest) *> r -->*
  l <* pl ps' <{{m'}} tw rs' *> r.
Proof.
  intros Hw m' ps' rs' Hr l r.
  rewrite tw_cons. cbn [tokw]. rewrite (tw_app w (T0 :: rest)), !Str_app_assoc.
  follow AT0.
  follow (Csweep w Hw).
  rewrite tw_cons. cbn [tokw]. rewrite Str_app_assoc.
  follow CT0.
  (* now:  l <* [0;1] <* pl (prc w) <{{E}} [0;1] *> tw rest *> r *)
  assert (H := retf_spec (prc w ++ [P]) E (T1 :: rest) m' ps' rs' Hr l r).
  rewrite pl_app in H. cbn [pl pw] in H.
  cbn [tw tokw] in H.
  rewrite !Str_app_assoc in H.
  follow H. finish.
Qed.

(** ** Pause rules (proof.md section 3) *)
Ltac tnorm := rewrite <- ?app_assoc; repeat (rewrite ?tw_cons, ?tw_app, ?tw_Z); cbn [tokw]; rewrite ?Str_app_assoc.

Lemma TwoInc gs v p t L r : S (S v) < 2 ^ S (length gs) ->
  L <* [0] <* [1;0] {{A}}> tw (T0 :: repeat TZ p ++ ctr gs v ++ t) *> r -->*
  L {{A}}> tw (T0 :: repeat TZ (S p) ++ ctr gs (S (S v)) ++ t) *> r.
Proof.
  intros Hv.
  follow (IncL gs v p ltac:(lia)).
  follow B1.
  follow (IncL gs (S v) p Hv).
  follow ENDl.
  cbn [repeat app]. rewrite !tw_cons. cbn [tokw]. rewrite !Str_app_assoc.
  finish.
Qed.

Lemma ZXg gs v p t L r : S (S v) < 2 ^ S (length gs) ->
  L <* [0] <* [1;0;1;0;0;1;0;1;0;0;1;0] {{A}}> tw (T0 :: repeat TZ p ++ ctr gs v ++ t) *> r -->*
  L {{A}}> tw (T0 :: ctr (S (S p) :: gs) (2 * S (S v)) ++ t) *> r.
Proof.
  intros Hv.
  follow (IncL gs v p ltac:(lia)).
  follow B1.
  follow (IncL gs (S v) p Hv).
  follow ENDZX.
  rewrite ctr_even. cbn [repeat app]. tnorm.
  finish.
Qed.

Lemma ZXP2g gs v p t L r : S v < 2 ^ S (length gs) ->
  L <* [0] <* [0;1;0;0;1;0] {{A}}> tw (T0 :: repeat TZ p ++ ctr gs v ++ t) *> r -->*
  L {{A}}> tw (T0 :: ctr (p :: gs) (2 * S v) ++ t) *> r.
Proof.
  intros Hv.
  follow (IncL gs v p Hv).
  rewrite tw_cons. cbn [tokw]. rewrite Str_app_assoc.
  follow BN.
  rewrite ctr_even. cbn [app]. tnorm.
  finish.
Qed.

(** ** The tail (proof.md sections 1.2, 4.2, 4.4) *)
Definition bt (b : bool) : tok := if b then T1 else T0.
Definition tailx (y z b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 : bool) (e : list bool) : list tok :=
  bt y :: bt z :: TZ :: T1 :: bt b4 :: bt b5 :: TZ :: T1 :: bt b6 :: TZ :: bt b7 :: TZ :: T1 ::
  bt b8 :: bt b9 :: TZ :: bt b10 :: TZ :: T1 :: bt b11 :: TZ :: bt b12 :: TZ :: bt b13 :: TZ ::
  bt b14 :: TZ :: bt b15 :: TZ :: T1 :: map bt e ++ [T1].
Definition tailw (x y z b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 : bool) (e : list bool) : list tok :=
  bt x :: tailx y z b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 e.

(** L*: x = 1, front unit (y, z); the stream is the tail followed by blank tape. *)
Definition Lst (y z : bool) (S : Stream Sym) : Prop :=
  exists b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 e,
  S = tw (tailw true y z b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 e) *> const 0.

Lemma TailRet pre rest m out : noT0 pre -> retf E (prc pre) [T1] = (m, [], out) ->
  forall l R, l {{C}}> tw (pre ++ T0 :: rest) *> R -->* l <{{m}} tw (out ++ rest) *> R.
Proof.
  intros Hn Hr l R.
  rewrite tw_app, Str_app_assoc, tw_cons. cbn [tokw]. rewrite Str_app_assoc.
  follow (Csweep pre Hn).
  follow CT0.
  assert (H := retf_spec (prc pre) E [T1] m [] out Hr l (tw rest *> R)).
  cbn [pl tw tokw app] in H. rewrite tw_app, Str_app_assoc. exact H.
Qed.

Lemma Tail10 l b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 e :
  l {{C}}> tw (tailw true true false b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 e) *> const 0 -->*
  l <{{E}} tw (tailw true false true b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 e) *> const 0.
Proof.
  exact (TailRet [T1; T1] (tl (tl (tailx true true b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 e)))
    E [T1; T0; T1] I eq_refl l (const 0)).
Qed.

Lemma Tail0z l z b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 e :
  l {{C}}> tw (tailw true false z b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 e) *> const 0 -->*
  l <{{F}} [0;0] *> tw (tailx true z b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 e) *> const 0.
Proof.
  exact (TailRet [T1] (tl (tailx true z b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 e))
    F [T0; T1] I eq_refl l (const 0)).
Qed.

Definition F1 : list tok := [T1; T1; T1; TZ; T1; T1; T1; TZ; T1; T1; TZ; T1; TZ; T1; T1; T1; TZ; T1; TZ; T1; T1; TZ; T1; TZ; T1; TZ; T1; TZ; T1; TZ; T1].
Definition F1E : list tok := [T1; T0; T0; TZ; T1; T1; T0; TZ; T1; T0; TZ; T0; TZ; T1; T1; T0; TZ; T0; TZ; T1; T0; TZ; T1; TZ; T0; TZ; T1; TZ; T0; TZ; T1].
Definition F1F : list tok := [T0; T1; T0; TZ; T1; T0; T0; TZ; T1; T0; TZ; T1; TZ; T1; T0; T0; TZ; T1; TZ; T1; T0; TZ; T0; TZ; T1; TZ; T0; TZ; T1; TZ; T1].
Lemma F1E_ret X : retf E (prc F1) X = (E, [], F1E ++ X).  Proof. reflexivity. Qed.
Lemma F1F_ret X : retf F (prc F1) X = (F, [], F1F ++ X).  Proof. reflexivity. Qed.
Lemma tailw_ones e : tailw true true true true true true true true true true true true true true true e = F1 ++ map bt e ++ [T1].
Proof. reflexivity. Qed.

Lemma prc_app xs ys : prc (xs ++ ys) = prc ys ++ prc xs.
Proof. unfold prc. rewrite map_app, rev_app_distr. reflexivity. Qed.
Lemma repeat_snoc {X} (x : X) n : repeat x n ++ [x] = x :: repeat x n.
Proof. induction n as [|n IH]; cbn; [|rewrite IH]; reflexivity. Qed.
Lemma prc_T1s j : prc (repeat T1 j) = repeat P j.
Proof.
  unfold prc. induction j as [|j IH]; [reflexivity|].
  cbn [repeat map rev]. rewrite IH. apply repeat_snoc.
Qed.
Lemma noT0_app xs ys : noT0 xs -> noT0 ys -> noT0 (xs ++ ys).
Proof. induction xs as [|[] xs IH]; cbn; tauto. Qed.
Lemma noT0_T1s j : noT0 (repeat T1 j).
Proof. induction j; cbn; auto. Qed.
Lemma map_bt_true j : map bt (repeat true j) = repeat T1 j.
Proof. induction j; cbn; [|rewrite IHj]; reflexivity. Qed.
Lemma map_bt_alt i : map bt ([true; false]^^i) = [T1; T0]^^i.
Proof. induction i; cbn; [|rewrite IHi]; reflexivity. Qed.

Lemma retf_PP i : forall ps rs, retf E (repeat P (2 * i) ++ ps) rs = retf E ps ([T1;T0]^^i ++ rs).
Proof.
  induction i as [|i IH]; intros ps rs; [reflexivity|].
  replace (2 * S i) with (S (S (2 * i))) by lia. cbn [repeat app retf].
  rewrite IH. f_equal. change (T1 :: T0 :: rs) with ([T1;T0] ++ rs).
  rewrite app_assoc, lpow_shift. reflexivity.
Qed.
Lemma retf_PPP i ps rs : retf E (repeat P (S (2 * i)) ++ ps) rs = retf F ps (T0 :: [T1;T0]^^i ++ rs).
Proof.
  replace (repeat P (S (2 * i)) ++ ps) with (repeat P (2 * i) ++ P :: ps).
  - rewrite retf_PP. reflexivity.
  - change (P :: ps) with ([P] ++ ps). rewrite app_assoc, repeat_snoc. reflexivity.
Qed.

Lemma e_split e : (exists j e', e = repeat true j ++ false :: e') \/ (exists m, e = repeat true m).
Proof.
  induction e as [|[] e IH].
  - right. exists O. reflexivity.
  - destruct IH as [(j & e' & ->)|(m & ->)].
    + left. exists (S j), e'. reflexivity.
    + right. exists (S m). reflexivity.
  - left. exists O, e. reflexivity.
Qed.

Lemma Tail11_end e :
  (exists S', (forall l, l {{C}}> tw (tailw true true true true true true true true true true true true true true true e) *> const 0 -->*
              l <{{E}} S') /\ Lst false false S') \/
  (exists S', (forall l, l {{C}}> tw (tailw true true true true true true true true true true true true true true true e) *> const 0 -->*
              l <{{F}} [0;0] *> S') /\ Lst true false ([0;1] *> S')).
Proof.
  rewrite tailw_ones.
  destruct (e_split e) as [(j & e' & ->)|(m & ->)].
  - assert (Hs : F1 ++ map bt (repeat true j ++ false :: e') ++ [T1] =
                 (F1 ++ repeat T1 j) ++ T0 :: (map bt e' ++ [T1])).
    { rewrite map_app, map_bt_true. cbn [map bt app]. rewrite <- ?app_assoc. cbn [app]. reflexivity. }
    rewrite Hs.
    assert (Hn : noT0 (F1 ++ repeat T1 j)) by (apply noT0_app; [exact I | apply noT0_T1s]).
    destruct (Nat.Even_or_Odd j) as [[i ->]|[i ->]].
    + left. eexists. split.
      * intros l. apply (TailRet _ _ E (F1E ++ [T1;T0]^^i ++ [T1]) Hn).
        rewrite prc_app, prc_T1s, retf_PP, F1E_ret. reflexivity.
      * exists true; exists false; exists false; exists false; exists true; exists false; exists false; exists false; exists true; exists false; exists true; exists false; exists ([true;false]^^i ++ true :: e').
        unfold tailw, tailx. rewrite map_app, map_bt_alt. cbn [map bt app]. rewrite <- ?app_assoc. cbn [app]. reflexivity.
    + replace (2 * i + 1) with (S (2 * i)) in * by lia.
      right. exists (tw (tl F1F ++ T0 :: [T1;T0]^^i ++ [T1] ++ map bt e' ++ [T1]) *> const 0). split.
      * intros l. replace (tl F1F ++ T0 :: [T1;T0]^^i ++ [T1] ++ map bt e' ++ [T1]) with
          (tl ((F1F ++ T0 :: [T1;T0]^^i ++ [T1]) ++ map bt e' ++ [T1]))
          by (unfold F1F; cbn [tl app]; rewrite <- !app_assoc; reflexivity).
        apply (TailRet _ _ F (F1F ++ T0 :: [T1;T0]^^i ++ [T1]) Hn).
        rewrite prc_app, prc_T1s, retf_PPP, F1F_ret. reflexivity.
      * exists false; exists false; exists false; exists true; exists false; exists false; exists true; exists false; exists false; exists true; exists false; exists true; exists (false :: [true;false]^^i ++ true :: e').
        unfold tailw, tailx. cbn [map]. rewrite map_app, map_bt_alt. cbn [map bt app]. rewrite <- ?app_assoc. cbn [app]. reflexivity.
  - assert (Hs : tw (F1 ++ map bt (repeat true m) ++ [T1]) *> const 0 =
                 tw ((F1 ++ repeat T1 (S m)) ++ T0 :: []) *> const 0).
    { rewrite map_bt_true. rewrite !tw_app, !Str_app_assoc. cbn [tw tokw app].
      replace (repeat T1 (S m)) with (repeat T1 m ++ [T1]) by apply repeat_snoc.
      rewrite tw_app, Str_app_assoc. cbn [tw tokw app].
      rewrite (const_unfold _ 0) at 1. rewrite (const_unfold _ 0) at 1. reflexivity. }
    rewrite Hs.
    assert (Hn : noT0 (F1 ++ repeat T1 (S m))) by (apply noT0_app; [exact I | apply noT0_T1s]).
    destruct (Nat.Even_or_Odd (S m)) as [[i Hi]|[i Hi]]; rewrite Hi in *.
    + left. eexists. split.
      * intros l. apply (TailRet _ _ E (F1E ++ [T1;T0]^^i ++ [T1]) Hn).
        rewrite prc_app, prc_T1s, retf_PP, F1E_ret. reflexivity.
      * exists true; exists false; exists false; exists false; exists true; exists false; exists false; exists false; exists true; exists false; exists true; exists false; exists ([true;false]^^i).
        rewrite app_nil_r. unfold tailw, tailx. rewrite map_bt_alt. cbn [map bt app]. rewrite <- ?app_assoc. cbn [app]. reflexivity.
    + replace (2 * i + 1) with (S (2 * i)) in * by lia.
      right. exists (tw (tl F1F ++ T0 :: [T1;T0]^^i ++ [T1]) *> const 0). split.
      * intros l. replace (tl F1F ++ T0 :: [T1;T0]^^i ++ [T1]) with
          (tl ((F1F ++ T0 :: [T1;T0]^^i ++ [T1]) ++ []))
          by (rewrite app_nil_r; unfold F1F; reflexivity).
        apply (TailRet _ _ F (F1F ++ T0 :: [T1;T0]^^i ++ [T1]) Hn).
        rewrite prc_app, prc_T1s, retf_PPP, F1F_ret. reflexivity.
      * exists false; exists false; exists false; exists true; exists false; exists false; exists true; exists false; exists false; exists true; exists false; exists true; exists (false :: [true;false]^^i).
        unfold tailw, tailx. cbn [map]. rewrite map_bt_alt. cbn [map bt app]. rewrite <- ?app_assoc. cbn [app]. reflexivity.
Qed.

Lemma Tail11 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 e :
  (exists S', (forall l, l {{C}}> tw (tailw true true true b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 e) *> const 0 -->*
              l <{{E}} S') /\ Lst false false S') \/
  (exists S', (forall l, l {{C}}> tw (tailw true true true b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 e) *> const 0 -->*
              l <{{F}} [0;0] *> S') /\ Lst true false ([0;1] *> S')).
Proof.
  destruct b4. 2: {
    left. exists (tw (tailw true false false true b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 e) *> const 0). split.
    - intros l; exact (TailRet [T1; T1; T1; TZ; T1] (bt b5 :: TZ :: T1 :: bt b6 :: TZ :: bt b7 :: TZ :: T1 :: bt b8 :: bt b9 :: TZ :: bt b10 :: TZ :: T1 :: bt b11 :: TZ :: bt b12 :: TZ :: bt b13 :: TZ :: bt b14 :: TZ :: bt b15 :: TZ :: T1 :: map bt e ++ [T1]) E [T1; T0; T0; TZ; T1; T1] I eq_refl l (const 0)).
    - exists true; exists b5; exists b6; exists b7; exists b8; exists b9; exists b10; exists b11; exists b12; exists b13; exists b14; exists b15; exists e. reflexivity. }
  destruct b5. 2: {
    right. exists (tw ([T1; T0; TZ; T1; T0; T1] ++ (TZ :: T1 :: bt b6 :: TZ :: bt b7 :: TZ :: T1 :: bt b8 :: bt b9 :: TZ :: bt b10 :: TZ :: T1 :: bt b11 :: TZ :: bt b12 :: TZ :: bt b13 :: TZ :: bt b14 :: TZ :: bt b15 :: TZ :: T1 :: map bt e ++ [T1])) *> const 0). split.
    - intros l; exact (TailRet [T1; T1; T1; TZ; T1; T1] (TZ :: T1 :: bt b6 :: TZ :: bt b7 :: TZ :: T1 :: bt b8 :: bt b9 :: TZ :: bt b10 :: TZ :: T1 :: bt b11 :: TZ :: bt b12 :: TZ :: bt b13 :: TZ :: bt b14 :: TZ :: bt b15 :: TZ :: T1 :: map bt e ++ [T1]) F [T0; T1; T0; TZ; T1; T0; T1] I eq_refl l (const 0)).
    - exists false; exists true; exists b6; exists b7; exists b8; exists b9; exists b10; exists b11; exists b12; exists b13; exists b14; exists b15; exists e. reflexivity. }
  destruct b6. 2: {
    right. exists (tw ([T1; T0; TZ; T1; T0; T0; TZ; T1; T1] ++ (TZ :: bt b7 :: TZ :: T1 :: bt b8 :: bt b9 :: TZ :: bt b10 :: TZ :: T1 :: bt b11 :: TZ :: bt b12 :: TZ :: bt b13 :: TZ :: bt b14 :: TZ :: bt b15 :: TZ :: T1 :: map bt e ++ [T1])) *> const 0). split.
    - intros l; exact (TailRet [T1; T1; T1; TZ; T1; T1; T1; TZ; T1] (TZ :: bt b7 :: TZ :: T1 :: bt b8 :: bt b9 :: TZ :: bt b10 :: TZ :: T1 :: bt b11 :: TZ :: bt b12 :: TZ :: bt b13 :: TZ :: bt b14 :: TZ :: bt b15 :: TZ :: T1 :: map bt e ++ [T1]) F [T0; T1; T0; TZ; T1; T0; T0; TZ; T1; T1] I eq_refl l (const 0)).
    - exists false; exists false; exists true; exists b7; exists b8; exists b9; exists b10; exists b11; exists b12; exists b13; exists b14; exists b15; exists e. reflexivity. }
  destruct b7. 2: {
    left. exists (tw (tailw true false false true false false true b8 b9 b10 b11 b12 b13 b14 b15 e) *> const 0). split.
    - intros l; exact (TailRet [T1; T1; T1; TZ; T1; T1; T1; TZ; T1; T1; TZ] (TZ :: T1 :: bt b8 :: bt b9 :: TZ :: bt b10 :: TZ :: T1 :: bt b11 :: TZ :: bt b12 :: TZ :: bt b13 :: TZ :: bt b14 :: TZ :: bt b15 :: TZ :: T1 :: map bt e ++ [T1]) E [T1; T0; T0; TZ; T1; T1; T0; TZ; T1; T0; TZ; T1] I eq_refl l (const 0)).
    - exists true; exists false; exists false; exists true; exists b8; exists b9; exists b10; exists b11; exists b12; exists b13; exists b14; exists b15; exists e. reflexivity. }
  destruct b8. 2: {
    left. exists (tw (tailw true false false true false false false true b9 b10 b11 b12 b13 b14 b15 e) *> const 0). split.
    - intros l; exact (TailRet [T1; T1; T1; TZ; T1; T1; T1; TZ; T1; T1; TZ; T1; TZ; T1] (bt b9 :: TZ :: bt b10 :: TZ :: T1 :: bt b11 :: TZ :: bt b12 :: TZ :: bt b13 :: TZ :: bt b14 :: TZ :: bt b15 :: TZ :: T1 :: map bt e ++ [T1]) E [T1; T0; T0; TZ; T1; T1; T0; TZ; T1; T0; TZ; T0; TZ; T1; T1] I eq_refl l (const 0)).
    - exists true; exists false; exists false; exists false; exists true; exists b9; exists b10; exists b11; exists b12; exists b13; exists b14; exists b15; exists e. reflexivity. }
  destruct b9. 2: {
    right. exists (tw ([T1; T0; TZ; T1; T0; T0; TZ; T1; T0; TZ; T1; TZ; T1; T0; T1] ++ (TZ :: bt b10 :: TZ :: T1 :: bt b11 :: TZ :: bt b12 :: TZ :: bt b13 :: TZ :: bt b14 :: TZ :: bt b15 :: TZ :: T1 :: map bt e ++ [T1])) *> const 0). split.
    - intros l; exact (TailRet [T1; T1; T1; TZ; T1; T1; T1; TZ; T1; T1; TZ; T1; TZ; T1; T1] (TZ :: bt b10 :: TZ :: T1 :: bt b11 :: TZ :: bt b12 :: TZ :: bt b13 :: TZ :: bt b14 :: TZ :: bt b15 :: TZ :: T1 :: map bt e ++ [T1]) F [T0; T1; T0; TZ; T1; T0; T0; TZ; T1; T0; TZ; T1; TZ; T1; T0; T1] I eq_refl l (const 0)).
    - exists false; exists false; exists false; exists true; exists false; exists true; exists b10; exists b11; exists b12; exists b13; exists b14; exists b15; exists e. reflexivity. }
  destruct b10. 2: {
    left. exists (tw (tailw true false false true false false false true false true b11 b12 b13 b14 b15 e) *> const 0). split.
    - intros l; exact (TailRet [T1; T1; T1; TZ; T1; T1; T1; TZ; T1; T1; TZ; T1; TZ; T1; T1; T1; TZ] (TZ :: T1 :: bt b11 :: TZ :: bt b12 :: TZ :: bt b13 :: TZ :: bt b14 :: TZ :: bt b15 :: TZ :: T1 :: map bt e ++ [T1]) E [T1; T0; T0; TZ; T1; T1; T0; TZ; T1; T0; TZ; T0; TZ; T1; T1; T0; TZ; T1] I eq_refl l (const 0)).
    - exists true; exists false; exists false; exists false; exists true; exists false; exists true; exists b11; exists b12; exists b13; exists b14; exists b15; exists e. reflexivity. }
  destruct b11. 2: {
    left. exists (tw (tailw true false false true false false false true false false true b12 b13 b14 b15 e) *> const 0). split.
    - intros l; exact (TailRet [T1; T1; T1; TZ; T1; T1; T1; TZ; T1; T1; TZ; T1; TZ; T1; T1; T1; TZ; T1; TZ; T1] (TZ :: bt b12 :: TZ :: bt b13 :: TZ :: bt b14 :: TZ :: bt b15 :: TZ :: T1 :: map bt e ++ [T1]) E [T1; T0; T0; TZ; T1; T1; T0; TZ; T1; T0; TZ; T0; TZ; T1; T1; T0; TZ; T0; TZ; T1; T1] I eq_refl l (const 0)).
    - exists true; exists false; exists false; exists false; exists true; exists false; exists false; exists true; exists b12; exists b13; exists b14; exists b15; exists e. reflexivity. }
  destruct b12. 2: {
    right. exists (tw ([T1; T0; TZ; T1; T0; T0; TZ; T1; T0; TZ; T1; TZ; T1; T0; T0; TZ; T1; TZ; T1; T0; TZ; T1] ++ (TZ :: bt b13 :: TZ :: bt b14 :: TZ :: bt b15 :: TZ :: T1 :: map bt e ++ [T1])) *> const 0). split.
    - intros l; exact (TailRet [T1; T1; T1; TZ; T1; T1; T1; TZ; T1; T1; TZ; T1; TZ; T1; T1; T1; TZ; T1; TZ; T1; T1; TZ] (TZ :: bt b13 :: TZ :: bt b14 :: TZ :: bt b15 :: TZ :: T1 :: map bt e ++ [T1]) F [T0; T1; T0; TZ; T1; T0; T0; TZ; T1; T0; TZ; T1; TZ; T1; T0; T0; TZ; T1; TZ; T1; T0; TZ; T1] I eq_refl l (const 0)).
    - exists false; exists false; exists false; exists true; exists false; exists false; exists true; exists false; exists true; exists b13; exists b14; exists b15; exists e. reflexivity. }
  destruct b13. 2: {
    left. exists (tw (tailw true false false true false false false true false false false true true b14 b15 e) *> const 0). split.
    - intros l; exact (TailRet [T1; T1; T1; TZ; T1; T1; T1; TZ; T1; T1; TZ; T1; TZ; T1; T1; T1; TZ; T1; TZ; T1; T1; TZ; T1; TZ] (TZ :: bt b14 :: TZ :: bt b15 :: TZ :: T1 :: map bt e ++ [T1]) E [T1; T0; T0; TZ; T1; T1; T0; TZ; T1; T0; TZ; T0; TZ; T1; T1; T0; TZ; T0; TZ; T1; T0; TZ; T1; TZ; T1] I eq_refl l (const 0)).
    - exists true; exists false; exists false; exists false; exists true; exists false; exists false; exists false; exists true; exists true; exists b14; exists b15; exists e. reflexivity. }
  destruct b14. 2: {
    right. exists (tw ([T1; T0; TZ; T1; T0; T0; TZ; T1; T0; TZ; T1; TZ; T1; T0; T0; TZ; T1; TZ; T1; T0; TZ; T0; TZ; T1; TZ; T1] ++ (TZ :: bt b15 :: TZ :: T1 :: map bt e ++ [T1])) *> const 0). split.
    - intros l; exact (TailRet [T1; T1; T1; TZ; T1; T1; T1; TZ; T1; T1; TZ; T1; TZ; T1; T1; T1; TZ; T1; TZ; T1; T1; TZ; T1; TZ; T1; TZ] (TZ :: bt b15 :: TZ :: T1 :: map bt e ++ [T1]) F [T0; T1; T0; TZ; T1; T0; T0; TZ; T1; T0; TZ; T1; TZ; T1; T0; T0; TZ; T1; TZ; T1; T0; TZ; T0; TZ; T1; TZ; T1] I eq_refl l (const 0)).
    - exists false; exists false; exists false; exists true; exists false; exists false; exists true; exists false; exists false; exists true; exists true; exists b15; exists e. reflexivity. }
  destruct b15. 2: {
    left. exists (tw (tailw true false false true false false false true false false false true false true true e) *> const 0). split.
    - intros l; exact (TailRet [T1; T1; T1; TZ; T1; T1; T1; TZ; T1; T1; TZ; T1; TZ; T1; T1; T1; TZ; T1; TZ; T1; T1; TZ; T1; TZ; T1; TZ; T1; TZ] (TZ :: T1 :: map bt e ++ [T1]) E [T1; T0; T0; TZ; T1; T1; T0; TZ; T1; T0; TZ; T0; TZ; T1; T1; T0; TZ; T0; TZ; T1; T0; TZ; T1; TZ; T0; TZ; T1; TZ; T1] I eq_refl l (const 0)).
    - exists true; exists false; exists false; exists false; exists true; exists false; exists false; exists false; exists true; exists false; exists true; exists true; exists e. reflexivity. }

  apply Tail11_end.
Qed.

(** ** Composition of the return automaton *)
Lemma retf_app_n n : forall ps1, length ps1 <= n -> forall m ps2 rs m1 rs1,
  retf m ps1 rs = (m1, [], rs1) -> retf m (ps1 ++ ps2) rs = retf m1 ps2 rs1.
Proof.
  induction n as [|n IH]; intros ps1 Hn m ps2 rs m1 rs1 Hr.
  - destruct ps1; [|cbn in Hn; lia].
    destruct m; cbn in Hr; inversion Hr; subst; reflexivity.
  - destruct ps1 as [|p ps1].
    { destruct m; cbn in Hr; inversion Hr; subst; reflexivity. }
    cbn in Hn.
    destruct m, p; cbn in Hr; try discriminate.
    + cbn [app retf]. apply (IH ps1 ltac:(lia) _ _ _ _ _ Hr).
    + cbn [app retf]. apply (IH ps1 ltac:(lia) _ _ _ _ _ Hr).
    + cbn [app retf]. apply (IH ps1 ltac:(lia) _ _ _ _ _ Hr).
    + destruct ps1 as [|[|] ps1]; try discriminate.
      destruct rs as [|[| |] rs]; try discriminate.
      cbn [app retf]. cbn in Hn. apply (IH ps1 ltac:(lia) _ _ _ _ _ Hr).
Qed.
Lemma retf_app m ps1 ps2 rs m1 rs1 :
  retf m ps1 rs = (m1, [], rs1) -> retf m (ps1 ++ ps2) rs = retf m1 ps2 rs1.
Proof. intros. eapply retf_app_n; [apply le_n|eassumption]. Qed.

(** ** Lemma RB: the return over the R block (proof.md section 4.3) *)
Lemma RB_E2 n : forall rs, retf E ([PZ;P]^^(2*n)) rs = (E, [], [T0;TZ;T1;TZ]^^n ++ rs).
Proof.
  induction n as [|n IH]; intros rs; [reflexivity|].
  replace (2 * S n) with (S (S (2 * n))) by lia. cbn [lpow app retf].
  rewrite IH. f_equal. f_equal. change (T0 :: TZ :: T1 :: TZ :: rs) with ([T0;TZ;T1;TZ] ++ rs).
  rewrite app_assoc, lpow_shift. reflexivity.
Qed.
Lemma RB_F2 n : forall rs, retf F ([PZ;P]^^(2*n)) (T0 :: rs) = (F, [], T0 :: [TZ;T0;TZ;T1]^^n ++ rs).
Proof.
  induction n as [|n IH]; intros rs; [reflexivity|].
  replace (2 * S n) with (S (S (2 * n))) by lia. cbn [lpow app retf].
  rewrite IH. f_equal. f_equal. f_equal. change (TZ :: T0 :: TZ :: T1 :: rs) with ([TZ;T0;TZ;T1] ++ rs).
  rewrite app_assoc, lpow_shift. reflexivity.
Qed.
Lemma RB_E1 n rs : retf E ([PZ;P]^^(S (2*n))) rs = (F, [], T0 :: [TZ;T0;TZ;T1]^^n ++ TZ :: rs).
Proof. cbn [lpow app retf]. apply RB_F2. Qed.
Lemma RB_F1 n rs : retf F ([PZ;P]^^(S (2*n))) (T0 :: rs) = (E, [], [T0;TZ;T1;TZ]^^n ++ T0 :: TZ :: T1 :: rs).
Proof. cbn [lpow app retf]. apply RB_E2. Qed.

Lemma shift4 n : [T0;TZ;T1] ++ [TZ;T0;TZ;T1]^^n = [T0;TZ;T1;TZ]^^n ++ [T0;TZ;T1].
Proof.
  induction n as [|n IH]; [reflexivity|].
  cbn [lpow]. change ([T0;TZ;T1] ++ [TZ;T0;TZ;T1] ++ [TZ;T0;TZ;T1]^^n) with
    ([T0;TZ;T1;TZ] ++ ([T0;TZ;T1] ++ [TZ;T0;TZ;T1]^^n)).
  rewrite IH, app_assoc. reflexivity.
Qed.

(** ** Digits, all-ones and all-zeros counters *)
Definition dig (b : tok) (g : nat) : list tok := b :: TZ :: T1 :: repeat TZ g.
Fixpoint LD (b : tok) (G : list nat) : list tok :=
  match G with [] => [] | g :: G' => dig b g ++ LD b G' end.

Lemma LD_app b G1 G2 : LD b (G1 ++ G2) = LD b G1 ++ LD b G2.
Proof. induction G1; cbn; [|rewrite IHG1, app_assoc]; reflexivity. Qed.
Lemma LD_ones b r : LD b (repeat 1%nat r) = [b;TZ;T1;TZ]^^r.
Proof. induction r; cbn; [|rewrite IHr]; reflexivity. Qed.

Lemma ctr_zero gs : ctr gs 0 = LD T0 gs ++ [T0].
Proof.
  induction gs as [|g gs IH]; [reflexivity|]. cbn [ctr LD dig].
  change (Nat.div2 O) with O. rewrite IH, <- !app_assoc. reflexivity.
Qed.
Lemma ctr_ones gs : ctr gs (2 ^ S (length gs) - 1) = LD T1 gs ++ [T1].
Proof.
  induction gs as [|g gs IH]; [reflexivity|].
  cbn [length]. replace (2 ^ S (S (length gs)) - 1) with (S (2 * (2 ^ S (length gs) - 1))).
  2: { rewrite (pow2S (S (length gs))). assert (0 < 2 ^ S (length gs)) by (apply Nat.neq_0_lt_0, Nat.pow_nonzero; lia). lia. }
  rewrite ctr_odd, IH. cbn [LD dig]. rewrite <- !app_assoc. reflexivity.
Qed.

Lemma noT0_LD1 G : noT0 (LD T1 G).
Proof.
  induction G as [|g G IH]; [exact I|]. cbn [LD dig].
  cbn [app noT0]. induction g; cbn; auto.
Qed.
Lemma noT0_U q : noT0 ([T1;TZ]^^q).
Proof. induction q; cbn; auto. Qed.
Lemma noT0_TZ a : noT0 (repeat TZ a).
Proof. induction a; cbn; auto. Qed.

Lemma prc_TZ a : prc (repeat TZ a) = repeat PZ a.
Proof.
  unfold prc. induction a as [|a IH]; [reflexivity|].
  cbn [repeat map rev]. rewrite IH. apply repeat_snoc.
Qed.
Lemma prc_U q : prc ([T1;TZ]^^q) = [PZ;P]^^q.
Proof.
  induction q as [|q IH]; [reflexivity|].
  cbn [lpow]. rewrite prc_app, IH. change (prc [T1;TZ]) with [PZ;P].
  rewrite lpow_shift. reflexivity.
Qed.
Lemma prc_dig g : prc (dig T1 g) = repeat PZ g ++ [P; PZ; P].
Proof. unfold dig. change (T1 :: TZ :: T1 :: repeat TZ g) with ([T1;TZ;T1] ++ repeat TZ g).
  rewrite prc_app, prc_TZ. reflexivity. Qed.
Lemma prc_LD G : prc (LD T1 G) = flat_map (fun g => repeat PZ g ++ [P; PZ; P]) (rev G).
Proof.
  induction G as [|g G IH]; [reflexivity|].
  cbn [LD rev]. rewrite prc_app, IH, prc_dig, flat_map_app. cbn. rewrite app_nil_r. reflexivity.
Qed.

(** the S-return through the processed large digits and the lead *)
Lemma retf_dig g ps rs : retf E (repeat PZ g ++ [P; PZ; P] ++ ps) rs =
  retf E ps (dig T0 g ++ rs).
Proof.
  revert rs. induction g as [|g IH]; intros rs; [reflexivity|].
  cbn [repeat app retf]. rewrite IH. f_equal. unfold dig. cbn [app repeat].
  change (TZ :: rs) with ([TZ] ++ rs). rewrite app_assoc, repeat_snoc. reflexivity.
Qed.
Lemma retf_LD G : forall ps rs, retf E (prc (LD T1 G) ++ ps) rs = retf E ps (LD T0 G ++ rs).
Proof.
  induction G as [|g G IH]; intros ps rs; [reflexivity|].
  cbn [LD]. rewrite prc_app, <- app_assoc, IH, prc_dig, <- app_assoc, retf_dig.
  rewrite app_assoc. reflexivity.
Qed.
Lemma retf_lead a rs : retf E (repeat PZ a ++ [P]) rs = (F, [], T0 :: repeat TZ a ++ rs).
Proof.
  revert rs. induction a as [|a IH]; intros rs; [reflexivity|].
  cbn [repeat app retf]. rewrite IH. cbn [app repeat].
  change (TZ :: rs) with ([TZ] ++ rs). rewrite app_assoc, repeat_snoc. reflexivity.
Qed.

Lemma AT0p l r : l {{A}}> [0;0] *> r -->+ l <* [0;1] {{C}}> r.  Proof. es. Qed.
Lemma OvSweep w : noT0 w -> forall l S,
  l {{A}}> tw (T0 :: w) *> S -->+ l <* pl (prc w ++ [P]) {{C}}> S.
Proof.
  intros Hw l S.
  rewrite tw_cons. cbn [tokw]. rewrite Str_app_assoc.
  eapply progress_evstep_trans; [apply AT0p|].
  follow (Csweep w Hw).
  rewrite pl_app, Str_app_assoc. finish.
Qed.

(** ** The overflow core: sweep, tail, R block, boundary (proof.md 4.1-4.3) *)
Definition sfx (H : bool) : list tok := if H then [TZ] else [TZ;T1;TZ].
Definition gsof (G : list nat) (r1 : nat) : list nat := G ++ 2%nat :: repeat 1%nat r1.
Definition qof (H : bool) (r1 : nat) : nat := if H then S (2 * r1) else 2 * S r1.
Definition ones (gs : list nat) : nat := 2 ^ S (length gs) - 1.

Lemma U2 r : [T1;TZ;T1;TZ]^^r = [T1;TZ]^^(2*r).
Proof.
  induction r as [|r IH]; [reflexivity|].
  replace (2 * S r) with (S (S (2 * r))) by lia. cbn [lpow]. rewrite IH. reflexivity.
Qed.

Lemma body_ones G r1 H : ctr (gsof G r1) (ones (gsof G r1)) ++ sfx H =
  LD T1 G ++ dig T1 2 ++ [T1;TZ]^^(qof H r1).
Proof.
  unfold ones, gsof. rewrite ctr_ones, LD_app. cbn [LD]. rewrite LD_ones, U2.
  rewrite <- !app_assoc. f_equal. f_equal. destruct H; cbn [qof sfx].
  - replace (S (2 * r1)) with (2 * r1 + 1) by lia. rewrite lpow_add. reflexivity.
  - replace (2 * S r1) with (2 * r1 + 2) by lia. rewrite lpow_add. reflexivity.
Qed.

Lemma body_zero G r1 : ctr (gsof G r1) 0 = LD T0 G ++ dig T0 2 ++ [T0;TZ;T1;TZ]^^r1 ++ [T0].
Proof. unfold gsof. rewrite ctr_zero, LD_app. cbn [LD]. rewrite LD_ones, <- !app_assoc. reflexivity. Qed.

Lemma noT0_w a G q : noT0 (repeat TZ a ++ LD T1 G ++ dig T1 2 ++ [T1;TZ]^^q).
Proof.
  repeat apply noT0_app; auto using noT0_TZ, noT0_LD1, noT0_U. exact I.
Qed.

Lemma prc_w a G q : prc (repeat TZ a ++ LD T1 G ++ dig T1 2 ++ [T1;TZ]^^q) ++ [P] =
  [PZ;P]^^q ++ [PZ;PZ;P;PZ;P] ++ (prc (LD T1 G) ++ repeat PZ a ++ [P]).
Proof.
  rewrite !prc_app, prc_U, prc_TZ, prc_dig. rewrite <- !app_assoc. reflexivity.
Qed.

Lemma BNp ps l r : l <* pl ([PZ;PZ;P;PZ;P] ++ ps) <{{F}} [0;0] *> r -->*
  l <* pl ps <* [1;0;1;0;0;1] {{A}}> [0;0;0;0;1;0;0;0;1] *> r.
Proof.
  rewrite pl_app, Str_app_assoc. cbn [pl pw app].
  change [0;1;0;0;1;0;0;1;0;1;0;0;1] with ([0;1;0;0;1;0] ++ [0;1;0;1;0;0;1]).
  rewrite Str_app_assoc. follow BN. finish.
Qed.

Lemma OvN1 G r1 a l St St' : (forall l', l' {{C}}> St -->* l' <{{E}} St') ->
  l {{A}}> tw (T0 :: repeat TZ a ++ ctr (gsof G r1) (ones (gsof G r1)) ++ sfx true) *> St -->+
  l <* pl (prc (LD T1 G) ++ repeat PZ a ++ [P]) <* [1;0;1;0;0;1] {{A}}>
    tw (T0 :: ctr (repeat 1%nat r1) 0 ++ sfx false) *> St'.
Proof.
  intros Ht.
  rewrite body_ones.
  eapply progress_evstep_trans; [apply (OvSweep _ (noT0_w a G (qof true r1)) l St)|].
  eapply evstep_trans; [apply Ht|].
  rewrite prc_w.
  set (X := prc (LD T1 G) ++ repeat PZ a ++ [P]).
  assert (Hr : retf E ([PZ;P]^^(qof true r1) ++ [PZ;PZ;P;PZ;P] ++ X) [] =
               (F, [PZ;PZ;P;PZ;P] ++ X, T0 :: [TZ;T0;TZ;T1]^^r1 ++ [TZ])).
  { cbn [qof]. rewrite (retf_app _ _ _ _ _ _ (RB_E1 r1 [])). reflexivity. }
  follow (retf_spec _ _ _ _ _ _ Hr l St').
  rewrite tw_cons. cbn [tokw]. rewrite Str_app_assoc.
  follow BNp.
  rewrite ctr_zero, LD_ones.
  replace (T0 :: ([T0;TZ;T1;TZ]^^r1 ++ [T0]) ++ sfx false) with
    ([T0;T0;TZ;T1] ++ [TZ;T0;TZ;T1]^^r1 ++ [TZ]).
  2: { cbn [sfx]. rewrite <- !app_assoc. change ([T0;T0;TZ;T1] ++ ([TZ;T0;TZ;T1]^^r1 ++ [TZ]))
         with (T0 :: ([T0;TZ;T1] ++ [TZ;T0;TZ;T1]^^r1) ++ [TZ]). rewrite shift4, <- !app_assoc. reflexivity. }
  rewrite !tw_app, !Str_app_assoc. finish.
Qed.

Lemma OvN0 G r1 a l St S0 : (forall l', l' {{C}}> St -->* l' <{{F}} [0;0] *> S0) ->
  l {{A}}> tw (T0 :: repeat TZ a ++ ctr (gsof G r1) (ones (gsof G r1)) ++ sfx false) *> St -->+
  l <* pl (prc (LD T1 G) ++ repeat PZ a ++ [P]) <* [1;0;1;0;0;1] {{A}}>
    tw (T0 :: ctr (repeat 1%nat (S r1)) 0 ++ sfx true) *> ([0;1] *> S0).
Proof.
  intros Ht.
  rewrite body_ones.
  eapply progress_evstep_trans; [apply (OvSweep _ (noT0_w a G (qof false r1)) l St)|].
  eapply evstep_trans; [apply Ht|].
  rewrite prc_w.
  set (X := prc (LD T1 G) ++ repeat PZ a ++ [P]).
  assert (Hr : retf F ([PZ;P]^^(qof false r1) ++ [PZ;PZ;P;PZ;P] ++ X) [T0] =
               (F, [PZ;PZ;P;PZ;P] ++ X, T0 :: [TZ;T0;TZ;T1]^^(S r1) ++ [])).
  { cbn [qof]. rewrite (retf_app _ _ _ _ _ _ (RB_F2 (S r1) [])). reflexivity. }
  follow (retf_spec _ _ _ _ _ _ Hr l S0).
  rewrite tw_cons. cbn [tokw]. rewrite Str_app_assoc.
  follow BNp.
  assert (E : tw (T0 :: ctr (repeat 1%nat (S r1)) 0 ++ sfx true) *> ([0;1] *> S0) =
              tw ([T0;T0;TZ;T1] ++ [TZ;T0;TZ;T1]^^(S r1)) *> S0).
  { change ([0;1] *> S0) with (tw [T1] *> S0). rewrite <- Str_app_assoc, <- tw_app.
    f_equal. f_equal. rewrite ctr_zero, LD_ones. cbn [sfx]. rewrite <- !app_assoc. cbn [app].
    f_equal. rewrite <- !app_assoc. cbn [app]. rewrite <- shift4. reflexivity. }
  rewrite E, app_nil_r, !tw_app, !Str_app_assoc. finish.
Qed.

Lemma OvS1 G r1 a l St S0 : (forall l', l' {{C}}> St -->* l' <{{F}} [0;0] *> S0) ->
  l {{A}}> tw (T0 :: repeat TZ a ++ ctr (gsof G r1) (ones (gsof G r1)) ++ sfx true) *> St -->+
  l <{{F}} tw (T0 :: repeat TZ a ++ ctr (gsof G r1) 0 ++ sfx true) *> ([0;1] *> S0).
Proof.
  intros Ht.
  rewrite body_ones.
  eapply progress_evstep_trans; [apply (OvSweep _ (noT0_w a G (qof true r1)) l St)|].
  eapply evstep_trans; [apply Ht|].
  rewrite prc_w.
  assert (Hr : retf F ([PZ;P]^^(qof true r1) ++ [PZ;PZ;P;PZ;P] ++ prc (LD T1 G) ++ repeat PZ a ++ [P]) [T0] =
    (F, [], T0 :: repeat TZ a ++ LD T0 G ++ dig T0 2 ++ [T0;TZ;T1;TZ]^^r1 ++ [T0;TZ;T1])).
  { cbn [qof]. rewrite (retf_app _ _ _ _ _ _ (RB_F1 r1 [])).
    change [PZ;PZ;P;PZ;P] with (repeat PZ 2 ++ [P;PZ;P]). rewrite <- app_assoc, retf_dig, retf_LD, retf_lead.
    rewrite <- ?app_assoc. reflexivity. }
  assert (E : tw (T0 :: repeat TZ a ++ ctr (gsof G r1) 0 ++ sfx true) *> ([0;1] *> S0) =
    tw (T0 :: repeat TZ a ++ LD T0 G ++ dig T0 2 ++ [T0;TZ;T1;TZ]^^r1 ++ [T0;TZ;T1]) *> S0).
  { change ([0;1] *> S0) with (tw [T1] *> S0). rewrite <- Str_app_assoc, <- tw_app.
    f_equal. f_equal. rewrite body_zero. cbn [sfx app]. rewrite <- !app_assoc. cbn [app]. reflexivity. }
  rewrite E.
  follow (retf_spec _ _ _ _ _ _ Hr l S0).
  finish.
Qed.

Ltac fw H := eapply evstep_trans; [exact H|].

(** ** Macro steps: configurations IR in normal mode (W = 0inf) and pause mode *)
Definition KP (W : side) (p : nat) (gs : list nat) (v : nat) (H : bool) (St : side) : Q * tape :=
  W {{A}}> tw (T0 :: repeat TZ p ++ ctr gs v ++ sfx H) *> St.
Definition NN (gs : list nat) : nat := 2 ^ S (length gs).

Lemma wall0 : (const 0 <* [1] : side) = Str_app [1;0] (Str_app [0] (const 0)).
Proof. cbn. rewrite <- !const_unfold. reflexivity. Qed.

Lemma P100 n l p gs v H St : S (S v) < NN gs ->
  KP (Str_app ([1] ++ [0;0;1]^^(S n)) l) p gs v H St -->*
  KP (Str_app ([1] ++ [0;0;1]^^n) l) (S p) gs (S (S v)) H St.
Proof. intros Hv. exact (TwoInc gs v p (sfx H) (Str_app ([1] ++ [0;0;1]^^n) l) St Hv). Qed.

Lemma P100s m : forall n l p gs v H St, 2 * m + v < NN gs ->
  KP (Str_app ([1] ++ [0;0;1]^^(m + n)) l) p gs v H St -->*
  KP (Str_app ([1] ++ [0;0;1]^^n) l) (m + p) gs (2 * m + v) H St.
Proof.
  induction m as [|m IH]; intros n l p gs v H St Hv; [finish|].
  follow (P100 (m + n) l p gs v H St ltac:(lia)).
  follow (IH n l (S p) gs (S (S v)) H St ltac:(lia)).
  replace (m + S p) with (S m + p) by lia. replace (2 * m + S (S v)) with (2 * S m + v) by lia.
  finish.
Qed.

Lemma WX p gs v H St : S (S v) < NN gs ->
  KP (Str_app [1] (const 0)) p gs v H St -->* KP (const 0) (S p) gs (S (S v)) H St.
Proof. intros Hv. unfold KP. rewrite wall0. exact (TwoInc gs v p (sfx H) (const 0) St Hv). Qed.

Lemma Inc1 a gs v H St : S v < NN gs ->
  KP (const 0) (S a) gs v H St -->* KP (const 0) (S (S a)) gs (S v) H St.
Proof.
  intros Hv. unfold KP.
  follow (IncL gs v (S a) Hv).
  cbn [repeat app]. rewrite !tw_cons. cbn [tokw]. rewrite !Str_app_assoc.
  follow Bnc. finish.
Qed.

Lemma Incs m : forall a gs v H St, m + v < NN gs ->
  KP (const 0) (S a) gs v H St -->* KP (const 0) (m + S a) gs (m + v) H St.
Proof.
  induction m as [|m IH]; intros a gs v H St Hv; [finish|].
  follow (Inc1 a gs v H St ltac:(lia)).
  follow (IH (S a) gs (S v) H St ltac:(lia)).
  replace (m + S (S a)) with (S m + S a) by lia. replace (m + S v) with (S m + v) by lia.
  finish.
Qed.

(** zones: Zn(g) 1001 packed in the wall, innermost first *)
Fixpoint zw (L : list nat) : list Sym :=
  match L with [] => [] | g :: L' => [1;0;0;1] ++ [0;1;0]^^(S g) ++ zw L' end.
Fixpoint zv (L : list nat) (v : nat) : nat :=
  match L with [] => v | g :: L' => zv L' (2 * v + 2 * g) end.
Fixpoint zg (L : list nat) (p : nat) (gs : list nat) : list nat :=
  match L with [] => gs | g :: L' => zg L' (g - 2) (S (S p) :: gs) end.
Fixpoint zp (L : list nat) (p : nat) : nat :=
  match L with [] => p | g :: L' => zp L' (g - 2) end.

Lemma P010s m : forall X Y p gs v H St, 2 * m + v < NN gs ->
  KP (Str_app ([1;0] ++ [0;1;0]^^m ++ X) Y) p gs v H St -->*
  KP (Str_app ([1;0] ++ X) Y) (m + p) gs (2 * m + v) H St.
Proof.
  induction m as [|m IH]; intros X Y p gs v H St Hv; [finish|].
  follow (TwoInc gs v p (sfx H) (Str_app ([1;0] ++ [0;1;0]^^m ++ X) Y) St ltac:(unfold NN in Hv; lia)).
  follow (IH X Y (S p) gs (S (S v)) H St ltac:(lia)).
  replace (m + S p) with (S m + p) by lia. replace (2 * m + S (S v)) with (2 * S m + v) by lia.
  finish.
Qed.

Lemma Zone g L X Y p gs v H St : 2 <= g -> v + g < NN gs ->
  KP (Str_app ([1;0] ++ zw (g :: L) ++ X) Y) p gs v H St -->*
  KP (Str_app ([1;0] ++ zw L ++ X) Y) (g - 2) (S (S p) :: gs) (2 * v + 2 * g) H St.
Proof.
  intros Hg Hv. destruct g as [|[|g]]; try lia. replace (S (S g) - 2) with g by lia.
  unfold KP at 1. cbn [zw]. rewrite <- !app_assoc.
  fw (ZXg gs v p (sfx H) (Str_app ([1;0] ++ [0;1;0]^^g ++ zw L ++ X) Y) St ltac:(unfold NN in *; lia)).
  fw (P010s g (zw L ++ X) Y 0 (S (S p) :: gs) (2 * S (S v)) H St ltac:(unfold NN in *; cbn [length]; rewrite pow2S; lia)).
  replace (g + 0) with g by lia. replace (2 * g + 2 * S (S v)) with (2 * v + 2 * S (S g)) by lia.
  finish.
Qed.

Lemma zv_ge L : forall v, 2 ^ length L * v <= zv L v.
Proof.
  induction L as [|g L IH]; intros v; cbn [zv length]; [rewrite Nat.pow_0_r; lia|].
  specialize (IH (2 * v + 2 * g)). rewrite pow2S. nia.
Qed.
Lemma zg_len L : forall p gs, length (zg L p gs) = length L + length gs.
Proof. induction L as [|g L IH]; intros p gs; cbn [zg length]; [|rewrite IH; cbn [length]]; lia. Qed.

Lemma Zones L : Forall (le 2) L -> forall X Y p gs v H St,
  zv L v < 2 ^ (S (length gs) + length L) ->
  KP (Str_app ([1;0] ++ zw L ++ X) Y) p gs v H St -->*
  KP (Str_app ([1;0] ++ X) Y) (zp L p) (zg L p gs) (zv L v) H St.
Proof.
  induction L as [|g L IH]; intros HL X Y p gs v H St Hv; [finish|].
  inversion HL as [|? ? Hg HL']; subst.
  cbn [zv zg zp length] in *.
  assert (Hz := zv_ge L (2 * v + 2 * g)).
  assert (Hn : v + g < NN gs).
  { unfold NN.
    assert (E : 2 ^ (S (length gs) + S (length L)) = 2 ^ length L * (2 * 2 ^ S (length gs))).
    { rewrite Nat.add_succ_r, Nat.pow_succ_r', Nat.pow_add_r. ring. }
    rewrite E in Hv.
    assert (Hp : 0 < 2 ^ length L) by (apply Nat.neq_0_lt_0, Nat.pow_nonzero; lia).
    assert (H2 : 2 * v + 2 * g < 2 * 2 ^ S (length gs)).
    { apply (Nat.mul_lt_mono_pos_l (2 ^ length L)); [exact Hp|]. lia. }
    lia. }
  follow (Zone g L X Y p gs v H St Hg Hn).
  apply IH; [exact HL'|]. cbn [length].
  replace (S (S (length gs)) + length L) with (S (length gs) + S (length L)) by lia. exact Hv.
Qed.

(** ** Wall bookkeeping *)
Fixpoint gval (G : list nat) : nat := match G with [] => 0 | g :: G' => 2 * (g + gval G') end.

Lemma zv_app L1 : forall L2 v, zv (L1 ++ L2) v = zv L2 (zv L1 v).
Proof. induction L1; intros; cbn; auto. Qed.
Lemma zp_app L1 : forall L2 p, zp (L1 ++ L2) p = zp L2 (zp L1 p).
Proof. induction L1; intros; cbn; auto. Qed.
Lemma zg_app L1 : forall L2 p gs, zg (L1 ++ L2) p gs = zg L2 (zp L1 p) (zg L1 p gs).
Proof. induction L1; intros; cbn; auto. Qed.
Lemma zw_app L1 L2 : zw (L1 ++ L2) = zw L1 ++ zw L2.
Proof. induction L1; cbn; [|rewrite IHL1, <- !app_assoc]; reflexivity. Qed.
Lemma zv_rev G : zv (rev G) 0 = gval G.
Proof. induction G as [|g G IH]; [reflexivity|]. cbn [rev gval]. rewrite zv_app, IH. cbn. lia. Qed.
Lemma zg_rev G gs0 : Forall (le 2) G -> S (S (zp (rev G) 0)) :: zg (rev G) 0 gs0 = G ++ 2%nat :: gs0.
Proof.
  induction G as [|g G IH]; intros HG; [reflexivity|].
  inversion HG; subst. cbn [rev]. rewrite zp_app, zg_app. cbn [zp zg].
  rewrite (IH H2). cbn [app]. f_equal. lia.
Qed.
Lemma zp_rev_last G p : zp (rev G ++ [p]) 0 = p - 2.
Proof. rewrite zp_app. reflexivity. Qed.
Lemma zv_rev_last G p : zv (rev G ++ [p]) 0 = 2 * gval G + 2 * p.
Proof. rewrite zv_app, zv_rev. reflexivity. Qed.
Lemma zg_rev_last G p gs0 : Forall (le 2) G -> zg (rev G ++ [p]) 0 gs0 = G ++ 2%nat :: gs0.
Proof. intros HG. rewrite zg_app. cbn [zg]. apply zg_rev, HG. Qed.
Lemma zg_len' L p gs : length (zg L p gs) = length L + length gs.
Proof. apply zg_len. Qed.

Lemma pl_lead a : pl (repeat PZ a ++ [P]) = [0;1] ++ [0;0;1]^^a.
Proof. induction a as [|a IH]; [reflexivity|]. cbn [repeat app pl pw]. rewrite IH. reflexivity. Qed.

Lemma pl_PZ g : pl (repeat PZ g) = [0;1;0]^^g.
Proof. induction g; cbn; [|rewrite IHg]; reflexivity. Qed.

Lemma zw_LD_gen L : [1;0;0;1] ++ pl (flat_map (fun g => repeat PZ g ++ [P; PZ; P]) L) = zw L ++ [1;0;0;1].
Proof.
  induction L as [|g L IH]; [reflexivity|].
  cbn [flat_map zw]. rewrite !pl_app, pl_PZ. change (pl [P;PZ;P]) with ([0;1;0] ++ [1;0;0;1]).
  rewrite <- !app_assoc. rewrite IH. f_equal.
  rewrite app_assoc, lpow_shift. reflexivity.
Qed.

Lemma wallOv G W l : (l <* pl (prc (LD T1 G) ++ W) <* [1;0;1;0;0;1] : side) =
  Str_app ([1;0] ++ zw (rev G) ++ [1;0;0;1] ++ pl W) l.
Proof.
  rewrite <- Str_app_assoc. f_equal.
  rewrite pl_app, prc_LD. change [1;0;1;0;0;1] with ([1;0] ++ [1;0;0;1]).
  rewrite <- app_assoc, (app_assoc [1;0;0;1]), zw_LD_gen, <- !app_assoc. reflexivity.
Qed.

Lemma wallPO G p n l : Str_app ([1;0] ++ zw (rev G) ++ [1;0;0;1] ++ pl (repeat PZ p ++ [P]))
    (Str_app ([0;0;0;1] ++ [0;0;1]^^n) l) =
  Str_app ([1;0] ++ zw (rev G ++ [p]) ++ [0;0;1]^^(S n)) l.
Proof.
  rewrite <- Str_app_assoc. f_equal.
  rewrite zw_app, pl_app, pl_PZ. cbn [zw]. rewrite app_nil_r, <- !app_assoc.
  f_equal. f_equal. f_equal.
  change (pl [P] ++ [0;0;0;1] ++ [0;0;1]^^n) with ([0;1;0] ++ [0;0;1] ++ [0;0;1]^^n).
  rewrite app_assoc, lpow_shift. reflexivity.
Qed.

(** ends of the rebuild *)
Lemma ZXN a l p gs v H St : S (S v) < NN gs ->
  KP (Str_app ([1;0] ++ [1;0;0;1] ++ pl (repeat PZ (S (S a)) ++ [P])) l) p gs v H St -->*
  KP (Str_app ([1] ++ [0;0;1]^^a) l) 0 (S (S p) :: gs) (2 * S (S v)) H St.
Proof.
  intros Hv. unfold KP at 1. rewrite pl_lead.
  exact (ZXg gs v p (sfx H) (Str_app ([1] ++ [0;0;1]^^a) l) St Hv).
Qed.

Lemma ZXP n l p gs v H St : S (S (S v)) < NN gs ->
  KP (Str_app ([1;0] ++ [0;0;1]^^(S (S (S n)))) l) p gs v H St -->*
  KP (Str_app ([1] ++ [0;0;1]^^n) l) 0 (S p :: gs) (2 * S (S (S v))) H St.
Proof.
  intros Hv.
  fw (TwoInc gs v p (sfx H) (Str_app ([0;1] ++ [0;0;1]^^(S (S n))) l) St ltac:(unfold NN in Hv; lia)).
  exact (ZXP2g gs (S (S v)) (S p) (sfx H) (Str_app ([1] ++ [0;0;1]^^n) l) St Hv).
Qed.

(** ** NO, PO, SILENT, SILENTP with their rebuilds (proof.md 4.3, 5.2) *)
Definition OvNp (H : bool) (r1 : nat) (St : side) (H' : bool) (r1' : nat) (St' : side) : Prop :=
  forall G a l, l {{A}}> tw (T0 :: repeat TZ a ++ ctr (gsof G r1) (ones (gsof G r1)) ++ sfx H) *> St -->+
    l <* pl (prc (LD T1 G) ++ repeat PZ a ++ [P]) <* [1;0;1;0;0;1] {{A}}>
    tw (T0 :: ctr (repeat 1%nat r1') 0 ++ sfx H') *> St'.
Definition OvSp (r1 : nat) (St St' : side) : Prop :=
  forall G a l, l {{A}}> tw (T0 :: repeat TZ a ++ ctr (gsof G r1) (ones (gsof G r1)) ++ sfx true) *> St -->+
    l <{{F}} tw (T0 :: repeat TZ a ++ ctr (gsof G r1) 0 ++ sfx true) *> St'.

Lemma OvNp1 r1 St St' : (forall l', l' {{C}}> St -->* l' <{{E}} St') -> OvNp true r1 St false r1 St'.
Proof. intros Ht G a l. apply OvN1, Ht. Qed.
Lemma OvNp0 r1 St S0 : (forall l', l' {{C}}> St -->* l' <{{F}} [0;0] *> S0) ->
  OvNp false r1 St true (S r1) ([0;1] *> S0).
Proof. intros Ht G a l. apply OvN0, Ht. Qed.
Lemma OvSp1 r1 St S0 : (forall l', l' {{C}}> St -->* l' <{{F}} [0;0] *> S0) -> OvSp r1 St ([0;1] *> S0).
Proof. intros Ht G a l. apply OvS1, Ht. Qed.

Lemma len_gsof G r1 : length (gsof G r1) = length G + S r1.
Proof. unfold gsof. rewrite length_app. cbn [length]. rewrite repeat_length. lia. Qed.
Lemma pow_pos n : 0 < 2 ^ n.
Proof. apply Nat.neq_0_lt_0, Nat.pow_nonzero. lia. Qed.

Lemma NOrb H r1 St H' r1' St' G a : OvNp H r1 St H' r1' St' -> Forall (le 2) G ->
  gval G + 2 < 2 ^ (length G + S r1') ->
  KP (const 0) (S (S a)) (gsof G r1) (ones (gsof G r1)) H St -->+
  KP (Str_app ([1] ++ [0;0;1]^^a) (const 0)) 0 (gsof G r1') (2 * gval G + 4) H' St'.
Proof.
  intros Hov HG Hv.
  eapply progress_evstep_trans; [exact (Hov G (S (S a)) (const 0))|].
  rewrite wallOv.
  assert (HGr : Forall (le 2) (rev G)) by (apply Forall_rev, HG).
  assert (Hz : zv (rev G) 0 < 2 ^ (S (length (repeat 1%nat r1')) + length (rev G))).
  { rewrite zv_rev, repeat_length, length_rev. replace (S r1' + length G) with (length G + S r1') by lia. lia. }
  fw (Zones (rev G) HGr ([1;0;0;1] ++ pl (repeat PZ (S (S a)) ++ [P])) (const 0) 0 (repeat 1%nat r1') 0 H' St' Hz).
  assert (Hx : S (S (zv (rev G) 0)) < NN (zg (rev G) 0 (repeat 1%nat r1'))).
  { unfold NN. rewrite zg_len, zv_rev, repeat_length, length_rev.
    replace (S (length G + r1')) with (length G + S r1') by lia. lia. }
  fw (ZXN a (const 0) (zp (rev G) 0) (zg (rev G) 0 (repeat 1%nat r1')) (zv (rev G) 0) H' St' Hx).
  rewrite zg_rev by exact HG. rewrite zv_rev.
  replace (2 * S (S (gval G))) with (2 * gval G + 4) by lia.
  finish.
Qed.

Lemma ones_S gs : S (ones gs - 1) = ones gs.
Proof. unfold ones. assert (H := pow_pos (S (length gs))). rewrite pow2S in *. lia. Qed.
Lemma ones_lt gs : ones gs < NN gs.
Proof. unfold ones, NN. assert (H := pow_pos (S (length gs))). lia. Qed.

Lemma POrb H r1 St H' r1' St' G p n l0 : OvNp H r1 St H' r1' St' -> Forall (le 2) G -> 2 <= p ->
  2 * gval G + 2 * p + 3 < 2 ^ (length G + S (S r1')) ->
  KP (Str_app ([1] ++ [0;0;1]^^(S (S (S n)))) l0) p (gsof G r1) (ones (gsof G r1) - 1) H St -->*
  KP (Str_app ([1] ++ [0;0;1]^^n) l0) 0 (gsof (S (p - 2) :: G) r1') (2 * S (S (S (2 * gval G + 2 * p)))) H' St'.
Proof.
  intros Hov HG Hp Hv.
  assert (HI : S (ones (gsof G r1) - 1) < 2 ^ S (length (gsof G r1))) by (rewrite ones_S; apply ones_lt).
  fw (IncL (gsof G r1) (ones (gsof G r1) - 1) p HI (Str_app ([1] ++ [0;0;1]^^(S (S (S n)))) l0) St (sfx H)).
  rewrite ones_S.
  fw (B1 (Str_app ([0;1] ++ [0;0;1]^^(S (S n))) l0) (tw (T0 :: repeat TZ p ++ ctr (gsof G r1) (ones (gsof G r1)) ++ sfx H) *> St)).
  fw (progress_evstep _ _ _ (Hov G p (Str_app [0;0] (Str_app ([0;1] ++ [0;0;1]^^(S (S n))) l0)))).
  rewrite wallOv.
  replace (Str_app [0;0] (Str_app ([0;1] ++ [0;0;1]^^(S (S n))) l0)) with
    (Str_app ([0;0;0;1] ++ [0;0;1]^^(S (S n))) l0) by (rewrite <- Str_app_assoc; reflexivity).
  rewrite wallPO.
  assert (HGr : Forall (le 2) (rev G ++ [p])) by (apply Forall_app; split; [apply Forall_rev, HG | auto]).
  assert (Hz : zv (rev G ++ [p]) 0 < 2 ^ (S (length (repeat 1%nat r1')) + length (rev G ++ [p]))).
  { rewrite zv_rev_last, repeat_length, length_app, length_rev. cbn [length].
    replace (S r1' + (length G + 1)) with (length G + S (S r1')) by lia. lia. }
  fw (Zones (rev G ++ [p]) HGr ([0;0;1]^^(S (S (S n)))) l0 0 (repeat 1%nat r1') 0 H' St' Hz).
  assert (Hx : S (S (S (zv (rev G ++ [p]) 0))) < NN (zg (rev G ++ [p]) 0 (repeat 1%nat r1'))).
  { unfold NN. rewrite zg_len, zv_rev_last, repeat_length, length_app, length_rev. cbn [length].
    replace (S (length G + 1 + r1')) with (length G + S (S r1')) by lia. lia. }
  fw (ZXP n l0 (zp (rev G ++ [p]) 0) (zg (rev G ++ [p]) 0 (repeat 1%nat r1')) (zv (rev G ++ [p]) 0) H' St' Hx).
  rewrite zp_rev_last, zg_rev_last, zv_rev_last by exact HG.
  finish.
Qed.

Lemma SILENTP r1 St St' G p n l0 : OvSp r1 St St' ->
  KP (Str_app ([1] ++ [0;0;1]^^(S n)) l0) p (gsof G r1) (ones (gsof G r1) - 1) true St -->*
  KP (Str_app ([1] ++ [0;0;1]^^n) l0) (S p) (gsof G r1) 0 true St'.
Proof.
  intros Hov.
  assert (HI : S (ones (gsof G r1) - 1) < 2 ^ S (length (gsof G r1))) by (rewrite ones_S; apply ones_lt).
  fw (IncL (gsof G r1) (ones (gsof G r1) - 1) p HI (Str_app ([1] ++ [0;0;1]^^(S n)) l0) St (sfx true)).
  rewrite ones_S.
  fw (B1 (Str_app ([0;1] ++ [0;0;1]^^n) l0) (tw (T0 :: repeat TZ p ++ ctr (gsof G r1) (ones (gsof G r1)) ++ sfx true) *> St)).
  fw (progress_evstep _ _ _ (Hov G p (Str_app [0;0] (Str_app ([0;1] ++ [0;0;1]^^n) l0)))).
  fw (ENDl (Str_app ([0;1] ++ [0;0;1]^^n) l0) (tw (T0 :: repeat TZ p ++ ctr (gsof G r1) 0 ++ sfx true) *> St')).
  unfold KP. cbn [repeat app]. rewrite !tw_cons. cbn [tokw]. rewrite !Str_app_assoc.
  finish.
Qed.

Lemma SILENT r1 St St' G a : OvSp r1 St St' ->
  KP (const 0) (S a) (gsof G r1) (ones (gsof G r1)) true St -->+ KP (const 0) (S (S a)) (gsof G r1) 0 true St'.
Proof.
  intros Hov.
  eapply progress_evstep_trans; [exact (Hov G (S a) (const 0))|].
  unfold KP. cbn [repeat app]. rewrite !tw_cons. cbn [tokw]. rewrite !Str_app_assoc.
  follow Bnc. finish.
Qed.

(** ** The four paths between normal-mode overflows (proof.md section 5.2) *)
Definition KX (a : nat) (G : list nat) (r1 : nat) (St : side) : Q * tape :=
  KP (const 0) a (gsof G r1) (ones (gsof G r1)) true St.

Lemma pS k r : 2 ^ (k + S r) = 2 * 2 ^ (k + r).
Proof. rewrite Nat.add_succ_r. apply Nat.pow_succ_r'. Qed.
Lemma NN_gsof G r1 : NN (gsof G r1) = 4 * 2 ^ (length G + r1).
Proof. unfold NN. rewrite len_gsof, <- Nat.add_succ_r, pS, pS. lia. Qed.
Lemma ones_gsof G r1 : ones (gsof G r1) = 4 * 2 ^ (length G + r1) - 1.
Proof. rewrite <- NN_gsof. reflexivity. Qed.
Lemma Q_cons (g : nat) (G : list nat) r1 : 2 ^ (length (g :: G) + S r1) = 4 * 2 ^ (length G + r1).
Proof. cbn [length]. rewrite pS. rewrite Nat.add_succ_l, Nat.pow_succ_r'. lia. Qed.

Lemma KP_eq W p p' gs v v' H St : p = p' -> v = v' -> KP W p gs v H St = KP W p' gs v' H St.
Proof. intros -> ->. reflexivity. Qed.

Lemma pathS a G r1 St St' : OvSp r1 St St' -> 1 <= a ->
  KX a G r1 St -->+ KX (a + 4 * 2 ^ (length G + r1)) G r1 St'.
Proof.
  intros Hov Ha. unfold KX.
  assert (HO := ones_gsof G r1). assert (HN := NN_gsof G r1). assert (HP := pow_pos (length G + r1)).
  replace a with (S (a - 1)) at 1 by lia.
  eapply progress_evstep_trans; [apply (SILENT r1 St St' G (a - 1) Hov)|].
  fw (Incs (ones (gsof G r1)) (S (a - 1)) (gsof G r1) 0 true St' ltac:(lia)).
  rewrite (KP_eq _ _ (a + 4 * 2 ^ (length G + r1)) _ _ (ones (gsof G r1))) by lia.
  finish.
Qed.

(** NO with e0, then the pause up to PO#1 and PO#1 with e1: common prefix of P1, P1S, P3 *)
Lemma pre1 a G r1 St St1 S0 kap s : let Q := 2 ^ (length G + r1) in
  OvNp true r1 St false r1 St1 -> (forall l', l' {{C}}> St1 -->* l' <{{F}} [0;0] *> S0) ->
  Forall (le 2) G -> gval G + 6 + kap = Q -> a = s + Q + kap -> 8 <= s ->
  KX a G r1 St -->+
  KP (Str_app ([1] ++ [0;0;1]^^(s - 8)) (const 0)) 0 (gsof ((Q + 2 + kap) :: G) (S r1)) (8 * Q - 6) true ([0;1] *> S0).
Proof.
  intros Q Hov1 Ht2 HG HV Ha Hs. unfold KX.
  assert (HO := ones_gsof G r1). assert (HN := NN_gsof G r1). assert (HP := pow_pos (length G + r1)).
  fold Q in HO, HN, HP.
  replace a with (S (S (a - 2))) at 1 by lia.
  eapply progress_evstep_trans.
  { apply (NOrb true r1 St false r1 St1 G (a - 2) Hov1 HG). rewrite pS. fold Q. lia. }
  replace (a - 2) with ((Q + 3 + kap) + S (S (S (s - 8)))) by lia.
  fw (P100s (Q + 3 + kap) (S (S (S (s - 8)))) (const 0) 0 (gsof G r1) (2 * gval G + 4) false St1 ltac:(lia)).
  rewrite (KP_eq _ _ (Q + 3 + kap) _ _ (ones (gsof G r1) - 1)) by lia.
  fw (POrb false r1 St1 true (S r1) ([0;1] *> S0) G (Q + 3 + kap) (s - 8) (const 0) (OvNp0 r1 St1 S0 Ht2) HG
        ltac:(lia) ltac:(rewrite !pS; fold Q; lia)).
  replace (S (Q + 3 + kap - 2)) with (Q + 2 + kap) by lia.
  rewrite (KP_eq _ _ 0 _ _ (8 * Q - 6)) by lia.
  finish.
Qed.

Definition TailF (St S0 : side) : Prop := forall l', l' {{C}}> St -->* l' <{{F}} [0;0] *> S0.

Lemma gval_cons g G : gval (g :: G) = 2 * (g + gval G).
Proof. reflexivity. Qed.

Lemma pathP1 a G r1 St St1 S0 kap s : let Q := 2 ^ (length G + r1) in
  OvNp true r1 St false r1 St1 -> TailF St1 S0 ->
  Forall (le 2) G -> gval G + 6 + kap = Q -> a = s + Q + kap -> 8 <= s -> s <= 4 * Q + 9 ->
  KX a G r1 St -->+ KX (8 * Q + 12 - s) ((Q + 2 + kap) :: G) (S r1) ([0;1] *> S0).
Proof.
  intros Q Hov1 Ht2 HG HV Ha Hs1 Hs2.
  eapply progress_evstep_trans; [apply (pre1 a G r1 St St1 S0 kap s Hov1 Ht2 HG HV Ha Hs1)|].
  fold Q. set (G' := (Q + 2 + kap) :: G).
  assert (HN : NN (gsof G' (S r1)) = 16 * Q) by (rewrite NN_gsof; unfold G'; rewrite Q_cons; fold Q; lia).
  assert (HO : ones (gsof G' (S r1)) = 16 * Q - 1) by (unfold ones, NN in *; lia).
  assert (HP := pow_pos (length G + r1)). fold Q in HP.
  replace (s - 8) with (s - 8 + 0) at 1 by lia.
  fw (P100s (s - 8) 0 (const 0) 0 (gsof G' (S r1)) (8 * Q - 6) true ([0;1] *> S0) ltac:(lia)).
  fw (WX (s - 8 + 0) (gsof G' (S r1)) (2 * (s - 8) + (8 * Q - 6)) true ([0;1] *> S0) ltac:(lia)).
  fw (Incs (8 * Q + 19 - 2 * s) (s - 8 + 0) (gsof G' (S r1)) (S (S (2 * (s - 8) + (8 * Q - 6)))) true ([0;1] *> S0) ltac:(lia)).
  unfold KX. rewrite (KP_eq _ _ (8 * Q + 12 - s) _ _ (ones (gsof G' (S r1)))) by lia.
  finish.
Qed.

Lemma pathP1S a G r1 St St1 S0 St3 kap s : let Q := 2 ^ (length G + r1) in
  OvNp true r1 St false r1 St1 -> TailF St1 S0 -> OvSp (S r1) ([0;1] *> S0) St3 ->
  Forall (le 2) G -> gval G + 6 + kap = Q -> a = s + Q + kap -> 4 * Q + 11 <= s -> s <= 12 * Q + 9 ->
  KX a G r1 St -->+ KX (24 * Q + 12 - s) ((Q + 2 + kap) :: G) (S r1) St3.
Proof.
  intros Q Hov1 Ht2 Hov3 HG HV Ha Hs1 Hs2.
  eapply progress_evstep_trans; [apply (pre1 a G r1 St St1 S0 kap s Hov1 Ht2 HG HV Ha ltac:(lia))|].
  fold Q. set (G' := (Q + 2 + kap) :: G).
  assert (HN : NN (gsof G' (S r1)) = 16 * Q) by (rewrite NN_gsof; unfold G'; rewrite Q_cons; fold Q; lia).
  assert (HO : ones (gsof G' (S r1)) = 16 * Q - 1) by (unfold ones, NN in *; lia).
  assert (HP := pow_pos (length G + r1)). fold Q in HP.
  replace (s - 8) with ((4 * Q + 2) + S (s - 4 * Q - 11)) at 1 by lia.
  fw (P100s (4 * Q + 2) (S (s - 4 * Q - 11)) (const 0) 0 (gsof G' (S r1)) (8 * Q - 6) true ([0;1] *> S0) ltac:(lia)).
  rewrite (KP_eq _ _ (4 * Q + 2) _ _ (ones (gsof G' (S r1)) - 1)) by lia.
  fw (SILENTP (S r1) ([0;1] *> S0) St3 G' (4 * Q + 2) (s - 4 * Q - 11) (const 0) Hov3).
  replace (s - 4 * Q - 11) with (s - 4 * Q - 11 + 0) at 1 by lia.
  fw (P100s (s - 4 * Q - 11) 0 (const 0) (S (4 * Q + 2)) (gsof G' (S r1)) 0 true St3 ltac:(lia)).
  fw (WX (s - 4 * Q - 11 + S (4 * Q + 2)) (gsof G' (S r1)) (2 * (s - 4 * Q - 11) + 0) true St3 ltac:(lia)).
  fw (Incs (24 * Q + 19 - 2 * s) (s - 4 * Q - 11 + S (4 * Q + 2)) (gsof G' (S r1))
        (S (S (2 * (s - 4 * Q - 11) + 0))) true St3 ltac:(lia)).
  unfold KX. rewrite (KP_eq _ _ (24 * Q + 12 - s) _ _ (ones (gsof G' (S r1)))) by lia.
  finish.
Qed.

Lemma pathP3 a G r1 St St1 S0 St3 S4 kap s : let Q := 2 ^ (length G + r1) in
  OvNp true r1 St false r1 St1 -> TailF St1 S0 ->
  OvNp true (S r1) ([0;1] *> S0) false (S r1) St3 -> TailF St3 S4 ->
  Forall (le 2) G -> gval G + 6 + kap = Q -> a = s + Q + kap -> 4 * Q + 24 <= s -> s <= 36 * Q + 31 ->
  KX a G r1 St -->+ KX (68 * Q + 40 - s) (7 :: (4 * Q + 1) :: (Q + 2 + kap) :: G) (S (S r1)) ([0;1] *> S4).
Proof.
  intros Q Hov1 Ht2 Hov3 Ht4 HG HV Ha Hs1 Hs2.
  eapply progress_evstep_trans; [apply (pre1 a G r1 St St1 S0 kap s Hov1 Ht2 HG HV Ha ltac:(lia))|].
  fold Q. set (G' := (Q + 2 + kap) :: G).
  assert (HP := pow_pos (length G + r1)). fold Q in HP.
  assert (HN : NN (gsof G' (S r1)) = 16 * Q) by (rewrite NN_gsof; unfold G'; rewrite Q_cons; fold Q; lia).
  assert (HO : ones (gsof G' (S r1)) = 16 * Q - 1) by (unfold ones, NN in *; lia).
  assert (HG' : Forall (le 2) G') by (constructor; [lia | exact HG]).
  assert (HV' : gval G' = 4 * Q - 8) by (unfold G'; rewrite gval_cons; lia).
  assert (HL' : length G' = S (length G)) by reflexivity.
  (* pause up to PO#2 *)
  replace (s - 8) with ((4 * Q + 2) + S (S (S (s - 4 * Q - 13)))) at 1 by lia.
  fw (P100s (4 * Q + 2) (S (S (S (s - 4 * Q - 13)))) (const 0) 0 (gsof G' (S r1)) (8 * Q - 6) true ([0;1] *> S0) ltac:(lia)).
  rewrite (KP_eq _ _ (4 * Q + 2) _ _ (ones (gsof G' (S r1)) - 1)) by lia.
  fw (POrb true (S r1) ([0;1] *> S0) false (S r1) St3 G' (4 * Q + 2) (s - 4 * Q - 13) (const 0) Hov3 HG'
        ltac:(lia) ltac:(rewrite !pS, HL', Nat.add_succ_l, Nat.pow_succ_r'; fold Q; lia)).
  replace (S (4 * Q + 2 - 2)) with (4 * Q + 1) by lia.
  set (G'' := (4 * Q + 1) :: G').
  assert (HN2 : NN (gsof G'' (S r1)) = 32 * Q).
  { rewrite NN_gsof. unfold G'', G'. cbn [length]. rewrite !Nat.add_succ_l, !Nat.pow_succ_r', !pS. fold Q. lia. }
  assert (HO2 : ones (gsof G'' (S r1)) = 32 * Q - 1) by (unfold ones, NN in *; lia).
  assert (HG'' : Forall (le 2) G'') by (constructor; [lia | exact HG']).
  assert (HV'' : gval G'' = 16 * Q - 14) by (unfold G''; rewrite gval_cons; lia).
  assert (HL'' : length G'' = S (S (length G))) by reflexivity.
  replace (s - 4 * Q - 13) with (8 + S (S (S (s - 4 * Q - 24)))) at 1 by lia.
  fw (P100s 8 (S (S (S (s - 4 * Q - 24)))) (const 0) 0 (gsof G'' (S r1))
        (2 * S (S (S (2 * gval G' + 2 * (4 * Q + 2))))) false St3 ltac:(lia)).
  rewrite (KP_eq _ _ 8 _ _ (ones (gsof G'' (S r1)) - 1)) by lia.
  fw (POrb false (S r1) St3 true (S (S r1)) ([0;1] *> S4) G'' 8 (s - 4 * Q - 24) (const 0) (OvNp0 (S r1) St3 S4 Ht4) HG''
        ltac:(lia) ltac:(rewrite !pS, HL'', !Nat.add_succ_l, !Nat.pow_succ_r'; fold Q; lia)).
  replace (S (8 - 2)) with 7 by lia.
  set (G3 := 7 :: G'').
  assert (HN3 : NN (gsof G3 (S (S r1))) = 128 * Q).
  { rewrite NN_gsof. unfold G3, G'', G'. cbn [length]. rewrite !Nat.add_succ_l, !Nat.pow_succ_r', !pS. fold Q. lia. }
  assert (HO3 : ones (gsof G3 (S (S r1))) = 128 * Q - 1) by (unfold ones, NN in *; lia).
  replace (s - 4 * Q - 24) with (s - 4 * Q - 24 + 0) at 1 by lia.
  fw (P100s (s - 4 * Q - 24) 0 (const 0) 0 (gsof G3 (S (S r1))) (2 * S (S (S (2 * gval G'' + 2 * 8)))) true ([0;1] *> S4) ltac:(lia)).
  fw (WX (s - 4 * Q - 24 + 0) (gsof G3 (S (S r1))) (2 * (s - 4 * Q - 24) + 2 * S (S (S (2 * gval G'' + 2 * 8)))) true ([0;1] *> S4) ltac:(lia)).
  fw (Incs (72 * Q + 63 - 2 * s) (s - 4 * Q - 24 + 0) (gsof G3 (S (S r1)))
        (S (S (2 * (s - 4 * Q - 24) + 2 * S (S (S (2 * gval G'' + 2 * 8)))))) true ([0;1] *> S4) ltac:(lia)).
  unfold KX. rewrite (KP_eq _ _ (68 * Q + 40 - s) _ _ (ones (gsof G3 (S (S r1))))) by lia.
  finish.
Qed.

(** ** The invariant (proof.md section 5.3) and the induction step *)
Definition INV (a : nat) (G : list nat) (r1 : nat) (St : side) : Prop :=
  Forall (le 2) G /\ 64 <= 2 ^ (length G + r1) /\
  exists kap s, (kap = 2 \/ kap = 8) /\ gval G + 6 + kap = 2 ^ (length G + r1) /\
    a = s + 2 ^ (length G + r1) + kap /\
    ((Lst true true St /\ 24 <= s <= 2 ^ (length G + r1) + 2) \/
     (Lst true false St /\ ((8 <= s <= 4 * 2 ^ (length G + r1) - 14) \/
                             (4 * 2 ^ (length G + r1) + 24 <= s <= 8 * 2 ^ (length G + r1))))).

Lemma Lst_intro y z b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 e :
  Lst y z (tw (tailw true y z b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 e) *> const 0).
Proof.
  exists b4; exists b5; exists b6; exists b7; exists b8; exists b9; exists b10; exists b11;
  exists b12; exists b13; exists b14; exists b15; exists e. reflexivity.
Qed.

Lemma Q1 (g : nat) G r1 : 2 ^ (length (g :: G) + S r1) = 4 * 2 ^ (length G + r1).
Proof. apply Q_cons. Qed.
Lemma Q3 (g1 g2 g3 : nat) G r1 : 2 ^ (length (g1 :: g2 :: g3 :: G) + S (S r1)) = 32 * 2 ^ (length G + r1).
Proof. cbn [length]. rewrite !Nat.add_succ_l, !Nat.pow_succ_r', !pS. lia. Qed.

Lemma step a G r1 St : INV a G r1 St ->
  exists a' G' r1' St', KX a G r1 St -->+ KX a' G' r1' St' /\ INV a' G' r1' St'.
Proof.
  intros (HG & HQ & kap & s & Hk & HV & Ha & Ht).
  set (Q := 2 ^ (length G + r1)) in *.
  destruct Ht as [(HL & Hs) | (HL & Hs)].
  - (* front unit 11 *)
    destruct HL as (b4 & b5 & b6 & b7 & b8 & b9 & b10 & b11 & b12 & b13 & b14 & b15 & e & ->).
    destruct (Tail11 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 e) as [(S' & HE & HL') | (S0 & HF & HL')].
    + (* N: path P1 *)
      destruct HL' as (c4 & c5 & c6 & c7 & c8 & c9 & c10 & c11 & c12 & c13 & c14 & c15 & e' & ->).
      set (S0 := tw (tailx true false c4 c5 c6 c7 c8 c9 c10 c11 c12 c13 c14 c15 e') *> const 0).
      assert (Ht2 : TailF (tw (tailw true false false c4 c5 c6 c7 c8 c9 c10 c11 c12 c13 c14 c15 e') *> const 0) S0)
        by (intros l; apply Tail0z).
      exists (8 * Q + 12 - s), ((Q + 2 + kap) :: G), (S r1), ([0;1] *> S0). split.
      * apply (pathP1 a G r1 _ _ S0 kap s (OvNp1 r1 _ _ HE) Ht2 HG HV Ha); lia.
      * split; [constructor; [lia|exact HG]|]. rewrite Q1. fold Q. split; [lia|].
        exists 2, (4 * Q + 10 - s). split; [auto|]. rewrite gval_cons. split; [lia|]. split; [lia|].
        right. split; [exact (Lst_intro true false c4 c5 c6 c7 c8 c9 c10 c11 c12 c13 c14 c15 e')|]. lia.
    + (* S: path S *)
      exists (a + 4 * Q), G, r1, ([0;1] *> S0). split.
      * apply (pathS a G r1 _ _ (OvSp1 r1 _ S0 HF)); lia.
      * split; [exact HG|]. fold Q. split; [lia|].
        exists kap, (s + 4 * Q). split; [auto|]. split; [lia|]. split; [lia|].
        right. split; [exact HL'|]. lia.
  - (* front unit 10 *)
    destruct HL as (b4 & b5 & b6 & b7 & b8 & b9 & b10 & b11 & b12 & b13 & b14 & b15 & e & ->).
    set (St1 := tw (tailw true false true b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 e) *> const 0).
    assert (HE : forall l, l {{C}}> tw (tailw true true false b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 e) *> const 0 -->* l <{{E}} St1)
      by (intros l; apply Tail10).
    set (S0 := tw (tailx true true b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 e) *> const 0).
    assert (Ht2 : TailF St1 S0) by (intros l; apply Tail0z).
    destruct Hs as [Hs | Hs].
    + (* path P1 *)
      exists (8 * Q + 12 - s), ((Q + 2 + kap) :: G), (S r1), ([0;1] *> S0). split.
      * apply (pathP1 a G r1 _ St1 S0 kap s (OvNp1 r1 _ _ HE) Ht2 HG HV Ha); lia.
      * split; [constructor; [lia|exact HG]|]. rewrite Q1. fold Q. split; [lia|].
        exists 2, (4 * Q + 10 - s). split; [auto|]. rewrite gval_cons. split; [lia|]. split; [lia|].
        left. split; [exact (Lst_intro true true b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 e)|]. lia.
    + destruct (Tail11 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 e) as [(S3 & HE3 & HL3) | (S3 & HF3 & HL3)].
      * (* path P3 *)
        destruct HL3 as (c4 & c5 & c6 & c7 & c8 & c9 & c10 & c11 & c12 & c13 & c14 & c15 & e' & ->).
        set (S4 := tw (tailx true false c4 c5 c6 c7 c8 c9 c10 c11 c12 c13 c14 c15 e') *> const 0).
        assert (Ht4 : TailF (tw (tailw true false false c4 c5 c6 c7 c8 c9 c10 c11 c12 c13 c14 c15 e') *> const 0) S4)
          by (intros l; apply Tail0z).
        exists (68 * Q + 40 - s), (7 :: (4 * Q + 1) :: (Q + 2 + kap) :: G), (S (S r1)), ([0;1] *> S4). split.
        -- apply (pathP3 a G r1 _ St1 S0 _ S4 kap s (OvNp1 r1 _ _ HE) Ht2 (OvNp1 (S r1) _ _ HE3) Ht4 HG HV Ha); lia.
        -- split; [repeat constructor; try lia; exact HG|]. rewrite Q3. fold Q. split; [lia|].
           exists 8, (36 * Q + 32 - s). split; [auto|]. rewrite !gval_cons. split; [lia|]. split; [lia|].
           right. split; [exact (Lst_intro true false c4 c5 c6 c7 c8 c9 c10 c11 c12 c13 c14 c15 e')|]. lia.
      * (* path P1S *)
        exists (24 * Q + 12 - s), ((Q + 2 + kap) :: G), (S r1), ([0;1] *> S3). split.
        -- apply (pathP1S a G r1 _ St1 S0 _ kap s (OvNp1 r1 _ _ HE) Ht2 (OvSp1 (S r1) _ S3 HF3) HG HV Ha); lia.
        -- split; [constructor; [lia|exact HG]|]. rewrite Q1. fold Q. split; [lia|].
           exists 2, (20 * Q + 10 - s). split; [auto|]. rewrite gval_cons. split; [lia|]. split; [lia|].
           right. split; [exact HL3|]. lia.
Qed.

(** ** Initial segment and the theorem *)
Definition St0 : side :=
  tw (tailw true true true true true true false true true true true false true false true [false; true; false]) *> const 0.

Lemma init : c0 -->* KX 121 [28%nat] 5 St0.
Proof. unfold KX, KP, St0. solve_init. Qed.

Lemma INV0 : INV 121 [28%nat] 5 St0.
Proof.
  split; [repeat constructor; lia|]. cbn [length]. split; [cbn; lia|].
  exists 2, 55. split; [auto|]. cbn. split; [lia|]. split; [lia|].
  left. split; [exact (Lst_intro true true true true true false true true true true false true false true [false; true; false])|]. lia.
Qed.

Lemma nonhalt : ~ halts tm c0.
Proof.
  apply multistep_nonhalt with (c' := KX 121 [28%nat] 5 St0); [exact init|].
  apply (progress_nonhalt_cond tm _ (121, [28%nat], 5, St0)
    (fun '(a, G, r1, St) => KX a G r1 St) (fun '(a, G, r1, St) => INV a G r1 St)).
  - intros [[[a G] r1] St] HI.
    destruct (step a G r1 St HI) as (a' & G' & r1' & St' & Hs & HI').
    exists (a', G', r1', St'). split; assumption.
  - exact INV0.
Qed.


(*
```
     0    1
A   1RB  0LF
B   0RC  ---        halting transition: B reads 1
C   1RD  0RA
D   1LE  0RC
E   0LA  0LE
F   1LE  1LB

Token view (right of the lead):  T0 = 00,  T1 = 01,  TZ = 100 ;  processed  P = (10),  PZ = (010).
counter  ctr gs v  =  digits  b 100 01 (100)^g  with LSB leftmost (last digit = its bit only).
KP W p gs v H St :=  W A> 00 (100)^p <ctr gs v> <sfx H> St      (W = 0^inf: normal mode)
KX a G r1 St     :=  KP 0^inf a (G ++ 2 :: 1^r1) (all ones) 1 St (normal-mode overflow)

Inc1     KP 0^inf (a+1) gs v            -->*  KP 0^inf (a+2) gs (v+1)         (v+1 < 2^N)
P100     (100)^(n+1) 1 | p, v           -->*  (100)^n 1 | p+1, v+2
WX       1 | p, v                       -->*  0^inf | p+1, v+2  (normal mode)
Zone g   Y Zn(g) 1001 01 | p, gs, v     -->*  Y 01 | g-2, (p+2)::gs, 2v+2g
ZXN      (100)^(a+2) 10100101 | p, gs, v -->*  (100)^a 1 | 0, (p+2)::gs, 2v+4
ZXP      (100)^(n+3) 01 | p, gs, v      -->*  (100)^n 1 | 0, (p+1)::gs, 2v+6
NO/PO    overflow, tail answers N       -->+  wall of zones, then Zones, ZXN / ZXP
SILENT   overflow, tail answers S       -->+  KP 0^inf (a+1) gs 0
SILENTP  overflow in a pause, S         -->*  (100)^n 1 | p+1, 0

pathS    KX a G r1 St  -->+  KX (a+M) G r1 St'                                  front 11 -> 10
pathP1   KX a G r1 St  -->+  KX (2M+12-s) ((Q+2+k)::G) (r1+1) St''              10 -> 11, 11 -> 10
pathP1S  KX a G r1 St  -->+  KX (6M+12-s) ((Q+2+k)::G) (r1+1) St''              10 -> 10
pathP3   KX a G r1 St  -->+  KX (17M+40-s) (7::(4Q+1)::(Q+2+k)::G) (r1+2) St''   10 -> 10
         (Q = 2^(length G + r1), M = 4Q, k in {2,8}, a = s + Q + k)
```
*)
