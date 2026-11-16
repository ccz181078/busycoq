From BusyCoq Require Import Individual62 Longitudinal ES_v3 Eqb.
Require Import ZArith ZifyNat Lia String List.
From BusyCoq Require Import BigUint.
Local Open Scope sym_scope.

Module TM1.
Definition tm := Eval compute in (TM_from_str "1LB0LE_1RC0LA_1RA1RD_0RC1RF_0RB1LB_1LA---").
Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Notation hR := (C,<[0]).
Notation hL := (B,[1;0;0;1;0;0]).
Notation hL0 := (B,@nil Sym).
Notation hL2 := (A,[0;1;0;0;1;0;0;1;0;0]).
Notation hL3 := (E,[0;0;1;0;0;1;0;0]).
Notation w := [1;0;0;1;0;0].
Notation w0 := [1;0;1;1;0;0].
Notation w1 := [1;0;1;0].
Notation w2 := [1;0].

Inductive Tp := H1 | H0 | H2 | H3.
Inductive RC :=
| D1 (a:nat) (r:RC)
| D2 (a:nat) (r:RC)
| D4 (a:nat) (r:RC)
| D3 (a:nat)
| DZ (a:nat) (r:RC)
| DY (a:nat) (r:RC).

Fixpoint toRC x :=
match x with
| D1 a r => w0 *> w^^a *> toRC r
| D2 a r => w1 *> w^^a *> toRC r
| D4 a r => w2 *> w^^a *> toRC r
| D3 a => w1^^a *> 0inf
| DZ a r => [1;0;1;0;0;0] *> w^^a *> toRC r
| DY a r => [1;0;1;0;1;0;1] *> w^^a *> toRC r
end.

(* The exceptional right pass has physical left guard 0101.  These four
   rules are open-tail contracts: the last three never call their tail. *)
Inductive ScanA: RC -> RC -> Prop :=
| A_D1 a r r': ScanA r r' -> ScanA (D1 a r) (DZ a r')
| A_stopZ a r: ScanA (DZ a r) (DZ 0 (D2 a r))
| A_stopD4 a r: ScanA (D4 (1+a) r) (DZ 0 (D1 a r))
| A_stopD2 a r: ScanA (D2 (1+a) r) (D4 1 (D1 a r)).

Lemma ScanA_spec r r':
  ScanA r r' ->
  forall l, l <* <[0;1;0;1] {{A}}> toRC r -->* l <{{B}} toRC r'.
Proof.
  intro H; induction H; intros; cbn[toRC].
  2-4: es.
  es; er; follow IHScanA; es.
Qed.

Inductive RInc: Tp -> RC -> RC -> Prop :=
| D1_Inc a r r': RInc H1 r r' -> RInc H1 (D1 a r) (D1 a r')
| D1_Inc0 a r r': RInc H0 r r' -> RInc H1 (D1 (1+a) r) (D1 a r')
| D1_Inc2 a r r': RInc H2 r r' -> RInc H1 (D1 a r) (D2 (1+a) r')
| D1_Inc3 a r r': RInc H3 r r' -> RInc H0 (D1 a r) (D4 1 (D1 a r'))
| D2_Inc a r r': RInc H1 r r' -> RInc H0 (D2 a r) (D2 (1+a) r')
| D2_Inc0 a r r': RInc H0 r r' -> RInc H0 (D2 a r) (D2 a r')
| D4_Inc a r r': RInc H1 r r' -> RInc H0 (D4 a r) (D4 (1+a) r')
| D4_Inc0 a r r': RInc H0 r r' -> RInc H0 (D4 a r) (D4 a r')
| D3_Inc a: RInc H0 (D3 a) (D3 (1+a))
| D2_Ov a r r': RInc H1 r r' -> RInc H2 (D1 0 (D2 a r)) (D1 a r')
| D2_Ov0 a r r': RInc H0 r r' -> RInc H2 (D1 0 (D2 (1+a) r)) (D1 a r')
| D2_Ov3 a r r': RInc H3 r r' -> RInc H3 (D1 0 (D2 a r)) (D2 0 (D1 a r'))
| D4_Ov a r r': RInc H1 r r' -> RInc H3 (D1 0 (D4 a r)) (D1 a r')
| D4_Ov0 a r r': RInc H0 r r' -> RInc H3 (D1 0 (D4 (1+a) r)) (D1 a r')
| D3_Ov2 a b: RInc H1 (D1 a (D1 0 (D3 (b*3+2)))) (D2 (2+a+b*2) (D3 1))
| D3_Ov1 a b: RInc H1 (D1 a (D1 0 (D3 (b*3+1)))) (D1 (1+a+b*2) (D3 1))
| D3_Ov0 a b: RInc H0 (D1 a (D1 0 (D3 (b*3+0)))) (D4 1 (D1 (a+b*2) (D3 1)))
| D4_Inc2 a r r': RInc H2 r r' -> RInc H0 (D4 a r) (DZ (1+a) r')
| Z_Inc a r: RInc H0 (DZ a r) (DY a r)
| Y_Inc a r r': ScanA r r' ->
    RInc H0 (DY (2+a) r) (D2 1 (D1 a r'))
| Y0_D2_Inc a r r': ScanA r r' ->
    RInc H0 (DY 0 (D2 (1+a) r)) (D2 0 (D4 1 (D4 a r'))).

Definition hLx tp :=
match tp with H1 => hL | H0 => hL0 | H2 => hL2 | H3 => hL3 end.

Lemma RInc_spec tp r r':
  RInc tp r r' ->
  forall l, l {{{ (hR,R) }}} toRC r -->* l {{{ (hLx tp,L) }}} toRC r'.
Proof.
  unfold hLx. intro H. induction H; intros; cbn[toRC].
  20-21: pose proof (ScanA_spec _ _ H) as Hs; es; er; follow Hs; es.
  19: es.
  15-17: ut; es' a b & l.
  9: ut; es' a & l.
  all: es; er; follow IHRInc; es.
Qed.

Definition lh (b:bool) :=
  if b then
    (0inf<*<[1;1;0]<*<[1]^^10<*<[1;0]^^5<*<[1]^^13<*<[0;1;1;1;0]<*<[1]^^13<*<[0;1;1;1;0;1;0]<*<[1]^^13)
  else
    (0inf<*<[1;1;0]<*<[1]^^10<*<[1;0]^^5<*<[1]^^13<*<[0;1;1;1;0]<*<[1]^^7<*<[0]<*<[1]^^7<*<[0;1;1;1;0]<*<[1]^^13).

Lemma LRst b r:
  lh b {{{ (hL,L) }}} toRC r -->+
  lh (negb b) {{{ (hR,R) }}} toRC (D1 2 r).
Proof. destruct b; cbn; es' & (toRC r). Qed.

Definition S' '(tp,r) := lh tp {{{ (hL,L) }}} toRC r.
Fixpoint D1s a n r :=
match n with O => r | S n => D1 a (D1s a n r) end.
Fixpoint DZs a n r :=
match n with O => r | S n => DZ a (DZs a n r) end.
Definition r0 :=
  D1s 2 10 (D1 0 (D4 2 (D1s 2 4 (D1 0 (D2 5 (D1s 5 2
  (D1 2 (D1 0 (D4 5 (D1s 5 3 (D2 15 (D3 1)))))))))))).

Lemma init: c0 -->* S' (true,r0).
Proof.
  eapply without_counter.
  eapply (multistep_c_spec _ 110942).
  vm_compute; repeat rewrite <-const_unfold; reflexivity.
Qed.

Lemma BigStep tp r r':
  RInc H1 (D1 2 r) r' -> S' (tp,r) -->+ S' (negb tp,r').
Proof.
  unfold S'. intro H. follow10 LRst.
  eapply RInc_spec in H. apply H.
Qed.

Lemma D1s_Inc a n r r':
  RInc H1 r r' -> RInc H1 (D1s a n r) (D1s a n r').
Proof. intro H; induction n; cbn[D1s]; auto using D1_Inc. Qed.

Lemma D1s_Inc0 a n r r':
  RInc H0 r r' ->
  RInc H1 (D1s (1+a) (1+n) r) (D1s (1+a) n (D1 a r')).
Proof.
  intro H; induction n; cbn[D1s Nat.add]; auto using D1_Inc, D1_Inc0.
Qed.

Lemma D1s_Inc2 a n r r':
  RInc H2 r r' ->
  RInc H1 (D1s a (1+n) r) (D1s a n (D2 (1+a) r')).
Proof. intro H; induction n; cbn[D1s Nat.add]; auto using D1_Inc, D1_Inc2. Qed.

Lemma D1s_Inc3 a n r r':
  RInc H3 r r' ->
  RInc H1 (D1s (1+a) (2+n) r)
    (D1s (1+a) n (D1 a (D4 1 (D1 (1+a) r')))).
Proof.
  intro H; induction n; cbn[D1s Nat.add]; auto using D1_Inc, D1_Inc0, D1_Inc3.
Qed.

Lemma D1s_add a n m r:
  D1s a (n+m) r = D1s a n (D1s a m r).
Proof. induction n; cbn[D1s Nat.add]; congruence. Qed.

Local Open Scope nat_scope.

Inductive Packed :=
| C1 (a n:N') (r:Packed)
| C2 (a:N') (r:Packed)
| C4 (a:N') (r:Packed)
| C3 (a:N')
| C5 (a n:N') (r:Packed)
| C6 (a:N') (r:Packed).

Fixpoint decode r :=
match r with
| C1 a n r => D1s (to_nat a) (to_nat n) (decode r)
| C2 a r => D2 (to_nat a) (decode r)
| C4 a r => D4 (to_nat a) (decode r)
| C3 a => D3 (to_nat a)
| C5 a n r => DZs (to_nat a) (to_nat n) (decode r)
| C6 a r => DY (to_nat a) (decode r)
end.

Definition put a n r :=
  if is0 n then r else
  match r with
  | C1 b m s => if eqb a b then C1 a (add n m) s else C1 a n r
  | _ => C1 a n r
  end.

Lemma put_spec a n r:
  decode (put a n r) = D1s (to_nat a) (to_nat n) (decode r).
Proof.
  unfold put. destruct (inj_is0 n); [rewrite e; reflexivity|].
  destruct r; try reflexivity.
  destruct (eqb_spec a a0); subst; cbn[decode]; rw_N'.
  - apply D1s_add.
  - reflexivity.
Qed.

Definition lift a n tp r :=
match pred n with
| None => Some (tp,r)
| Some n0 =>
  match tp with
  | H1 => Some (H1,put a n r)
  | H0 =>
      match pred a with
      | Some a0 => Some (H1,put a n0 (put a0 N1 r))
      | None => None
      end
  | H2 => Some (H1,put a n0 (C2 (succ a) r))
  | H3 =>
      let r := C4 N1 (put a N1 r) in
      match pred n0 with
      | None => Some (H0,r)
      | Some n1 =>
          match pred a with
          | Some a0 => Some (H1,put a n1 (put a0 N1 r))
          | None => None
          end
      end
  end
end.

Local Opaque put.

Lemma lift_spec a n tp r r0:
  RInc tp r0 (decode r) ->
  match lift a n tp r with
  | Some (tp',r') => RInc tp' (D1s (to_nat a) (to_nat n) r0) (decode r')
  | None => True
  end.
Proof.
  intro H. unfold lift.
  pose proof (inj_pred n) as En. destruct (pred n) as [n0|].
  2: rewrite En; exact H.
  destruct tp; cbn; rewrite ?put_spec; cbn[decode]; rw_N'.
  - apply D1s_Inc; exact H.
  - pose proof (inj_pred a) as Ea. destruct (pred a) as [a0|]; [|exact I].
    repeat rewrite put_spec. cbn[decode]. rewrite En,Ea.
    apply D1s_Inc0; exact H.
  - rewrite En. apply D1s_Inc2; exact H.
  - pose proof (inj_pred n0) as En0. destruct (pred n0) as [n1|].
    + pose proof (inj_pred a) as Ea. destruct (pred a) as [a0|]; [|exact I].
      repeat rewrite put_spec. cbn[decode]. repeat rewrite put_spec.
      rewrite En,En0,Ea.
      apply D1s_Inc3; exact H.
    + cbn[decode]. rewrite put_spec,En,En0. apply D1_Inc3; exact H.
Qed.

Definition N2 := Eval compute in (succ N1).
Definition N3 := Eval compute in (succ N2).

Definition terminal a b :=
match divmod_small b N3 with
| None => None
| Some (q,s) =>
    let c := add a (add q q) in
    if eqb s N0 then Some (H0,C4 N1 (C1 c N1 (C3 N1))) else
    if eqb s N1 then Some (H1,C1 (succ c) N1 (C3 N1)) else
    if eqb s N2 then Some (H1,C2 (succ (succ c)) (C3 N1)) else None
end.

Lemma terminal_spec a b:
match terminal a b with
| Some (tp,r) => RInc tp (D1 (to_nat a) (D1 0 (D3 (to_nat b)))) (decode r)
| None => True
end.
Proof.
  unfold terminal. destruct (divmod_small b N3) as [[q s]|] eqn:E; [|exact I].
  apply inj_divmod_small in E.
  change (to_nat b = 3*to_nat q+to_nat s /\ to_nat s<3) in E.
  destruct (eqb_spec s N0); [subst|];
  [|destruct (eqb_spec s N1); [subst|]];
  [| |destruct (eqb_spec s N2); [subst|exact I]];
  cbn[decode]; rw_N';
  change (to_nat N0) with 0 in *;
  change (to_nat N1) with 1 in *;
  change (to_nat N2) with 2 in *;
  cbn[D1s].
  - applys_eq (D3_Ov0 (to_nat a) (to_nat q)); flia.
  - applys_eq (D3_Ov1 (to_nat a) (to_nat q)); flia.
  - applys_eq (D3_Ov2 (to_nat a) (to_nat q)); flia.
Qed.

Definition ov (is2:bool) a tp r :=
match tp with
| H1 => Some ((if is2 then H2 else H3),put a N1 r)
| H0 =>
    match pred a with
    | Some a0 => Some ((if is2 then H2 else H3),put a0 N1 r)
    | None => None
    end
| H3 => if is2 then Some (H3,C2 N0 (put a N1 r)) else None
| H2 => None
end.

Lemma ov_spec is2 a tp r r0:
  RInc tp r0 (decode r) ->
  match ov is2 a tp r with
  | Some (tp',r') => RInc tp'
      (D1 0 (if is2 then D2 (to_nat a) r0 else D4 (to_nat a) r0)) (decode r')
  | None => True
  end.
Proof.
  intro H. unfold ov. destruct tp; destruct is2; cbn[decode];
    repeat rewrite put_spec; try exact I;
    try (constructor; exact H).
  all: pose proof (inj_pred a) as Ea; destruct (pred a) as [a0|]; [|exact I];
    cbn[decode]; rewrite put_spec,Ea; constructor; exact H.
Qed.

Local Transparent put.
Local Open Scope sym_scope.

(* A halting suffix can be reached through every ordinary finite prefix.
   The changed left words are irrelevant because the premise is uniform in l. *)
Lemma Cpass_halt (a:nat) (r:side):
  (forall l:side, halts tm (l <* [0] {{C}}> r)) ->
  forall l:side, halts tm (l <* [0] {{C}}> w^^a *> r).
Proof.
  intros H l. eapply halts_evstep.
  - apply (H (l <* [1;1;1;1;1;1]^^a)).
  - es' a & l r.
Qed.

Lemma D1_halt a r:
  (forall l, halts tm (l {{{(hR,R)}}} toRC r)) ->
  forall l, halts tm (l {{{(hR,R)}}} toRC (D1 a r)).
Proof.
  intros H l. cbn[toRC]. eapply halts_evstep.
  - apply (Cpass_halt a (toRC r) H (l <* <[0;1;1;1;0;1])).
  - es.
Qed.

Lemma D2_halt a r:
  (forall l, halts tm (l {{{(hR,R)}}} toRC r)) ->
  forall l, halts tm (l {{{(hR,R)}}} toRC (D2 a r)).
Proof.
  intros H l. cbn[toRC]. eapply halts_evstep.
  - apply (Cpass_halt a (toRC r) H (l <* <[0;1;0;1])).
  - es.
Qed.

Lemma D4_halt a r:
  (forall l, halts tm (l {{{(hR,R)}}} toRC r)) ->
  forall l, halts tm (l {{{(hR,R)}}} toRC (D4 a r)).
Proof.
  intros H l. cbn[toRC]. eapply halts_evstep.
  - apply (Cpass_halt a (toRC r) H (l <* <[0;1])).
  - es.
Qed.

Lemma D1s_halt a n r:
  (forall l, halts tm (l {{{(hR,R)}}} toRC r)) ->
  forall l, halts tm (l {{{(hR,R)}}} toRC (D1s a n r)).
Proof. intro H; induction n; cbn[D1s]; auto using D1_halt. Qed.

(* The 15-bit prefix is (10)^3 1(10)^3 11: 6 steps then Halt 3,
   exactly 32 raw steps to F reading 1, independently of a and r. *)
Lemma Y0_D20_D1_Halt a r l:
  halts tm (l {{{(hR,R)}}} toRC (DY 0 (D2 0 (D1 a r)))).
Proof.
  change (halts tm (l <* [0] {{C}}> [1;0;1;0;1;0;1] *>
    w1 *> w0 *> w^^a *> toRC r)).
  remember (toRC r) as s. es' a & l s.
Qed.

Local Close Scope sym_scope.

Lemma DZs_add a n m r:
  DZs a (n+m) r = DZs a n (DZs a m r).
Proof. induction n; cbn[DZs Nat.add]; congruence. Qed.

Definition putZ a n r :=
  if is0 n then r else
  match r with
  | C5 b m s => if eqb a b then C5 a (add n m) s else C5 a n r
  | _ => C5 a n r
  end.

Lemma putZ_spec a n r:
  decode (putZ a n r) = DZs (to_nat a) (to_nat n) (decode r).
Proof.
  unfold putZ. destruct (inj_is0 n); [rewrite e; reflexivity|].
  destruct r; try reflexivity.
  destruct (eqb_spec a a0); subst; cbn[decode]; rw_N'.
  - apply DZs_add.
  - reflexivity.
Qed.

Lemma ScanA_bulk a n r r':
  ScanA r r' -> ScanA (D1s a n r) (DZs a n r').
Proof. intro H; induction n; cbn[D1s DZs]; auto using A_D1. Qed.

Fixpoint scanA r : option Packed :=
  match r with
  | C1 a n s =>
      match scanA s with Some t => Some (putZ a n t) | None => None end
  | C2 a s =>
      match pred a with
      | Some a0 => Some (C4 N1 (put a0 N1 s))
      | None => None
      end
  | C4 a s =>
      match pred a with
      | Some a0 => Some (putZ N0 N1 (put a0 N1 s))
      | None => None
      end
  | C5 a n s =>
      match pred n with
      | Some n0 => Some (putZ N0 N1 (C2 a (putZ a n0 s)))
      | None => scanA s
      end
  | _ => None
  end.

Lemma scanA_spec r:
  match scanA r with Some s => ScanA (decode r) (decode s) | None => True end.
Proof.
  induction r as [a n r IH|a r IH|a r IH|a|a n r IH|a r IH];
    cbn[scanA decode]; try exact I.
  - destruct (scanA r); [rewrite putZ_spec; apply ScanA_bulk,IH|exact I].
  - pose proof (inj_pred a) as E. destruct (pred a); [|exact I].
    cbn[decode]. rewrite put_spec,E. apply A_stopD2.
  - pose proof (inj_pred a) as E. destruct (pred a); [|exact I].
    rewrite putZ_spec. cbn[decode]. rewrite put_spec,E. apply A_stopD4.
  - pose proof (inj_pred n) as E. destruct (pred n).
    + rewrite putZ_spec. cbn[decode]. rewrite putZ_spec,E. apply A_stopZ.
    + rewrite E; exact IH.
Qed.

Definition exceptional a r :=
  if is0 a then
    match r with
    | C2 b s =>
      match pred b with
      | Some b0 =>
        match scanA s with
        | Some t => Some (H0,C2 N0 (C4 N1 (C4 b0 t)))
        | None => None
        end
      | None => None
      end
    | _ => None
    end
  else
    match pred a with
    | Some a0 =>
      match pred a0 with
      | Some a1 =>
        match scanA r with
        | Some t => Some (H0,C2 N1 (put a1 N1 t))
        | None => None
        end
      | None => None
      end
    | None => None
    end.

Lemma exceptional_spec a r:
  match exceptional a r with
  | Some (tp,s) => RInc tp (DY (to_nat a) (decode r)) (decode s)
  | None => True
  end.
Proof.
  unfold exceptional. destruct (inj_is0 a) as [E|E].
  - rewrite E. destruct r as [b n s|b s|b s|b|b n s|b s]; try exact I.
    pose proof (inj_pred b) as Eb. destruct (pred b) as [b0|]; [|exact I].
    pose proof (scanA_spec s) as H. destruct (scanA s); [|exact I].
    cbn[decode]. rewrite Eb. apply Y0_D2_Inc,H.
  - pose proof (inj_pred a) as Ea. destruct (pred a) as [a0|]; [|exact I].
    pose proof (inj_pred a0) as Ea0. destruct (pred a0) as [a1|]; [|exact I].
    pose proof (scanA_spec r) as H. destruct (scanA r); [|exact I].
    cbn[decode]. rewrite put_spec,Ea,Ea0. apply Y_Inc,H.
Qed.

Fixpoint halt_test r :=
  match r with
  | C1 _ _ s | C2 _ s | C4 _ s => halt_test s
  | C6 a (C2 b (C1 _ n _)) =>
      if is0 a then if is0 b then negb (is0 n) else false else false
  | _ => false
  end.

Local Open Scope sym_scope.

Lemma halt_test_spec r:
  halt_test r = true ->
  forall l, halts tm (l <* [0] {{C}}> toRC (decode r)).
Proof.
  induction r as [a n r IH|a r IH|a r IH|a|a n r IH|a r IH];
    cbn[halt_test decode]; try discriminate.
  - intro H. apply D1s_halt,IH,H.
  - intro H. apply D2_halt,IH,H.
  - intro H. apply D4_halt,IH,H.
  - destruct r as [b n s|b s|b s|b|b n s|b s]; try discriminate.
    destruct s as [c n t|c t|c t|c|c n t|c t]; try discriminate.
    destruct (inj_is0 a) as [Ea|Ea]; [|discriminate].
    destruct (inj_is0 b) as [Eb|Eb]; [|discriminate].
    destruct (inj_is0 n) as [En|En]; [discriminate|].
    cbn[decode]. rewrite Ea,Eb.
    destruct (to_nat n); [contradiction|].
    intros _. apply Y0_D20_D1_Halt.
Qed.

Local Close Scope sym_scope.

Definition Result := option (Tp * Packed).
Definition Good (r:RC) (v:Result) :=
  match v with Some (h,s) => RInc h r (decode s) | None => True end.

Definition lifting a n (v:Result) :=
  match v with Some (h,s) => lift a n h s | None => None end.

Lemma lifting_spec a n r v:
  Good r v -> Good (D1s (to_nat a) (to_nat n) r) (lifting a n v).
Proof.
  destruct v as [[h s]|]; unfold Good, lifting.
  - apply lift_spec.
  - auto.
Qed.

Definition overflowing is2 a (v:Result) :=
  match v with Some (h,s) => ov is2 a h s | None => None end.

Lemma overflowing_spec (is2:bool) a r v:
  Good r v ->
  Good (D1 0 (if is2 then D2 (to_nat a) r else D4 (to_nat a) r))
    (overflowing is2 a v).
Proof.
  destruct v as [[h s]|]; unfold Good, overflowing.
  - apply ov_spec.
  - auto.
Qed.

Definition ordinary (is2:bool) a (v:Result) : Result :=
  match v with
  | Some (H1,s) =>
      Some (H0, if is2 then C2 (succ a) s else C4 (succ a) s)
  | Some (H0,s) =>
      Some (H0, if is2 then C2 a s else C4 a s)
  | Some (H2,s) =>
      if is2 then None else Some (H0,putZ (succ a) N1 s)
  | _ => None
  end.

Lemma ordinary_spec (is2:bool) a r v:
  Good r v ->
  Good (if is2 then D2 (to_nat a) r else D4 (to_nat a) r)
    (ordinary is2 a v).
Proof.
  destruct v as [[h s]|]; [destruct h|]; destruct is2;
    cbn[Good ordinary decode]; rewrite ?putZ_spec; rw_N';
    auto using D2_Inc,D2_Inc0,D4_Inc,D4_Inc0,D4_Inc2.
  exact (D4_Inc2 _ _ _).
Qed.

Fixpoint inc (r:Packed) : Result :=
  match r with
  | C3 a => Some (H0,C3 (succ a))
  | C2 a s => ordinary true a (inc s)
  | C4 a s => ordinary false a (inc s)
  | C5 a n s =>
      match pred n with
      | Some n0 => Some (H0,C6 a (putZ a n0 s))
      | None => inc s
      end
  | C6 a s => exceptional a s
  | C1 a n s =>
    match pred n with
    | None => inc s
    | Some n0 =>
      match s with
      | C3 b =>
        if is0 a then
          match pred n0 with
          | Some n1 => lifting a n1 (terminal a b)
          | None => lifting a n (inc s)
          end
        else lifting a n (inc s)
      | C2 b t =>
        if is0 a then lifting a n0 (overflowing true b (inc t))
        else lifting a n (inc s)
      | C4 b t =>
        if is0 a then lifting a n0 (overflowing false b (inc t))
        else lifting a n (inc s)
      | C1 b m t =>
        if is0 b then
          if eqb m N1 then
            match t with
            | C3 c => lifting a n0 (terminal a c)
            | _ => lifting a n (inc s)
            end
          else lifting a n (inc s)
        else lifting a n (inc s)
      | C5 _ _ _ | C6 _ _ => lifting a n (inc s)
      end
    end
  end.

Lemma D1s_snoc a n r:
  D1s a (S n) r = D1s a n (D1 a r).
Proof.
  induction n; [reflexivity|].
  change (D1 a (D1s a (S n) r) = D1 a (D1s a n (D1 a r))).
  now rewrite IHn.
Qed.

Lemma inc_spec r: Good (decode r) (inc r).
Proof.
  revert r. fix IH 1. intro r.
  destruct r as [a n s|a s|a s|a|a n s|a s].
  - cbn[inc decode].
    pose proof (IH s) as Hs.
    pose proof (inj_pred n) as En.
    destruct (pred n) as [n0|] eqn:PN.
    2: rewrite En; exact Hs.
    destruct s as [b m t|b t|b t|b|b m t|b t].
    + destruct (inj_is0 b) as [Eb|Eb].
      * destruct (eqb_spec m N1) as [Em|Em].
        -- subst m. destruct t as [c k u|c u|c u|c|c k u|c u];
             try (apply lifting_spec; exact Hs).
           rewrite En. cbn[decode]. rewrite Eb.
           change (Good
             (D1s (to_nat a) (S (to_nat n0)) (D1 0 (D3 (to_nat c))))
             (lifting a n0 (terminal a c))).
           rewrite D1s_snoc.
           apply lifting_spec. exact (terminal_spec a c).
        -- apply lifting_spec; exact Hs.
      * apply lifting_spec; exact Hs.
    + destruct (inj_is0 a) as [Ea|Ea].
      * rewrite En.
        rewrite D1s_snoc.
        apply lifting_spec. rewrite Ea.
        apply (overflowing_spec true b (decode t) (inc t)). apply IH.
      * apply lifting_spec; exact Hs.
    + destruct (inj_is0 a) as [Ea|Ea].
      * rewrite En.
        rewrite D1s_snoc.
        apply lifting_spec. rewrite Ea.
        apply (overflowing_spec false b (decode t) (inc t)). apply IH.
      * apply lifting_spec; exact Hs.
    + destruct (inj_is0 a) as [Ea|Ea].
      * pose proof (inj_pred n0) as En0.
        destruct (pred n0) as [n1|] eqn:PN0.
        -- rewrite En,En0.
           rewrite !D1s_snoc.
           apply lifting_spec.
           rewrite Ea at 2.
           exact (terminal_spec a b).
        -- apply lifting_spec; exact Hs.
      * apply lifting_spec; exact Hs.
    + apply lifting_spec; exact Hs.
    + apply lifting_spec; exact Hs.
  - cbn[inc decode]. apply (ordinary_spec true a (decode s) (inc s)). apply IH.
  - cbn[inc decode]. apply (ordinary_spec false a (decode s) (inc s)). apply IH.
  - cbn[inc Good decode]. rw_N'. apply D3_Inc.
  - cbn[inc Good decode].
    pose proof (inj_pred n) as En. destruct (pred n) as [n0|].
    + change (RInc H0 (DZs (to_nat a) (to_nat n) (decode s))
        (DY (to_nat a) (decode (putZ a n0 s)))).
      rewrite putZ_spec,En. apply Z_Inc.
    + rewrite En. apply IH.
  - exact (exceptional_spec a s).
Qed.

Definition step r :=
  match inc (put N2 N1 r) with
  | Some (H1,s) => Some s
  | _ => None
  end.

Definition packed0 :=
 C1 (of_nat 2) (of_nat 10)
 (C1 N0 N1
 (C4 (of_nat 2)
 (C1 (of_nat 2) (of_nat 4)
 (C1 N0 N1
 (C2 (of_nat 5)
 (C1 (of_nat 5) (of_nat 2)
 (C1 (of_nat 2) N1
 (C1 N0 N1
 (C4 (of_nat 5)
 (C1 (of_nat 5) (of_nat 3)
 (C2 (of_nat 15) (C3 N1)))))))))))).

Lemma packed0_spec: decode packed0 = r0.
Proof. reflexivity. Qed.

Definition bind_step (v:option Packed) (f:Packed -> option Packed) :=
  match v with Some r => f r | None => None end.

(* Binary iteration avoids constructing a unary 110-million-element fuel. *)
Fixpoint iterate_pos p r : option Packed :=
  match p with
  | xH => step r
  | xO q => bind_step (iterate_pos q r) (iterate_pos q)
  | xI q => bind_step (bind_step (iterate_pos q r) (iterate_pos q)) step
  end.
Definition iterate (n:N) r :=
  match n with BinNums.N0 => Some r | Npos p => iterate_pos p r end.


Definition WillHalt r := forall b, halts tm (S' (b,decode r)).
Definition transfer r v :=
  match v with Some s => WillHalt s -> WillHalt r | None => True end.

Lemma step_transfer r: transfer r (step r).
Proof.
  unfold step.
  pose proof (inc_spec (put N2 N1 r)) as H.
  destruct (inc (put N2 N1 r)) as [[tp s]|]; [destruct tp|];
    cbn[transfer Good] in *; try exact I.
  intro K; intro b. eapply halts_evstep; [apply K|].
  apply progress_evstep, BigStep.
  rewrite put_spec in H. exact H.
Qed.

Lemma transfer_bind r v f:
  transfer r v -> (forall s, transfer s (f s)) ->
  transfer r (bind_step v f).
Proof.
  destruct v as [s|]; cbn[bind_step transfer]; auto.
  intros H Hf. specialize (Hf s).
  destruct (f s); cbn[transfer] in *; tauto.
Qed.

Lemma iterate_pos_transfer p r: transfer r (iterate_pos p r).
Proof.
  revert r; induction p; intro r; cbn[iterate_pos].
  - apply transfer_bind; [apply transfer_bind; apply IHp|apply step_transfer].
  - apply transfer_bind; apply IHp.
  - apply step_transfer.
Qed.

Lemma iterate_transfer n r: transfer r (iterate n r).
Proof.
  destruct n; cbn[iterate transfer]; [trivial|apply iterate_pos_transfer].
Qed.

Lemma from_init r n:
  iterate n packed0 = Some r -> WillHalt r -> halts tm c0.
Proof.
  intros H K. pose proof (iterate_transfer n packed0) as Hn.
  rewrite H in Hn. unfold transfer in Hn.
  eapply halts_evstep; [apply (Hn K true)|].
  rewrite packed0_spec. apply init.
Qed.

Definition check n :=
  match iterate n packed0 with Some r => halt_test r | None => false end.

Lemma check_spec n: check n = true -> halts tm c0.
Proof.
  unfold check. destruct (iterate n packed0) as [r|] eqn:E; [|discriminate].
  intro H. eapply from_init; [exact E|].
  intro b. unfold S'.
  eapply halts_evstep; [|apply progress_evstep,LRst].
  apply D1_halt,halt_test_spec,H.
Qed.

Theorem halt: halts tm c0.
Proof. apply (check_spec 110596950%N). native_check_eq. Time Qed.

End TM1.

Print Assumptions TM1.halt.
