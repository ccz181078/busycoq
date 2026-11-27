(* Shared base dispatcher for BusyCoq PRs #78 and #79.
   Control flow depends only on tape symbols, not counter representation
   or machine state names. *)
From BusyCoq Require Import Individual62.
Close Scope sym_scope.
Set Default Goal Selector "!".

(* The base dispatcher works on either representation. Its interface makes
   the partial affine operations explicit; the concrete ones always succeed. *)
Section BaseDispatcher.
Context {L R : Type}.
Variable tm : TM.
Variable hub sweep : Q.
Local Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Local Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Variable lword : L -> side.
Variable rword : R -> side.
Variable lv : L -> Prop.
Variable rv : R -> Prop.
Variable splitL stripL : L -> R -> option (L * R).
Variable splitR : L -> R -> L * R.
Variable popLeft : L -> option (Sym * L).
Variable popRight : R -> option (Sym * R).
Variable pushLeft0 pushLeft1 pushLeft110 : L -> L.
Variable pushRight0 pushRight1 pushRight001 : R -> R.

Definition baseDispatch (hd : Sym) (l : L) (r : R) : option (Sym * L * R) :=
  match hd with
  | S1 =>
    let '(l1, r_in) := splitR l r in
    match popRight r_in with
    | None => None
    | Some (b1, r1) =>
      match b1 with
      | S1 => Some (S0, l1, pushRight0 r1)
      | S0 =>
        match popRight r1 with
        | None => None
        | Some (b2, r2) =>
          match b2 with
          | S0 =>
            match popRight r2 with
            | None => None
            | Some (b3, r3) => Some (b3, pushLeft110 l1, r3)
            end
          | S1 =>
            match popRight r2 with
            | None => None
            | Some (b3, r3) =>
              match b3 with
              | S0 => Some (S1, pushLeft0 l1, pushRight0 (pushRight0 r3))
              | S1 => None
              end
            end
          end
        end
      end
    end
  | S0 =>
    match splitL l r with
    | None => None
    | Some (l1, r1) =>
      match stripL l1 (pushRight1 r1) with
      | None => None
      | Some (l_after, r_rem) =>
        match popLeft l_after with
        | None => None
        | Some (e, e_rem) =>
          match e with
          | S0 => Some (S1, pushLeft1 e_rem, r_rem)
          | S1 =>
            match popLeft e_rem with
            | None => None
            | Some (ab, a_rem) =>
              match ab with
              | S1 =>
                match popLeft a_rem with
                | None => None
                | Some (cb, c_rem) => Some (cb, c_rem, pushRight001 r_rem)
                end
              | S0 => Some (S1, pushLeft1 (pushLeft1 a_rem), r_rem)
              end
            end
          end
        end
      end
    end
  end.


Hypothesis splitL_spec : forall l r l' r', lv l -> rv r ->
  splitL l r = Some (l', r') -> lv l' /\ rv r' /\
  (lword l {{hub}}> (S0 >> rword r)) -->* (lword l' {{hub}}> (S0 >> rword r')).
Hypothesis splitR_spec : forall r l, lv l -> rv r ->
  lv (fst (splitR l r)) /\ rv (snd (splitR l r)) /\
  (lword l {{hub}}> (S1 >> rword r)) -->*
  (lword (fst (splitR l r)) {{hub}}> (S1 >> rword (snd (splitR l r)))).
Hypothesis stripL_spec : forall l r l' r', lv l -> rv r ->
  stripL l r = Some (l', r') -> lv l' /\ rv r' /\
  (lword l <{{sweep}} rword r) -->* (lword l' {{sweep}}> (S0 >> rword r')).
Hypothesis popLeft_spec : forall l l' b, lv l -> popLeft l = Some (b, l') ->
  lv l' /\ lword l = b >> lword l'.
Hypothesis popRight_spec : forall r r' b, rv r -> popRight r = Some (b, r') ->
  rv r' /\ rword r = b >> rword r'.
Hypothesis pushLeft0_spec : forall l, lv l -> lv (pushLeft0 l) /\ lword (pushLeft0 l) = S0 >> lword l.
Hypothesis pushLeft1_spec : forall l, lv l -> lv (pushLeft1 l) /\ lword (pushLeft1 l) = S1 >> lword l.
Hypothesis pushLeft110_spec : forall l, lv l ->
  lv (pushLeft110 l) /\ lword (pushLeft110 l) = S1 >> S1 >> S0 >> lword l.
Hypothesis pushRight0_spec : forall r, rv r -> rv (pushRight0 r) /\ rword (pushRight0 r) = S0 >> rword r.
Hypothesis pushRight1_spec : forall r, rv r -> rv (pushRight1 r) /\ rword (pushRight1 r) = S1 >> rword r.
Hypothesis pushRight001_spec : forall r, rv r ->
  rv (pushRight001 r) /\ rword (pushRight001 r) = S0 >> S0 >> S1 >> rword r.


Hypothesis enterSweep : forall l r : side,
  (l {{hub}}> (S0 >> r)) -->* (l <{{sweep}} (S1 >> r)).
Hypothesis reach_R1_lb : forall (l r : side) ,
  (l {{hub}}> (S1 >> S1 >> r)) -->+ (l {{hub}}> (S0 >> S0 >> r)).
Hypothesis reach_R2_lb : forall (b3 : Sym) (l r : side) ,
  (l {{hub}}> (S1 >> S0 >> S0 >> b3 >> r)) -->+
  ((S1 >> S1 >> S0 >> l) {{hub}}> (b3 >> r)).
Hypothesis reach_R3_lb : forall (l r : side) ,
  (l {{hub}}> (S1 >> S0 >> S1 >> S0 >> r)) -->+
  ((S0 >> l) {{hub}}> (S1 >> S0 >> S0 >> r)).
Hypothesis reach_L1_lb : forall (l r : side) ,
  ((S0 >> l) {{sweep}}> (S0 >> r)) -->+ ((S1 >> l) {{hub}}> (S1 >> r)).
Hypothesis reach_L2_lb : forall (cb : Sym) (l r : side) ,
  ((S1 >> S1 >> cb >> l) {{sweep}}> (S0 >> r)) -->+
  (l {{hub}}> (cb >> S0 >> S0 >> S1 >> r)).
Hypothesis reach_L3_lb : forall (l r : side) ,
  ((S1 >> S0 >> l) {{sweep}}> (S0 >> r)) -->+
  ((S1 >> S1 >> l) {{hub}}> (S1 >> r)).

Lemma baseDispatch_sound hd l r hd' l' r' : lv l -> rv r ->
  baseDispatch hd l r = Some (hd', l', r') ->
  lv l' /\ rv r' /\ (lword l {{hub}}> (hd >> rword r)) -->+ (lword l' {{hub}}> (hd' >> rword r')).
Proof.
  intros hvl hvr H.
  unfold baseDispatch in H.
  destruct hd as [|].
  - destruct (splitL l r) as [[l1 r1] |] eqn:EL; [| discriminate].
    destruct (splitL_spec l r l1 r1 hvl hvr EL) as [hvL1 [hvR1 hsw]].
    destruct (pushRight1_spec r1 hvR1) as [hvR1p hR1p].
    assert (hb0 : (lword l1 {{hub}}> (S0 >> rword r1)) -->*
                  (lword l1 <{{sweep}} rword (pushRight1 r1))).
    { rewrite hR1p. apply enterSweep. }
    destruct (stripL l1 (pushRight1 r1)) as [[l_after r_rem] |] eqn:EO; [| discriminate].
    destruct (stripL_spec l1 (pushRight1 r1) l_after r_rem hvL1 hvR1p EO)
      as [hvLa [hvRr hones]].
    pose proof (evstep_trans tm _ _ _ (evstep_trans tm _ _ _ hsw hb0) hones) as hpre.
    destruct (popLeft l_after) as [[e e_rem] |] eqn:EPE; [| discriminate].
    destruct (popLeft_spec l_after e_rem e hvLa EPE) as [hve hpe].
    destruct e as [|].
    + injection H as <- <- <-.
      destruct (pushLeft1_spec e_rem hve) as [hvl1 hexl1].
      split; [exact hvl1 | split; [exact hvRr |]].
      rewrite hpe in hpre. rewrite hexl1.
      exact (evstep_progress_trans tm _ _ _ hpre (reach_L1_lb (lword e_rem) (rword r_rem))).
    + destruct (popLeft e_rem) as [[ab a_rem] |] eqn:EPA; [| discriminate].
      destruct (popLeft_spec e_rem a_rem ab hve EPA) as [hva hpa].
      destruct ab as [|].
      * injection H as <- <- <-.
        destruct (pushLeft1_spec a_rem hva) as [hvl1 hexl1].
        destruct (pushLeft1_spec (pushLeft1 a_rem) hvl1) as [hvl2 hexl2].
        split; [exact hvl2 | split; [exact hvRr |]].
        rewrite hpe, hpa in hpre. rewrite hexl2, hexl1.
        exact (evstep_progress_trans tm _ _ _ hpre (reach_L3_lb (lword a_rem) (rword r_rem))).
      * destruct (popLeft a_rem) as [[cb c_rem] |] eqn:EPC; [| discriminate].
        injection H as <- <- <-.
        destruct (popLeft_spec a_rem c_rem cb hva EPC) as [hvc hpc].
        destruct (pushRight001_spec r_rem hvRr) as [hvr1 hexr1].
        split; [exact hvc | split; [exact hvr1 |]].
        rewrite hpe, hpa, hpc in hpre.
        rewrite hexr1.
        exact (evstep_progress_trans tm _ _ _ hpre (reach_L2_lb cb (lword c_rem) (rword r_rem))).
  - destruct (splitR_spec r l hvl hvr) as [hvL1 [hvR1 hsw]].
    destruct (splitR l r) as [l1 r_in]; cbn [fst snd] in hvL1, hvR1, hsw.
    destruct (popRight r_in) as [[b1 r1] |] eqn:EP1; [| discriminate].
    destruct (popRight_spec r_in r1 b1 hvR1 EP1) as [hvr1 hp1].
    destruct b1 as [|].
    + destruct (popRight r1) as [[b2 r2] |] eqn:EP2; [| discriminate].
      destruct (popRight_spec r1 r2 b2 hvr1 EP2) as [hvr2 hp2].
      destruct b2 as [|].
      * destruct (popRight r2) as [[b3 r3] |] eqn:EP3; [| discriminate].
        injection H as <- <- <-.
        destruct (popRight_spec r2 r3 b3 hvr2 EP3) as [hvr3 hp3].
        destruct (pushLeft110_spec l1 hvL1) as [hvl2 hexl2].
        split; [exact hvl2 | split; [exact hvr3 |]].
        rewrite hp1, hp2, hp3 in hsw.
        rewrite hexl2.
        exact (evstep_progress_trans tm _ _ _ hsw (reach_R2_lb b3 (lword l1) (rword r3))).
      * destruct (popRight r2) as [[b3 r3] |] eqn:EP3; [| discriminate].
        destruct (popRight_spec r2 r3 b3 hvr2 EP3) as [hvr3 hp3].
        destruct b3 as [|]; [| discriminate].
        injection H as <- <- <-.
        destruct (pushLeft0_spec l1 hvL1) as [hvl2 hexl2].
        destruct (pushRight0_spec r3 hvr3) as [hvr4 hexr4].
        destruct (pushRight0_spec (pushRight0 r3) hvr4) as [hvr5 hexr5].
        split; [exact hvl2 | split; [exact hvr5 |]].
        rewrite hp1, hp2, hp3 in hsw. rewrite hexl2, hexr5, hexr4.
        exact (evstep_progress_trans tm _ _ _ hsw (reach_R3_lb (lword l1) (rword r3))).
    + injection H as <- <- <-.
      destruct (pushRight0_spec r1 hvr1) as [hvr0 hexr0].
      split; [exact hvL1 | split; [exact hvr0 |]].
      rewrite hp1 in hsw. rewrite hexr0.
      exact (evstep_progress_trans tm _ _ _ hsw (reach_R1_lb (lword l1) (rword r1))).
Qed.
End BaseDispatcher.
