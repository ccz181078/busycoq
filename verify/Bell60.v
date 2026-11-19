(* Bell60: a complete RLE accelerator and its halting certificate.
   Only BusyCoq and standard-library dependencies; no stored long trace. *)
From BusyCoq Require Import Individual62 SimplTape ES_v2 ES_v3 BigUint Eqb Helper.
Require Import List Bool NArith ZArith ZifyNat Lia String.
Import ListNotations.

Module Bell60.
Definition tm := Eval compute in (TM_from_str "1RB1RE_1LC0LB_1LD1LC_0RA1RF_1RD1RE_---1LB").
Notation "c -->* c'" := (c -[tm]->* c') (at level 40).

Definition n1 := Eval compute in (BigUint.of_nat 1).
Definition n2 := Eval compute in (BigUint.of_nat 2).
Definition n4 := Eval compute in (BigUint.of_nat 4).
Definition n5 := Eval compute in (BigUint.of_nat 5).
Definition tape := list (bool * BigUint).

Definition push (b:bool) (n:BigUint) (t:tape) : tape :=
  if is0 n then t else
  match t with
  | [] => if b then [(b,n)] else []
  | (c,m)::r => if Bool.eqb b c then (b,BigUint.add n m)::r else (b,n)::t
  end.

Fixpoint pop (t:tape) : bool * tape :=
  match t with
  | [] => (false,[])
  | (b,n)::r =>
    match BigUint.pred n with
    | None => pop r
    | Some m => (b,if is0 m then r else (b,m)::r)
    end
  end.

Definition word (w:list bool) (t:tape) : tape :=
  fold_right (fun b r => push b n1 r) t w.

(* Some n is the whole 1^n token, None is one 001 token.
   revtokens is already in application order for the left return. *)
Fixpoint back (revtokens:list (option BigUint)) (phase:bool) (t:tape) : tape :=
  match revtokens with
  | [] => word (if phase then [true] else [true;false]) t
  | Some n::r => back r phase (push phase n t)
  | None::r => back r (negb phase)
       (word (if phase then [false;true;true] else [true;true;false]) t)
  end.

Definition result := (tape + bool)%type.

Definition scan_zero (next:tape -> list (option BigUint) -> result) t acc :=
  let '(a,t1) := pop t in
  let '(b,t2) := pop t1 in
  let '(c,t3) := pop t2 in
  if a then inr false else
  if b then
    if c then inl (back acc false (word [false;false;true] t3))
    else inr true
  else if c then next t3 (None::acc)
  else let '(d,t4) := pop t3 in
    if d then inl (back acc true (word [true;true;false;false] t4))
    else inl (back acc false (word [false;true;true;true] t4)).

Fixpoint scan (fuel:nat) (t:tape) (acc:list (option BigUint)) : result :=
  match fuel with
  | O => inr false
  | S fuel =>
    match t with
    | (true,n)::r => scan fuel r (Some n::acc)
    | _ => scan_zero (scan fuel) t acc
    end
  end.

Definition sweep t := scan 64 t [].

Definition step (t:tape) : result :=
  match t with
  | (true,a)::(false,z)::(true,two)::(false,b)::r =>
    if BigUint.eqb z n2 then
      if BigUint.eqb two n2 then
        let '(q,rem) := divmodc b (Uint63.of_Z 4%Z) in
        if is0 q then sweep t else
        inl (push true (BigUint.add a (BigUint.mulc q (Uint63.of_Z 6%Z)))
          (push false n2 (push true n2 (push false (Cons_simpl rem BigUintNil) r))))
      else sweep t
    else sweep t
  | _ => sweep t
  end.

Definition seed : tape := [(true,n4);(false,n2);(true,n5)].
Definition run (fuel:N) := N_iter_until step (inl seed) fuel.
Definition check (fuel:N) := match run fuel with inr b => b | _ => false end.

(* The logical interpretation is never evaluated by the checker. *)
Open Scope sym.
Definition bit (b:bool) : Sym := if b then 1 else 0.
Fixpoint denote (t:tape) : side := match t with
  | [] => 0inf
  | (b,n)::r => [bit b]^^(BigUint.to_nat n) *> denote r
  end.
Definition config t := 0inf <{{C}} denote t.

Lemma push_spec b n t :
  denote (push b n t) = [bit b]^^(BigUint.to_nat n) *> denote t.
Proof.
  unfold push; destruct (inj_is0 n) as [H|H].
  - rewrite H; reflexivity.
  - destruct t as [|[c m] r]; cbn [denote].
    + destruct b; cbn [bit]; [reflexivity|symmetry; apply lpow_all0_1].
    + destruct (Bool.eqb_spec b c); subst; cbn [denote].
      * rewrite inj_add, lpow_add, Str_app_assoc; reflexivity.
      * reflexivity.
Qed.

Lemma pop_spec t :
  let '(b,r) := pop t in denote t = bit b >> denote r.
Proof.
  induction t as [|[b n] r IH]; cbn [pop denote].
  - apply const_unfold.
  - pose proof (inj_pred n) as H; destruct (BigUint.pred n) as [m|].
    + rewrite H; destruct (inj_is0 m) as [Hm|Hm]; cbn [denote].
      * rewrite Hm; reflexivity.
      * reflexivity.
    + rewrite H; exact IH.
Qed.

Lemma word_spec w t : denote (word w t) = map bit w *> denote t.
Proof.
  induction w as [|b w IH]; [reflexivity|].
  change (denote (push b n1 (word w t)) = bit b >> (map bit w *> denote t)).
  rewrite push_spec, IH; reflexivity.
Qed.

Definition phase (b:bool) : Q := if b then C else B.
Fixpoint left (acc:list (option BigUint)) : side := match acc with
  | [] => 0inf <* <[1]
  | Some n::r => left r <* <[1]^^(BigUint.to_nat n)
  | None::r => left r <* <[1;0;1]
  end.

Lemma EOnes n l r :
  l {{E}}> [1]^^n *> r -->* l <* <[1]^^n {{E}}> r.
Proof. es. Qed.
Lemma RetOnes b n l r :
  l <* <[1]^^n <{{phase b}} r -->* l <{{phase b}} [bit b]^^n *> r.
Proof. destruct b; cbn [phase bit]; es. Qed.
Lemma E001 l r : l {{E}}> [0;0;1] *> r -->* l <* <[1;0;1] {{E}}> r.
Proof. es. Qed.
Lemma Ret001 b l r : l <* <[1;0;1] <{{phase b}} r -->*
  l <{{phase (negb b)}} (if b then [0;1;1] else [1;1;0]) *> r.
Proof. destruct b; cbn [phase negb]; es. Qed.
Lemma Exit b r : 0inf <* <[1] <{{phase b}} r -->*
  0inf <{{C}} (if b then [1] else [1;0]) *> r.
Proof. destruct b; cbn [phase]; es. Qed.

Lemma back_spec acc b t : halts tm (config (back acc b t)) ->
  halts tm (left acc <{{phase b}} denote t).
Proof.
  revert b t; induction acc as [|[n|] acc IH]; intros b t H.
  - unfold config in H; cbn [back] in H; rewrite word_spec in H.
    eapply halts_evstep; [exact H|destruct b; apply Exit].
  - apply IH in H; rewrite push_spec in H.
    eapply halts_evstep; [exact H|apply RetOnes].
  - apply IH in H; rewrite word_spec in H.
    eapply halts_evstep; [exact H|destruct b; apply Ret001].
Qed.

Lemma E011 l r : l {{E}}> [0;1;1] *> r -->* l <{{B}} [0;0;1] *> r.
Proof. es. Qed.
Lemma E0000 l r : l {{E}}> [0;0;0;0] *> r -->* l <{{B}} [0;1;1;1] *> r.
Proof. es. Qed.
Lemma E0001 l r : l {{E}}> [0;0;0;1] *> r -->* l <{{C}} [1;1;0;0] *> r.
Proof. es. Qed.
Lemma E010 l r : halts tm (l {{E}}> [0;1;0] *> r).
Proof. esx. Qed.

(* A failed budget check makes no claim.  Every true result is actual halt. *)
Definition answer c (s:result) : Prop := match s with
  | inl t => halts tm (config t) -> halts tm c
  | inr b => b=true -> halts tm c
  end.
Lemma answer_step c c' s : c -->* c' -> answer c' s -> answer c s.
Proof.
  destruct s; cbn [answer]; intros H K J.
  all: eapply halts_evstep; [apply K,J|exact H].
Qed.

Lemma scan_zero_spec next :
  (forall t acc, answer (left acc {{E}}> denote t) (next t acc)) ->
  forall t acc, answer (left acc {{E}}> denote t) (scan_zero next t acc).
Proof.
  intros IH t acc; unfold scan_zero.
  pose proof (pop_spec t) as H1; destruct (pop t) as [a t1].
  pose proof (pop_spec t1) as H2; destruct (pop t1) as [b t2].
  pose proof (pop_spec t2) as H3; destruct (pop t2) as [c t3].
  rewrite H1,H2,H3; destruct a; [cbn [answer]; discriminate|].
  destruct b,c; cbn [bit answer].
  - intro H; apply back_spec in H; rewrite word_spec in H.
    eapply halts_evstep; [exact H|apply E011].
  - intros _; apply E010.
  - eapply answer_step; [apply E001|apply IH].
  - pose proof (pop_spec t3) as H4; destruct (pop t3) as [d t4].
    rewrite H4; destruct d; cbn [bit answer]; intro H;
      apply back_spec in H; rewrite word_spec in H;
      eapply halts_evstep; [exact H|apply E0001|exact H|apply E0000].
Qed.

Lemma scan_spec fuel t acc :
  answer (left acc {{E}}> denote t) (scan fuel t acc).
Proof.
  revert t acc; induction fuel as [|fuel IH]; intros t acc.
  - cbn [scan answer]; discriminate.
  - destruct t as [|[b n] r].
    + apply scan_zero_spec, IH.
    + destruct b.
      * cbn [scan denote bit]; eapply answer_step; [apply EOnes|apply IH].
      * apply scan_zero_spec, IH.
Qed.

Lemma sweep_spec t : answer (config t) (sweep t).
Proof.
  unfold sweep; eapply answer_step with (c':=left [] {{E}}> denote t).
  - cbn [left]; unfold config; es.
  - apply scan_spec.
Qed.

Definition S a b r := 0inf <{{C}} [1]^^a *> [0;0;1;1] *> [0]^^b *> r.
Lemma Inc1 a b r : S a (4+b) r -->* S (6+a) b r.
Proof. esx. Qed.
Lemma Incs a b n r : S a (4*n+b) r -->* S (a+6*n) b r.
Proof.
  induction n as [|n IH] in a |- *.
  - rewrite !Nat.mul_0_r, Nat.add_0_r; apply evstep_refl.
  - replace (4*Datatypes.S n+b) with (4+(4*n+b)) by lia.
    follow Inc1; applys_eq (IH (6+a)); flia.
Qed.

Lemma mul6_spec q :
  BigUint.to_nat (BigUint.mulc q (Uint63.of_Z 6%Z)) = 6*BigUint.to_nat q.
Proof.
  unfold BigUint.to_nat; rewrite mulc_spec by reflexivity.
  change (Z.to_nat (toZ q * 6) = 6*Z.to_nat (toZ q)).
  pose proof (toZ_ge0 q); lia.
Qed.
Lemma div4_spec b q rem : divmodc b (Uint63.of_Z 4%Z)=(q,rem) ->
  BigUint.to_nat b = 4*BigUint.to_nat q + BigUint.to_nat (Cons_simpl rem BigUintNil).
Proof.
  intro H; enough (divmod_small b n4 = Some (q,Cons_simpl rem BigUintNil)) as K.
  - apply inj_divmod_small in K; exact (proj1 K).
  - change ((let '(q,r) := divmodc b (Uint63.of_Z 4%Z) in
      Some (q,Cons_simpl r BigUintNil)) = Some (q,Cons_simpl rem BigUintNil)).
    rewrite H; reflexivity.
Qed.

Lemma batch_spec a b r q rem : divmodc b (Uint63.of_Z 4%Z)=(q,rem) ->
  config ((true,a)::(false,n2)::(true,n2)::(false,b)::r) -->*
  config (push true (BigUint.add a (BigUint.mulc q (Uint63.of_Z 6%Z)))
    (push false n2 (push true n2 (push false (Cons_simpl rem BigUintNil) r)))).
Proof.
  intro H; unfold config; rewrite !push_spec.
  change (S (BigUint.to_nat a) (BigUint.to_nat b) (denote r) -->*
    S (BigUint.to_nat (BigUint.add a (BigUint.mulc q (Uint63.of_Z 6%Z))))
      (BigUint.to_nat (Cons_simpl rem BigUintNil)) (denote r)).
  rewrite inj_add, mul6_spec, (div4_spec _ _ _ H); apply Incs.
Qed.

Lemma step_spec t : answer (config t) (step t).
Proof.
  unfold step.
  (* Choose fallback branches explicitly: speculative [apply sweep_spec]
     on an unmatched branch can unfold the scanner during unification. *)
  destruct t as [|[ba a] t]; [apply sweep_spec|].
  destruct ba; [|apply sweep_spec].
  destruct t as [|[bz z] t]; [apply sweep_spec|].
  destruct bz; [apply sweep_spec|].
  destruct t as [|[bt two] t]; [apply sweep_spec|].
  destruct bt; [|apply sweep_spec].
  destruct t as [|[bb b] r]; [apply sweep_spec|].
  destruct bb; [apply sweep_spec|].
  destruct (BigUint.eqb_spec z n2); [subst z|apply sweep_spec].
  destruct (BigUint.eqb_spec two n2); [subst two|apply sweep_spec].
  destruct (divmodc b (Uint63.of_Z 4%Z)) as [q rem] eqn:H.
  destruct (is0 q); [apply sweep_spec|].
  cbn [answer]; intro K; eapply halts_evstep; [exact K|apply batch_spec,H].
Qed.

Lemma run_spec fuel : answer (config seed) (run fuel).
Proof.
  unfold run, answer; apply N_iter_until_spec.
  - intros t H; pose proof (step_spec t) as K.
    destruct (step t); cbn [answer] in K; intro J; apply H,K,J.
  - trivial.
Qed.

Lemma init : c0 -->* config seed.
Proof. unfold config, seed; cbn [denote bit]; esx. Qed.

Lemma check_spec fuel : check fuel=true -> halts tm c0.
Proof.
  unfold check; pose proof (run_spec fuel) as H.
  destruct (run fuel); [discriminate|].
  intro K; eapply halts_evstep; [apply H,K|apply init].
Qed.

Theorem halt : halts tm c0.
Proof. apply (check_spec 700000%N). native_check_eq. Time Qed.

End Bell60.
