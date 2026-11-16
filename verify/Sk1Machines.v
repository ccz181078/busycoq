(* Sk1 Class1: TM17 nonhalts; TM91, TM94, TM104, TM105 halt.
   Self-contained except for BusyCoq and the Coq standard library. *)
From BusyCoq Require Import Individual62 Helper LongitudinalHalt Eqb FastRev.
Require Import ZifyNat Lia NArith PeanoNat String List.
Import BusyCoq.Eqb.
Open Scope sym_scope.

Module Sk1Counter.
Definition W : list Sym := [1;1;1;1;0;1;1;1;1;1].
Inductive digit := D0 | D1 | D2 | D3 | D4 | D5.
Definition word p : list Sym :=
  match p with
  | D0 => [0;1] | D1 => [1;1;1;1]
  | D2 => [0;1;1;1;1;1] | D3 => [1;1;1;1;1;1;1;1]
  | D4 => [0;1;1;1;1;1;1;1;1;1]
  | D5 => [1;1;1;1;1;1;1;1;1;1;1;1]
  end.

Definition next p := match p with
  | D0=>D1 | D1=>D2 | D2=>D3 | D3=>D4 | D4=>D5 | D5=>D0 end.
Definition take p : nat := match p with D1 | D3=>1 | _=>0 end.
Definition give p : nat := match p with D1 | D3 | D5=>1 | _=>0 end.
Definition carry p : nat := match p with D5=>1 | _=>0 end.

(* The batch rule deliberately requires all consumed W to be initially
   available. Right-neighbour gifts are retained, but not anticipated. *)
Section Counter.
Variable tm : TM.
Variable h : list (DH0*DH0).
Hypothesis wall : forall n, segRLs tm h h (W^^n) (W^^n).
Hypothesis one : forall p n,
  segRLs tm h (h^^carry p) (word p ++ W^^(take p+n))
    (W^^give p ++ word (next p) ++ W^^n).

Lemma walls t n : segRLs tm (h^^t) (h^^t) (W^^n) (W^^n).
Proof. apply segRLs_wall'', wall. Qed.

Lemma prefix_rule t u a p b q c :
  segRLs tm (h^^t) (h^^u) (word p ++ W^^b) (W^^a ++ word q ++ W^^c) ->
  forall k, segRLs tm (h^^t) (h^^u)
    (W^^k ++ word p ++ W^^b) (W^^(k+a) ++ word q ++ W^^c).
Proof.
  intros H k. rewrite lpow_add, <-app_assoc.
  eapply segRLs_concat; [apply walls|exact H].
Qed.

Record effect := Eff { phase : digit; used : nat; given : nat; sent : nat }.
Fixpoint total (p:digit) (t:nat) : effect :=
  match t with
  | O => Eff p 0 0 0
  | S t => let a := total (next p) t in
      Eff (phase a) (take p+used a) (give p+given a) (carry p+sent a)
  end.

Lemma total_spec t p n :
  let a := total p t in
  segRLs tm (h^^t) (h^^sent a) (word p ++ W^^(used a+n))
    (W^^given a ++ word (phase a) ++ W^^n).
Proof.
  gen p n. induction t; intros p n; cbn [total phase used given sent].
  - constructor.
  - cbn [lpow]. rewrite <-Nat.add_assoc.
    rewrite (lpow_add _ (carry p)).
    eapply segRLs_trans.
    + apply one.
    + apply prefix_rule, IHt.
Qed.
End Counter.

Lemma total_add p t u :
  total p (t+u) =
  let a := total p t in let b := total (phase a) u in
  Eff (phase b) (used a+used b) (given a+given b) (sent a+sent b).
Proof.
  gen p. induction t; intros p; cbn [Nat.add total phase used given sent].
  - destruct (total p u); reflexivity.
  - rewrite IHt. cbn. f_equal; lia.
Qed.

Lemma total_six p : total p 6 = Eff p 2 3 1.
Proof. destruct p; reflexivity. Qed.

Lemma total_period p k r :
  total p (k*6+r) = let a := total p r in
    Eff (phase a) (k*2+used a) (k*3+given a) (k+sent a).
Proof.
  induction k; [cbn [Nat.mul Nat.add]; destruct (total p r); reflexivity|].
  replace (S k*6+r) with (6+(k*6+r)) by lia.
  rewrite total_add,total_six. cbn [phase used given sent].
  rewrite IHk. cbn. f_equal; lia.
Qed.

Record effectN := EffN { phaseN : digit; usedN : N; givenN : N; sentN : N }.
Definition denote_effect a :=
  Eff (phaseN a) (N.to_nat (usedN a)) (N.to_nat (givenN a)) (N.to_nat (sentN a)).
Definition totalN p t : effectN :=
  let k := (t/6)%N in
  let a := total p (N.to_nat (t mod 6)) in
  EffN (phase a) (k*2+N.of_nat (used a))
    (k*3+N.of_nat (given a)) (k+N.of_nat (sent a)).

Lemma totalN_spec p t : denote_effect (totalN p t) = total p (N.to_nat t).
Proof.
  unfold totalN,denote_effect; cbn [phaseN usedN givenN sentN].
  rewrite !N2Nat.inj_add, !N2Nat.inj_mul, !Nat2N.id.
  replace (N.to_nat t) with (N.to_nat (t/6)*6+N.to_nat (t mod 6)).
  - apply eq_sym, total_period.
  - pose proof (N.div_mod t 6 ltac:(lia)). nia.
Qed.

Definition cells := list (digit*N).
Fixpoint cell_word (xs:cells) : list Sym := match xs with
  | [] => []
  | (p,n)::xs => word p ++ W^^N.to_nat n ++ cell_word xs
  end.

Fixpoint batch (t:N) (xs:cells) : option (N*cells) :=
  match xs with
  | [] => if (t=?0)%N then Some (0%N,[]) else None
  | (p,n)::xs =>
    let a := totalN p t in
    if (usedN a<=?n)%N then
      match batch (sentN a) xs with
      | Some (e,ys) => Some (givenN a,(phaseN a,(n-usedN a+e)%N)::ys)
      | None => None
      end
    else None
  end.

Section BatchCorrect.
Variable tm : TM.
Variable h : list (DH0*DH0).
Hypothesis wall : forall n, segRLs tm h h (W^^n) (W^^n).
Hypothesis one : forall p n,
  segRLs tm h (h^^carry p) (word p ++ W^^(take p+n))
    (W^^give p ++ word (next p) ++ W^^n).

Lemma totalN_rule p t n :
  (usedN (totalN p t)<=n)%N ->
  segRLs tm (h^^N.to_nat t) (h^^N.to_nat (sentN (totalN p t)))
    (word p ++ W^^N.to_nat n)
    (W^^N.to_nat (givenN (totalN p t)) ++ word (phaseN (totalN p t)) ++
      W^^N.to_nat (n-usedN (totalN p t))).
Proof.
  intros H.
  pose proof (total_spec tm h wall one (N.to_nat t) p
    (N.to_nat (n-usedN (totalN p t)))) as I.
  rewrite <-totalN_spec in I. cbn [denote_effect phase used given sent] in I.
  applys_eq I; flia.
Qed.

Lemma batch_spec t xs e ys :
  batch t xs = Some (e,ys) ->
  segRLs tm (h^^N.to_nat t) [] (cell_word xs)
    (W^^N.to_nat e ++ cell_word ys).
Proof.
  gen t e ys. induction xs as [|[p n] xs IH]; intros t e ys H; cbn [batch] in H.
  - destruct (N.eqb_spec t 0); inverts H. subst t. constructor.
  - destruct (N.leb_spec (usedN (totalN p t)) n); try discriminate.
    destruct (batch (sentN (totalN p t)) xs) as [[e' ys']|] eqn:E; inverts H.
    specialize (IH _ _ _ E).
    pose proof (totalN_rule p t n H0) as I.
    change (segRLs tm (h^^N.to_nat t) [] (cell_word ((p,n)::xs))
      (W^^N.to_nat (givenN (totalN p t)) ++
       cell_word ((phaseN (totalN p t),(n-usedN (totalN p t)+e')%N)::ys'))).
    remember (totalN p t) as a in *.
    cbn [cell_word]. rewrite N2Nat.inj_add, lpow_add.
    repeat rewrite app_assoc.
    applys_eq (segRLs_concat I IH); repeat rewrite app_assoc; reflexivity.
Qed.
End BatchCorrect.

Record scan := Scan { scan_q : Q; scan_dir : dir;
  scan_in : list Sym; scan_out : list Sym; scan_context : list Sym }.
Definition scan_valid tm s := forall n l r,
  match scan_dir s with
  | R =>
    l <* (rev (scan_context s)) {{scan_q s}}> (scan_in s)^^n *> r -[tm]->*
    l <* (rev (scan_out s))^^n <* (rev (scan_context s)) {{scan_q s}}> r
  | L =>
    l <* (rev (scan_in s))^^n <{{scan_q s}} (scan_context s) *> r -[tm]->*
    l <{{scan_q s}} (scan_context s) *> (scan_out s)^^n *> r
  end.

Definition head q : list (DH0*DH0) := [((q,<[1;0;1]),(q,[1]))].
Definition start (q:Q) (r:side) := 0inf <* <[1;0;1] {{q}}> r.

Section RootCorrect.
Variable tm : TM.
Variable q : Q.
Hypothesis emit : forall r,
  0inf <{{q}} [1] *> r -[tm]->* start q r.

Lemma calls_spec t r r' : sideRLs tm ((head q)^^t) r r' ->
  start q r -[tm]->* start q r'.
Proof.
  gen r r'. induction t; intros r r' H; cbn [lpow head app] in H.
  - inverts H. constructor.
  - inverts H.
    match goal with
    | Hret : sideRL _ _ _ _ _ |- _ => follow100 Hret
    end.
    follow emit. apply IHt; assumption.
Qed.

Hypothesis wall : forall n, segRLs tm (head q) (head q) (W^^n) (W^^n).
Hypothesis one : forall p n,
  segRLs tm (head q) ((head q)^^carry p) (word p ++ W^^(take p+n))
    (W^^give p ++ word (next p) ++ W^^n).

Lemma batch_root t xs e ys k r : batch t xs=Some (e,ys) ->
  start q (W^^N.to_nat k *> cell_word xs *> r) -[tm]->*
  start q (W^^N.to_nat (k+e) *> cell_word ys *> r).
Proof.
  intros H. apply (calls_spec (N.to_nat t)).
  rewrite N2Nat.inj_add,lpow_add,Str_app_assoc.
  eapply segRLs_sideRLs_concat; [apply walls,wall|].
  pose proof (segRLs_sideRLs_concat
    (batch_spec tm (head q) wall one t xs e ys H) (sideRLseq_O tm r)) as I.
  rewrite Str_app_assoc in I. exact I.
Qed.
End RootCorrect.
End Sk1Counter.

Module Sk1Counter7.
Definition W : list Sym := [0;1;0;1;1;1].
Inductive digit := D0 | D1 | D2 | D3 | D4 | D5 | D6.
Definition word p : list Sym :=
  match p with
  | D0 => [0;1;0;1;0;1] | D1 => [1;1] | D2 => [0;1;1;1]
  | D3 => [0;1;0;1;0;1;1;1;0;1;1;1] | D4 => [1;1;1;1;0;1;1;1]
  | D5 => [0;1;0;1;0;1;1;1;1;1] | D6 => [1;1;1;1;1;1]
  end.
Definition next p := match p with
  | D0=>D1 | D1=>D2 | D2=>D3 | D3=>D4 | D4=>D5 | D5=>D6 | D6=>D0 end.
Definition take p : nat := match p with D1 | D2=>1 | _=>0 end.
Definition give p : nat := match p with D0 | D1 | D3 | D5=>1 | _=>0 end.
Definition carry p : nat := match p with D6=>1 | _=>0 end.

(* The batch rule deliberately requires all consumed W to be initially
   available. Right-neighbour gifts are retained, but not anticipated. *)
Section Counter.
Variable tm : TM.
Variable h : list (DH0*DH0).
Hypothesis wall : forall n, segRLs tm h h (W^^n) (W^^n).
Hypothesis one : forall p n,
  segRLs tm h (h^^carry p) (word p ++ W^^(take p+n))
    (W^^give p ++ word (next p) ++ W^^n).

Lemma walls t n : segRLs tm (h^^t) (h^^t) (W^^n) (W^^n).
Proof. apply segRLs_wall'', wall. Qed.

Lemma prefix_rule t u a p b q c :
  segRLs tm (h^^t) (h^^u) (word p ++ W^^b) (W^^a ++ word q ++ W^^c) ->
  forall k, segRLs tm (h^^t) (h^^u)
    (W^^k ++ word p ++ W^^b) (W^^(k+a) ++ word q ++ W^^c).
Proof.
  intros H k. rewrite lpow_add, <-app_assoc.
  eapply segRLs_concat; [apply walls|exact H].
Qed.

Record effect := Eff { phase : digit; used : nat; given : nat; sent : nat }.
Fixpoint total (p:digit) (t:nat) : effect :=
  match t with
  | O => Eff p 0 0 0
  | S t => let a := total (next p) t in
      Eff (phase a) (take p+used a) (give p+given a) (carry p+sent a)
  end.

Lemma total_spec t p n :
  let a := total p t in
  segRLs tm (h^^t) (h^^sent a) (word p ++ W^^(used a+n))
    (W^^given a ++ word (phase a) ++ W^^n).
Proof.
  gen p n. induction t; intros p n; cbn [total phase used given sent].
  - constructor.
  - cbn [lpow]. rewrite <-Nat.add_assoc.
    rewrite (lpow_add _ (carry p)).
    eapply segRLs_trans.
    + apply one.
    + apply prefix_rule, IHt.
Qed.
End Counter.

Lemma total_add p t u :
  total p (t+u) =
  let a := total p t in let b := total (phase a) u in
  Eff (phase b) (used a+used b) (given a+given b) (sent a+sent b).
Proof.
  gen p. induction t; intros p; cbn [Nat.add total phase used given sent].
  - destruct (total p u); reflexivity.
  - rewrite IHt. cbn. f_equal; lia.
Qed.

Lemma total_seven p : total p 7 = Eff p 2 4 1.
Proof. destruct p; reflexivity. Qed.

Lemma total_period p k r :
  total p (k*7+r) = let a := total p r in
    Eff (phase a) (k*2+used a) (k*4+given a) (k+sent a).
Proof.
  induction k; [cbn [Nat.mul Nat.add]; destruct (total p r); reflexivity|].
  replace (S k*7+r) with (7+(k*7+r)) by lia.
  rewrite total_add,total_seven. cbn [phase used given sent].
  rewrite IHk. cbn. f_equal; lia.
Qed.

Record effectN := EffN { phaseN : digit; usedN : N; givenN : N; sentN : N }.
Definition denote_effect a :=
  Eff (phaseN a) (N.to_nat (usedN a)) (N.to_nat (givenN a)) (N.to_nat (sentN a)).
Definition totalN p t : effectN :=
  let k := (t/7)%N in
  let a := total p (N.to_nat (t mod 7)) in
  EffN (phase a) (k*2+N.of_nat (used a))
    (k*4+N.of_nat (given a)) (k+N.of_nat (sent a)).

Lemma totalN_spec p t : denote_effect (totalN p t) = total p (N.to_nat t).
Proof.
  unfold totalN,denote_effect; cbn [phaseN usedN givenN sentN].
  rewrite !N2Nat.inj_add, !N2Nat.inj_mul, !Nat2N.id.
  replace (N.to_nat t) with (N.to_nat (t/7)*7+N.to_nat (t mod 7)).
  - apply eq_sym, total_period.
  - pose proof (N.div_mod t 7 ltac:(lia)). nia.
Qed.

Definition cells := list (digit*N).
Fixpoint cell_word (xs:cells) : list Sym := match xs with
  | [] => []
  | (p,n)::xs => word p ++ W^^N.to_nat n ++ cell_word xs
  end.

Fixpoint batch (t:N) (xs:cells) : option (N*cells) :=
  match xs with
  | [] => if (t=?0)%N then Some (0%N,[]) else None
  | (p,n)::xs =>
    let a := totalN p t in
    if (usedN a<=?n)%N then
      match batch (sentN a) xs with
      | Some (e,ys) => Some (givenN a,(phaseN a,(n-usedN a+e)%N)::ys)
      | None => None
      end
    else None
  end.

Section BatchCorrect.
Variable tm : TM.
Variable h : list (DH0*DH0).
Hypothesis wall : forall n, segRLs tm h h (W^^n) (W^^n).
Hypothesis one : forall p n,
  segRLs tm h (h^^carry p) (word p ++ W^^(take p+n))
    (W^^give p ++ word (next p) ++ W^^n).

Lemma totalN_rule p t n :
  (usedN (totalN p t)<=n)%N ->
  segRLs tm (h^^N.to_nat t) (h^^N.to_nat (sentN (totalN p t)))
    (word p ++ W^^N.to_nat n)
    (W^^N.to_nat (givenN (totalN p t)) ++ word (phaseN (totalN p t)) ++
      W^^N.to_nat (n-usedN (totalN p t))).
Proof.
  intros H.
  pose proof (total_spec tm h wall one (N.to_nat t) p
    (N.to_nat (n-usedN (totalN p t)))) as I.
  rewrite <-totalN_spec in I. cbn [denote_effect phase used given sent] in I.
  applys_eq I; flia.
Qed.

Lemma batch_spec t xs e ys :
  batch t xs = Some (e,ys) ->
  segRLs tm (h^^N.to_nat t) [] (cell_word xs)
    (W^^N.to_nat e ++ cell_word ys).
Proof.
  gen t e ys. induction xs as [|[p n] xs IH]; intros t e ys H; cbn [batch] in H.
  - destruct (N.eqb_spec t 0); inverts H. subst t. constructor.
  - destruct (N.leb_spec (usedN (totalN p t)) n); try discriminate.
    destruct (batch (sentN (totalN p t)) xs) as [[e' ys']|] eqn:E; inverts H.
    specialize (IH _ _ _ E).
    pose proof (totalN_rule p t n H0) as I.
    change (segRLs tm (h^^N.to_nat t) [] (cell_word ((p,n)::xs))
      (W^^N.to_nat (givenN (totalN p t)) ++
       cell_word ((phaseN (totalN p t),(n-usedN (totalN p t)+e')%N)::ys'))).
    remember (totalN p t) as a in *.
    cbn [cell_word]. rewrite N2Nat.inj_add, lpow_add.
    repeat rewrite app_assoc.
    applys_eq (segRLs_concat I IH); repeat rewrite app_assoc; reflexivity.
Qed.
End BatchCorrect.
End Sk1Counter7.

Module Sk1CounterMixed.
(* Finite cycles may have different lengths, consumptions and carry counts,
   including zero carries. Their shared head permits horizontal composition. *)
Section Mixed.
Variable digit : Type.
Variable W : list Sym.
Variable word : digit -> list Sym.
Variable next : digit -> digit.
Variable take give carry : digit -> nat.

Section Counter.
Variable tm : TM.
Variable h : list (DH0*DH0).
Hypothesis wall : forall n, segRLs tm h h (W^^n) (W^^n).
Hypothesis one : forall p n,
  segRLs tm h (h^^carry p) (word p ++ W^^(take p+n))
    (W^^give p ++ word (next p) ++ W^^n).

Lemma walls t n : segRLs tm (h^^t) (h^^t) (W^^n) (W^^n).
Proof. apply segRLs_wall'', wall. Qed.

Lemma prefix_rule t u a p b q c :
  segRLs tm (h^^t) (h^^u) (word p ++ W^^b) (W^^a ++ word q ++ W^^c) ->
  forall k, segRLs tm (h^^t) (h^^u)
    (W^^k ++ word p ++ W^^b) (W^^(k+a) ++ word q ++ W^^c).
Proof.
  intros H k. rewrite lpow_add, <-app_assoc.
  eapply segRLs_concat; [apply walls|exact H].
Qed.

Record effect := Eff { phase : digit; used : nat; given : nat; sent : nat }.
Fixpoint total (p:digit) (t:nat) : effect :=
  match t with
  | O => Eff p 0 0 0
  | S t => let a := total (next p) t in
      Eff (phase a) (take p+used a) (give p+given a) (carry p+sent a)
  end.

Lemma total_spec t p n :
  let a := total p t in
  segRLs tm (h^^t) (h^^sent a) (word p ++ W^^(used a+n))
    (W^^given a ++ word (phase a) ++ W^^n).
Proof.
  gen p n. induction t; intros p n; cbn [total phase used given sent].
  - constructor.
  - cbn [lpow]. rewrite <-Nat.add_assoc.
    rewrite (lpow_add _ (carry p)).
    eapply segRLs_trans.
    + apply one.
    + apply prefix_rule, IHt.
Qed.
End Counter.

Lemma total_add p t u :
  total p (t+u) =
  let a := total p t in let b := total (phase a) u in
  Eff (phase b) (used a+used b) (given a+given b) (sent a+sent b).
Proof.
  gen p. induction t; intros p; cbn [Nat.add total phase used given sent].
  - destruct (total p u); reflexivity.
  - rewrite IHt. cbn. f_equal; lia.
Qed.

Variable period cycle_used cycle_given cycle_sent : digit -> nat.
Hypothesis period_positive : forall p, 0<period p.
Hypothesis cycle_ok : forall p,
  total p (period p) = Eff p (cycle_used p) (cycle_given p) (cycle_sent p).

Lemma total_period p k r :
  total p (k*period p+r) = let a := total p r in
    Eff (phase a) (k*cycle_used p+used a)
      (k*cycle_given p+given a) (k*cycle_sent p+sent a).
Proof.
  induction k; [cbn [Nat.mul Nat.add]; destruct (total p r); reflexivity|].
  replace (S k*period p+r) with (period p+(k*period p+r)) by lia.
  rewrite total_add,cycle_ok. cbn [phase used given sent].
  rewrite IHk. cbn. f_equal; lia.
Qed.

Record effectN := EffN { phaseN : digit; usedN : N; givenN : N; sentN : N }.
Definition denote_effect a :=
  Eff (phaseN a) (N.to_nat (usedN a)) (N.to_nat (givenN a)) (N.to_nat (sentN a)).
Definition totalN p t : effectN :=
  let b := N.of_nat (period p) in let k := (t/b)%N in
  let a := total p (N.to_nat (t mod b)) in
  EffN (phase a) (N.of_nat(cycle_used p)*k+N.of_nat (used a))
    (N.of_nat(cycle_given p)*k+N.of_nat (given a))
    (N.of_nat(cycle_sent p)*k+N.of_nat (sent a)).

Lemma totalN_spec p t : denote_effect (totalN p t) = total p (N.to_nat t).
Proof.
  unfold totalN,denote_effect; cbn [phaseN usedN givenN sentN].
  rewrite !N2Nat.inj_add, !N2Nat.inj_mul, !Nat2N.id.
  replace (N.to_nat t) with
    (N.to_nat(t/N.of_nat(period p))*period p+N.to_nat(t mod N.of_nat(period p))).
  - rewrite total_period. destruct(total p (N.to_nat(t mod N.of_nat(period p)))).
    cbn. f_equal; lia.
  - pose proof(period_positive p).
    pose proof(N.div_mod t (N.of_nat(period p)) ltac:(lia)). nia.
Qed.

Definition cells := list (digit*N).
Fixpoint cell_word (xs:cells) : list Sym := match xs with
  | [] => []
  | (p,n)::xs => word p ++ W^^N.to_nat n ++ cell_word xs
  end.

Fixpoint batch (t:N) (xs:cells) : option (N*cells) :=
  match xs with
  | [] => if (t=?0)%N then Some (0%N,[]) else None
  | (p,n)::xs =>
    let a := totalN p t in
    if (usedN a<=?n)%N then
      match batch (sentN a) xs with
      | Some (e,ys) => Some (givenN a,(phaseN a,(n-usedN a+e)%N)::ys)
      | None => None
      end
    else None
  end.

Section BatchCorrect.
Variable tm : TM.
Variable h : list (DH0*DH0).
Hypothesis wall : forall n, segRLs tm h h (W^^n) (W^^n).
Hypothesis one : forall p n,
  segRLs tm h (h^^carry p) (word p ++ W^^(take p+n))
    (W^^give p ++ word (next p) ++ W^^n).

Lemma totalN_rule p t n :
  (usedN (totalN p t)<=n)%N ->
  segRLs tm (h^^N.to_nat t) (h^^N.to_nat (sentN (totalN p t)))
    (word p ++ W^^N.to_nat n)
    (W^^N.to_nat (givenN (totalN p t)) ++ word (phaseN (totalN p t)) ++
      W^^N.to_nat (n-usedN (totalN p t))).
Proof.
  intros H.
  pose proof (total_spec tm h wall one (N.to_nat t) p
    (N.to_nat (n-usedN (totalN p t)))) as I.
  rewrite <-totalN_spec in I. cbn [denote_effect phase used given sent] in I.
  applys_eq I; flia.
Qed.

Lemma batch_spec t xs e ys :
  batch t xs = Some (e,ys) ->
  segRLs tm (h^^N.to_nat t) [] (cell_word xs)
    (W^^N.to_nat e ++ cell_word ys).
Proof.
  gen t e ys. induction xs as [|[p n] xs IH]; intros t e ys H; cbn [batch] in H.
  - destruct (N.eqb_spec t 0); inverts H. subst t. constructor.
  - destruct (N.leb_spec (usedN (totalN p t)) n); try discriminate.
    destruct (batch (sentN (totalN p t)) xs) as [[e' ys']|] eqn:E; inverts H.
    specialize (IH _ _ _ E).
    pose proof (totalN_rule p t n H0) as I.
    change (segRLs tm (h^^N.to_nat t) [] (cell_word ((p,n)::xs))
      (W^^N.to_nat (givenN (totalN p t)) ++
       cell_word ((phaseN (totalN p t),(n-usedN (totalN p t)+e')%N)::ys'))).
    remember (totalN p t) as a in *.
    cbn [cell_word]. rewrite N2Nat.inj_add, lpow_add.
    repeat rewrite app_assoc.
    applys_eq (segRLs_concat I IH); repeat rewrite app_assoc; reflexivity.
Qed.
End BatchCorrect.

End Mixed.
End Sk1CounterMixed.

Module Sk1Tape.
(* Both stacks are stored near-to-far. Repeated words never expand during
   computation; the nat expansion below is only the specification. *)
Module Runs.
Lemma nil_power {A} n : (@nil A)^^n = [].
Proof. induction n; cbn; assumption || reflexivity. Qed.
Definition t := list (list Sym*N).
Fixpoint denote (xs:t) : side := match xs with
  | [] => 0inf
  | (w,n)::xs => w^^N.to_nat n *> denote xs
  end.

Definition push (w:list Sym) (n:N) (xs:t) : t :=
  match w,n with
  | [],_ | _,N0 => xs
  | _,_ => match xs with
    | (v,m)::ys => if eqb w v then (w,(n+m)%N)::ys else (w,n)::xs
    | [] => [(w,n)] end
  end.

Lemma push_spec w n xs : denote (push w n xs) = w^^N.to_nat n *> denote xs.
Proof.
  destruct w as [|b w].
  - cbn [push]. rewrite nil_power. reflexivity.
  - destruct n as [|n]; [reflexivity|].
    destruct xs as [|[v m] xs]; cbn [push denote]; [reflexivity|].
    destruct (eqb_spec (b::w) v); subst; cbn [denote]; [|reflexivity].
    rewrite N2Nat.inj_add,lpow_add,Str_app_assoc. reflexivity.
Qed.

Fixpoint pop (xs:t) : Sym*t := match xs with
  | [] => (0,[])
  | ([],_)::xs | (_,N0)::xs => pop xs
  | ((b::w),Npos n)::xs =>
    (b,push w 1 (push (b::w) (N.pred (Npos n)) xs))
  end.

Lemma pop_spec xs : denote xs = fst (pop xs) >> denote (snd (pop xs)).
Proof.
  induction xs as [|[[|b w] [|n]] xs IH]; cbn [pop denote].
  - apply const_unfold.
  - exact IH.
  - rewrite nil_power. exact IH.
  - exact IH.
  - cbn [fst snd]. rewrite !push_spec. change (N.to_nat 1) with 1%nat. cbn [lpow app Str_app].
    replace (N.to_nat (Npos n)) with (1+N.to_nat (N.pred (Npos n))) by lia.
    cbn [Nat.add lpow app Str_app]. rewrite app_nil_r,Str_app_assoc. reflexivity.
Qed.

Fixpoint remove (w:list Sym) (xs:t) : option t := match w with
  | [] => Some xs
  | b::w => let '(c,ys) := pop xs in
    if eqb b c then remove w ys else None
  end.

Lemma remove_spec w xs ys : remove w xs=Some ys -> denote xs=w *> denote ys.
Proof.
  gen xs. induction w; intros xs H; cbn [remove] in H.
  - inverts H. reflexivity.
  - pose proof (pop_spec xs) as E. destruct (pop xs) as [b zs]; cbn in E.
    destruct (eqb_spec a b); try discriminate. subst.
    rewrite E,(IHw _ H). reflexivity.
Qed.

Lemma commute_power (x v w:list Sym) a b k :
  x++v^^a=w^^b++x -> x++v^^(k*a)=w^^(k*b)++x.
Proof.
  intros H. induction k.
  - cbn. rewrite !app_nil_r. reflexivity.
  - cbn [Nat.mul]. rewrite !lpow_add,app_assoc,H,<-app_assoc,IHk,app_assoc.
    reflexivity.
Qed.

(* Check one short periodic identity, then move an arbitrary number of
   groups. This also handles rotated and differently sized RLE words. *)
Definition skip_block w limit x v m ys : option (N*t) :=
  let a := N.of_nat (length w) in let b := N.of_nat (length v) in
  let k := N.min (limit/b) (m/a) in
  if (0<?k)%N then
  if (k*b<=?limit)%N then if (k*a<=?m)%N then
  if eqb (x++v^^length w) (w^^length v++x) then
    Some ((k*b)%N,push x 1 (push v (m-k*a) ys))
  else None else None else None else None.

Lemma skip_block_spec w limit x v m ys n zs :
  skip_block w limit x v m ys=Some (n,zs) ->
  (n<=limit)%N /\ x *> v^^N.to_nat m *> denote ys = w^^N.to_nat n *> denote zs.
Proof.
  unfold skip_block.
  generalize (N.min (limit/N.of_nat (length v)) (m/N.of_nat (length w))) as k.
  intros k H. destruct (N.ltb_spec 0 k); try discriminate.
  destruct (N.leb_spec (k*N.of_nat (length v)) limit); try discriminate.
  destruct (N.leb_spec (k*N.of_nat (length w)) m); try discriminate.
  destruct (eqb_spec (x++v^^length w) (w^^length v++x)); inverts H.
  split; [assumption|]. rewrite !push_spec.
  change (N.to_nat 1) with 1%nat. cbn [lpow]. rewrite app_nil_r.
  rewrite N2Nat.inj_mul,Nat2N.id.
  replace (N.to_nat m) with
    (N.to_nat k*length w+N.to_nat (m-k*N.of_nat (length w))) by lia.
  rewrite lpow_add,!Str_app_assoc.
  rewrite <-Str_app_assoc,(commute_power x v w _ _ _ e),!Str_app_assoc.
  reflexivity.
Qed.

Definition skip_periodic w n xs := match xs with
  | (x,Npos xH)::(v,m)::ys => skip_block w n x v m ys
  | (v,m)::ys => skip_block w n [] v m ys
  | [] => None end.

Lemma skip_periodic_spec w n xs k ys : skip_periodic w n xs=Some (k,ys) ->
  (k<=n)%N /\ denote xs=w^^N.to_nat k *> denote ys.
Proof.
  unfold skip_periodic. destruct xs as [|[x [|[p|p|]]] xs]; try discriminate;
    try (apply skip_block_spec).
  destruct xs as [|[v m] xs]; [apply skip_block_spec|].
  cbn [denote]. change (N.to_nat 1) with 1%nat.
  cbn [lpow]. rewrite app_nil_r. apply skip_block_spec.
Qed.

(* The common aligned case needs no division or periodic-word comparison. *)
Definition skip w n xs := match xs with
  | (v,m)::ys=>if eqb w v then
      let k:=N.min n m in Some(k,push v (m-k) ys)
    else skip_periodic w n xs
  | []=>None end.
Lemma skip_spec w n xs k ys : skip w n xs=Some(k,ys) ->
  (k<=n)%N /\ denote xs=w^^N.to_nat k *> denote ys.
Proof.
  destruct xs as [|[v m] xs]; cbn [skip]; [discriminate|].
  destruct(eqb_spec w v); subst; [|apply skip_periodic_spec].
  intros H; inverts H. split; [apply N.le_min_l|].
  cbn [denote]. rewrite push_spec,<-Str_app_assoc,<-lpow_add.
  f_equal; f_equal; lia.
Qed.

Fixpoint remove_fast fuel w n xs : option t :=
  if (n=?0)%N then Some xs else match fuel with
  | O => None
  | S fuel => match skip w n xs with
    | Some (k,ys) => remove_fast fuel w (n-k)%N ys
    | None => match remove w xs with
      | Some ys => remove_fast fuel w (N.pred n) ys
      | None => None end
    end
  end.

Lemma remove_fast_spec fuel w n xs ys : remove_fast fuel w n xs=Some ys ->
  denote xs=w^^N.to_nat n *> denote ys.
Proof.
  gen n xs ys. induction fuel; intros n xs ys H; cbn [remove_fast] in H;
    destruct (N.eqb_spec n 0); try discriminate; subst; try solve [inverts H; reflexivity].
  destruct (skip w n xs) as [[k zs]|] eqn:E.
  - destruct (skip_spec _ _ _ _ _ E) as [Hk E1].
    rewrite E1,(IHfuel _ _ _ H),<-Str_app_assoc,<-lpow_add.
    f_equal; f_equal; lia.
  - destruct (remove w xs) as [zs|] eqn:E1; try discriminate.
    rewrite (remove_spec _ _ _ E1),(IHfuel _ _ _ H).
    replace (N.to_nat n) with (1+N.to_nat (N.pred n)) by lia.
    cbn [Nat.add lpow]. rewrite Str_app_assoc. reflexivity.
Qed.

Fixpoint size (xs:t) : N := match xs with
  | []=>0%N | (w,n)::xs=>(N.of_nat (length w)*n+size xs)%N end.

End Runs.

Module RunMachine.
Record config := Cfg { left : Runs.t; right : Runs.t; state : Q; direction : dir }.
Definition denote c := match direction c with
  | L => Runs.denote (left c) <{{state c}} Runs.denote (right c)
  | R => Runs.denote (left c) {{state c}}> Runs.denote (right c)
  end.

Definition raw tm c : option config :=
  let '(b,l,r) := match direction c with
    | L => let '(b,l) := Runs.pop (left c) in (b,l,right c)
    | R => let '(b,r) := Runs.pop (right c) in (b,left c,r)
    end in
  match tm (state c,b) with
  | None => None
  | Some (b',L,q) => Some (Cfg l (Runs.push [b'] 1 r) q L)
  | Some (b',R,q) => Some (Cfg (Runs.push [b'] 1 l) r q R)
  end.

Lemma raw_spec tm c : match raw tm c with
  | None => halted tm (denote c)
  | Some c' => denote c -[tm]-> denote c'
  end.
Proof.
  destruct c as [l r q []]; unfold raw; cbn [left right state direction denote].
  - pose proof (Runs.pop_spec l) as H. destruct (Runs.pop l) as [b l']; cbn in H.
    rewrite H. destruct (tm (q,b)) as [[[b' []] q']|] eqn:E;
      cbn [denote left right state direction]; try rewrite Runs.push_spec;
      cbn [N.to_nat Pos.to_nat lpow app Str_app];
      first [solve [unfold halted; cbn; exact E] | solve [econstructor; exact E]].
  - pose proof (Runs.pop_spec r) as H. destruct (Runs.pop r) as [b r']; cbn in H.
    rewrite H. destruct (tm (q,b)) as [[[b' []] q']|] eqn:E;
      cbn [denote left right state direction]; try rewrite Runs.push_spec;
      cbn [N.to_nat Pos.to_nat lpow app Str_app];
      first [solve [unfold halted; cbn; exact E] | solve [econstructor; exact E]].
Qed.
End RunMachine.
End Sk1Tape.

Module Sk1Check.
Import Sk1Tape Sk1Counter.
Module RT := Runs.
Module RM := RunMachine.
Import RM.
Local Opaque RT.remove_fast RT.remove RT.push.

Definition orient d c := match d,direction c with
  | L,R => let '(b,r) := RT.pop (right c) in
      Cfg (RT.push [b] 1 (left c)) r (state c) L
  | R,L => let '(b,l) := RT.pop (left c) in
      Cfg l (RT.push [b] 1 (right c)) (state c) R
  | _,_ => c end.

Lemma orient_spec d c : denote (orient d c)=denote c.
Proof.
  destruct c as [l r q []],d; unfold orient; cbn [left right state direction]; try reflexivity.
  - pose proof (RT.pop_spec l) as H. destruct (RT.pop l) as [b l']; cbn in H.
    cbn [denote left right state direction]. rewrite RT.push_spec,H. reflexivity.
  - pose proof (RT.pop_spec r) as H. destruct (RT.pop r) as [b r']; cbn in H.
    cbn [denote left right state direction]. rewrite RT.push_spec,H. reflexivity.
Qed.
Lemma orient_direction d c : direction (orient d c)=d.
Proof. destruct c as [l r q []],d; cbn [orient direction left right state]; try reflexivity;
  first [solve [destruct (RT.pop l); reflexivity] | solve [destruct (RT.pop r); reflexivity]]. Qed.
Lemma orient_state d c : state (orient d c)=state c.
Proof. destruct c as [l r q []],d; cbn [orient direction left right state]; try reflexivity;
  first [solve [destruct (RT.pop l); reflexivity] | solve [destruct (RT.pop r); reflexivity]]. Qed.

(* 32 is only a matching-work budget. Exhaustion rejects the certificate. *)
Definition remove_run := RT.remove_fast 32.

Definition scan_stacks s n l r : option (RT.t*RT.t) :=
  match scan_dir s with
  | L => match RT.remove (scan_context s) r,
                 remove_run (fast_rev (scan_in s)) n l with
    | Some r,Some l => Some (l,RT.push (scan_context s) 1 (RT.push (scan_out s) n r))
    | _,_ => None end
  | R => match RT.remove (fast_rev (scan_context s)) l,
                 remove_run (scan_in s) n r with
    | Some l,Some r => Some (RT.push (fast_rev (scan_context s)) 1
        (RT.push (fast_rev (scan_out s)) n l),r)
    | _,_ => None end
  end.

Lemma scan_stacks_spec tm s n l r l' r' : scan_valid tm s ->
  scan_stacks s n l r=Some (l',r') ->
  denote (Cfg l r (scan_q s) (scan_dir s)) -[tm]->*
  denote (Cfg l' r' (scan_q s) (scan_dir s)).
Proof.
  destruct s as [q d w v x]. unfold scan_valid,scan_stacks,remove_run.
  destruct d; cbn [scan_q scan_dir scan_in scan_out scan_context]; intros H E.
  - destruct (RT.remove x r) as [r0|] eqn:Er; try discriminate.
    destruct (RT.remove_fast 32 (fast_rev w) n l) as [l0|] eqn:El; inverts E.
    cbn [denote left right state direction].
    rewrite !RT.push_spec,(RT.remove_spec _ _ _ Er),(RT.remove_fast_spec _ _ _ _ _ El).
    rewrite fast_rev_spec. change (N.to_nat 1) with 1%nat.
    cbn [lpow]. rewrite app_nil_r. apply H.
  - destruct (RT.remove (fast_rev x) l) as [l0|] eqn:El; try discriminate.
    destruct (RT.remove_fast 32 w n r) as [r0|] eqn:Er; inverts E.
    cbn [denote left right state direction].
    rewrite !RT.push_spec,(RT.remove_spec _ _ _ El),(RT.remove_fast_spec _ _ _ _ _ Er).
    rewrite !fast_rev_spec. change (N.to_nat 1) with 1%nat.
    cbn [lpow]. rewrite app_nil_r. apply H.
Qed.

Definition use_scan s n c : option config :=
  if eqb (state c) (scan_q s) then
    let c := orient (scan_dir s) c in
    match scan_stacks s n (left c) (right c) with
    | Some (l,r) => Some (Cfg l r (scan_q s) (scan_dir s))
    | None => None end
  else None.

Lemma use_scan_spec tm s n c c' : scan_valid tm s -> use_scan s n c=Some c' ->
  denote c -[tm]->* denote c'.
Proof.
  intros H. unfold use_scan. destruct (eqb_spec (state c) (scan_q s)); try discriminate.
  pose proof (orient_direction (scan_dir s) c) as Hd.
  pose proof (orient_state (scan_dir s) c) as Hq.
  rewrite <-(orient_spec (scan_dir s) c).
  remember (orient (scan_dir s) c) as z.
  destruct z as [l r q d]; cbn [left right state direction] in *; subst.
  destruct (scan_stacks s n l r) as [[l' r']|] eqn:E; intros Hc; inverts Hc.
  rewrite e. eapply scan_stacks_spec; eauto.
Qed.

Fixpoint zeros (xs:RT.t) := match xs with
  | [] => true
  | (w,_)::xs => if forallb (fun b=>eqb b 0) w then zeros xs else false end.
Lemma zero_word w : forallb (fun b=>eqb b 0) w=true -> w *> 0inf=0inf.
Proof.
  induction w as [|b w IH]; cbn; intros H; [reflexivity|].
  destruct b; cbn in H; try discriminate. rewrite IH by exact H. symmetry; apply const_unfold.
Qed.
Lemma zeros_spec xs : zeros xs=true -> RT.denote xs=0inf.
Proof.
  induction xs as [|[w n] xs IH]; cbn [zeros RT.denote]; intros H; [reflexivity|].
  destruct (forallb (fun b=>eqb b 0) w) eqn:E; try discriminate.
  rewrite IH by exact H. apply lpow_all0,zero_word,E.
Qed.

Section Cells.
Variable digit : Type.
Variable word : digit -> list Sym.
Variable W : list Sym.
Fixpoint cells_word (xs:list(digit*N)) : list Sym := match xs with
  | []=>[]
  | (p,n)::xs=>word p ++ W^^N.to_nat n ++ cells_word xs end.
Variable batch : N -> list(digit*N) -> option(N*list(digit*N)).

Fixpoint remove_cells xs r := match xs with
  | [] => Some r
  | (p,n)::xs => match RT.remove (word p) r with
    | None => None
    | Some r => match remove_run W n r with
      | Some r => remove_cells xs r | None => None end end end.
Fixpoint push_cells xs r := match xs with
  | [] => r
  | (p,n)::xs => RT.push (word p) 1 (RT.push W n (push_cells xs r)) end.

Lemma remove_cells_spec xs r r' : remove_cells xs r=Some r' ->
  RT.denote r=cells_word xs *> RT.denote r'.
Proof.
  gen r. induction xs as [|[p n] xs IH]; intros r H; cbn [remove_cells] in H.
  - inverts H; reflexivity.
  - destruct (RT.remove (word p) r) as [s|] eqn:E; try discriminate.
    destruct (remove_run W n s) as [s'|] eqn:E'; try discriminate.
    rewrite (RT.remove_spec _ _ _ E),(RT.remove_fast_spec _ _ _ _ _ E'),(IH _ H).
    cbn [cells_word]; rewrite !Str_app_assoc; reflexivity.
Qed.
Lemma push_cells_spec xs r : RT.denote (push_cells xs r)=cells_word xs *> RT.denote r.
Proof.
  induction xs as [|[p n] xs IH]; cbn [push_cells cells_word]; [reflexivity|].
  rewrite !RT.push_spec,IH. change (N.to_nat 1) with 1%nat.
  cbn [lpow]. rewrite app_nil_r,!Str_app_assoc. reflexivity.
Qed.

Definition bulk_stacks q (u:list Sym) t k xs c :=
  if eqb (state c) q then
    let c := orient R c in
    match RT.remove (fast_rev u) (left c),remove_run W k (right c),batch t xs with
    | Some l,Some r,Some (e,ys) => if zeros l then
      match remove_cells xs r with
      | Some r => Some (Cfg (left c) (RT.push W (k+e) (push_cells ys r)) q R)
      | None => None end else None
    | _,_,_ => None end
  else None.

Section BulkCorrect.
Variable tm : TM.
Variable q : Q.
Variable u : list Sym.
Hypothesis rule : forall t xs e ys k r, batch t xs=Some (e,ys) ->
  0inf <* rev u {{q}}> (W^^N.to_nat k *> cells_word xs *> r) -[tm]->*
  0inf <* rev u {{q}}> (W^^N.to_nat (k+e) *> cells_word ys *> r).

Lemma bulk_stacks_spec t k xs c c' : bulk_stacks q u t k xs c=Some c' ->
  denote c -[tm]->* denote c'.
Proof.
  unfold bulk_stacks. destruct (eqb_spec (state c) q); try discriminate.
  pose proof (orient_direction R c) as Hd. pose proof (orient_state R c) as Hq.
  rewrite <-(orient_spec R c). remember (orient R c) as z.
  destruct z as [l r q' d]; cbn [left right state direction] in *; subst.
  destruct (RT.remove (fast_rev u) l) as [l0|] eqn:El; try discriminate.
  destruct (remove_run W k r) as [r0|] eqn:Er; try discriminate.
  destruct (batch t xs) as [[e ys]|] eqn:Eb; try discriminate.
  destruct (zeros l0) eqn:Ez; try discriminate.
  destruct (remove_cells xs r0) as [r1|] eqn:Ec; intros H; inverts H.
  cbn [denote left right state direction].
  rewrite !RT.push_spec,push_cells_spec,(RT.remove_spec _ _ _ El),
    (zeros_spec _ Ez),(RT.remove_fast_spec _ _ _ _ _ Er),(remove_cells_spec _ _ _ Ec).
  rewrite fast_rev_spec. eapply rule; exact Eb.
Qed.
End BulkCorrect.
End Cells.


Definition initial := Cfg [] [] A R.
Lemma initial_spec : denote initial=c0.
Proof. reflexivity. Qed.
End Sk1Check.

Module Sk1Auto.
Import Sk1Check.
Import RM.
Local Opaque RT.remove_fast RT.remove RT.push.

(* Proposals need not be complete: the bulk/scan checkers certify each use. *)
Definition front_size (r:RT.t) := RT.size (firstn 2 r).
Definition periodic (w:list Sym) (r:RT.t) :=
  let '(x,v):=match r with
    | (x,Npos xH)::(v,_)::_=>(x,v)
    | (v,_)::_=>([],v) | []=>([],[]) end in
  eqb (x++v^^length w) (w^^length v++x).
Fixpoint count_run fuel w r : N*RT.t := match fuel with
  | O=>(0%N,r)
  | S fuel=>match (if periodic w r then RT.skip w (front_size r) r else None) with
    | Some(k,s)=>let '(n,s):=count_run fuel w s in ((k+n)%N,s)
    | None=>match RT.remove w r with
      | Some s=>let '(n,s):=count_run fuel w s in ((1+n)%N,s)
      | None=>(0%N,r) end end end.

Section Proposal.
Variable digit : Type.
Variable W : list Sym.
Variable word : digit -> list Sym.
Variable next : digit -> digit.
Variable take : digit -> nat.
Variable index : digit -> N.
Variable period : nat.
Variable order : list digit.
Fixpoint first_bad fuel p n : N := match fuel with
  | O=>1%N
  | S fuel=>if (N.of_nat(take p)<=?n)%N
    then (1+first_bad fuel (next p) (n-N.of_nat(take p)))%N else 1%N end.
Definition unsafe p n := (N.of_nat period*(n/2)+first_bad period p (n mod 2))%N.
Definition better (a b:option(digit*N*RT.t)) := match a,b with
  | Some(p,n,r),Some(q,m,s)=>if (n<?m)%N then b else a
  | None,_=>b | _,None=>a end.
Fixpoint choose ps r : option(digit*N*RT.t) := match ps with
  | []=>None
  | p::ps=>let cand:=match RT.remove (word p) r with
    | None=>None
    | Some r=>let '(n,r):=count_run 32 W r in Some(p,n,r) end in
    better cand (choose ps r) end.
Fixpoint propose_cells fuel r cap : N*list(digit*N) := match fuel with
  | O=>(0%N,[])
  | S fuel=>match choose order r with
    | None=>(0%N,[])
    | Some(p,n,r)=>
      let t:=N.pred(unsafe p n) in
      let t:=match cap with None=>t | Some u=>N.min t u end in
      let child:=((t+index p)/N.of_nat period)%N in
      if (child=?0)%N then (t,[(p,n)]) else
        let '(u,xs):=propose_cells fuel r (Some child) in
        (N.min t (N.of_nat period*u+N.of_nat (Nat.pred period)-index p)%N,(p,n)::xs)
    end end.
Definition proposal q (u:list Sym) c : option(N*N*list(digit*N)) :=
  if eqb (state c) q then
    let c:=orient R c in
    match RT.remove (fast_rev u) (left c) with
    | Some l=>if zeros l then
      let '(k,r):=count_run 32 W (right c) in
      let '(t,xs):=propose_cells 256 r None in
      if (t=?0)%N then None else Some(t,k,xs)
      else None
    | None=>None end
  else None.

End Proposal.

Fixpoint drop n r := match n with O=>r | S n=>drop n (snd(RT.pop r)) end.
Definition scan_count (s:Sk1Counter.scan) c : N :=
  if eqb (state c) (Sk1Counter.scan_q s) then
    let c:=orient (Sk1Counter.scan_dir s) c in
    if zeros (drop 11 (left c)) then 0%N else
    let '(ctx,dst,w,src):=match Sk1Counter.scan_dir s with
      | L=>(Sk1Counter.scan_context s,right c,fast_rev(Sk1Counter.scan_in s),left c)
      | R=>(fast_rev(Sk1Counter.scan_context s),left c,Sk1Counter.scan_in s,right c) end in
    match RT.remove ctx dst with
    | None=>0%N
    | Some _=>let '(n,tail):=count_run 32 w src in
      match Sk1Counter.scan_dir s with
      | L=>if zeros (drop 11 tail) then (n-6)%N else n | R=>n end end
  else 0%N.
Section Scan.
Variable min_scan : N.
Definition auto_scan s c :=
  let n:=scan_count s c in
  if (n<?min_scan)%N then None else use_scan s n c.
Fixpoint try_scans scans c := match scans with
  | []=>None | s::scans=>match auto_scan s c with
    | Some c=>Some c | None=>try_scans scans c end end.
Section Run.
Variable auto_bulk : config -> option config.
Definition advance tm scans c : config+unit := match auto_bulk c with
  | Some c=>inl c
  | None=>match try_scans scans c with
    | Some c=>inl c
    | None=>match RM.raw tm c with Some c=>inl c | None=>inr tt end end end.
Definition check tm scans fuel := match N_iter_until (advance tm scans) (inl initial) fuel with
  | inl _=>false | inr _=>true end.

Section Correct.
Variable tm:TM.
Variable scans:list Sk1Counter.scan.
Hypothesis scans_ok:Forall (Sk1Counter.scan_valid tm) scans.
Hypothesis bulk_ok:forall c c', auto_bulk c=Some c' -> denote c -[tm]->* denote c'.

Lemma auto_scan_spec s c c': Sk1Counter.scan_valid tm s -> auto_scan s c=Some c' ->
  denote c -[tm]->* denote c'.
Proof.
  intros H. unfold auto_scan. destruct (N.ltb (scan_count s c) min_scan); try discriminate.
  apply use_scan_spec,H.
Qed.
Lemma try_scans_spec ss c c':Forall(Sk1Counter.scan_valid tm) ss -> try_scans ss c=Some c' ->
  denote c -[tm]->* denote c'.
Proof.
  intros H. induction H; cbn [try_scans]; [discriminate|].
  destruct (auto_scan x c) as [c''|] eqn:E; [intros H'; inverts H'|apply IHForall].
  eapply auto_scan_spec; eauto.
Qed.
Lemma advance_spec c:match advance tm scans c with
  | inl c'=>denote c -[tm]->* denote c' | inr _=>halted tm (denote c) end.
Proof.
  unfold advance. destruct (auto_bulk c) as [c'|] eqn:E; [eapply bulk_ok; eauto|].
  destruct (try_scans scans c) as [c'|] eqn:Es; [eapply try_scans_spec; eauto|].
  pose proof(RM.raw_spec tm c) as H. destruct(RM.raw tm c); [apply evstep_one,H|exact H].
Qed.
Theorem check_spec fuel:check tm scans fuel=true -> halts tm c0.
Proof.
  rewrite <-initial_spec.
  pose proof (@N_iter_until_spec config unit (advance tm scans) (inl initial) fuel
    (fun c=>denote initial -[tm]->* denote c)
    (fun _=>halts tm (denote initial))) as H.
  assert (Hstep:forall c,denote initial -[tm]->* denote c ->
    match advance tm scans c with
    | inl c'=>denote initial -[tm]->* denote c' | inr _=>halts tm (denote initial) end).
  { intros c E. pose proof(advance_spec c) as I. destruct(advance tm scans c).
    - eapply evstep_trans; eauto.
    - eapply halts_evstep; [apply halted_halts,I|exact E]. }
  specialize (H Hstep ltac:(constructor)). unfold check.
  destruct(N_iter_until (advance tm scans) (inl initial) fuel); [discriminate|].
  intros _. exact H.
Qed.
End Correct.
End Run.
End Scan.
End Sk1Auto.

Module Sk1Auto6.
Import Sk1Counter Sk1Check Sk1Auto.
Import RM.

Definition index p : N := match p with
  | D0=>0 | D1=>1 | D2=>2 | D3=>3 | D4=>4 | D5=>5 end%N.
Definition proposal q := Sk1Auto.proposal digit W word next take index 6
  [D5;D4;D3;D2;D1;D0] q [1;0;1].
Definition auto_bulk q c := match proposal q c with
  | Some(t,k,xs)=>bulk_stacks digit word W batch q [1;0;1] t k xs c | None=>None end.
Lemma auto_bulk_spec tm q
  (rule:forall t xs e ys k r, batch t xs=Some(e,ys) ->
    start q (W^^N.to_nat k *> Sk1Counter.cell_word xs *> r) -[tm]->*
    start q (W^^N.to_nat(k+e) *> Sk1Counter.cell_word ys *> r)) c c':
  auto_bulk q c=Some c' -> denote c -[tm]->* denote c'.
Proof.
  unfold auto_bulk. destruct(proposal q c) as [[[t k] xs]|]; try discriminate.
  eapply bulk_stacks_spec; exact rule.
Qed.
End Sk1Auto6.

Module Sk1Auto94.
Import Sk1Check Sk1Counter7 Sk1Auto.
Import RM.

Definition entry (r:side) := 0inf <* <[1;1;1;1;1;0] {{D}}> r.
Definition index p : N := match p with
  | D0=>0 | D1=>1 | D2=>2 | D3=>3 | D4=>4 | D5=>5 | D6=>6 end%N.

Definition proposal := Sk1Auto.proposal digit W word next take index 7
  [D3;D5;D4;D0;D6;D2;D1] D [1;1;1;1;1;0].
Definition auto_bulk c := match proposal c with
  | Some(t,k,xs)=>bulk_stacks digit word W batch D [1;1;1;1;1;0] t k xs c | None=>None end.
Lemma auto_bulk_spec tm
  (rule:forall t xs e ys k r, batch t xs=Some(e,ys) ->
    entry (W^^N.to_nat k *> Sk1Counter7.cell_word xs *> r) -[tm]->*
    entry (W^^N.to_nat(k+e) *> Sk1Counter7.cell_word ys *> r)) c c':
  auto_bulk c=Some c' -> denote c -[tm]->* denote c'.
Proof.
  unfold auto_bulk. destruct(proposal c) as [[[t k] xs]|]; try discriminate.
  eapply bulk_stacks_spec; exact rule.
Qed.
End Sk1Auto94.

Module TM17.
Import Sk1CounterMixed Sk1Check Sk1Auto.
Import BusyCoq.Eqb.
Open Scope sym_scope.

Definition tm := Eval compute in (TM_from_str "1LB1LE_1RC1LB_1LA0RD_1LC0RB_0LF---_0RD1LA").
Definition glider l := l <* <[0;1;0;0] <{{A}}
  [1;0;1;1;0;1;1;1;1;1;0;1;1;1;1;1;1;0] *> 0inf.
Lemma glider_step l : glider l -[tm]->+ glider (l << 1).
Proof. unfold glider. step1. es. Qed.
Lemma glider_nonhalt l : ~halts tm (glider l).
Proof.
  apply (progress_nonhalt_simple tm side glider l).
  intros l'; exists (l' << 1); apply glider_step.
Qed.
Notation "c -->* c'" := (c -[tm]->* c') (at level 40).
Definition W : list Sym := [1;0;1;1;1;1;1;1;1].
Definition U : list Sym := [1;0;0;1;0;1;0;1;0;1;0].
Definition h : list(DH0*DH0) := [((D,rev [0;1;0;1;0;1;0;1;0]),(A,[1;0;1;1;1;1]))].
Inductive digit := D0 | D1 | D2 | D3 | D4 | D5 | D6 | D7 | D8 | D9 | D10 | D11 | D12 | D13 | D14 | D15 | D16 | D17 | D18 | D19 | D20 | D21.
Definition word p : list Sym := match p with
  | D0=>[1;0;1;1;1;1;1;0;1;1;1;1;1;0;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1]
  | D1=>[1;1;1;1;1;1;1;0;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1]
  | D2=>[1;0;1;1;1;1;1;0;1;1;1;1;1;1;1;1;0;1;1;1;1;1;0;1;1;1;1;1;0;1;1;1;1;1;1;1;1;1;1;1;1;1]
  | D3=>[1;1;1;1;1;1;1;1;1;1;0;1;1;1;1;1;0;1;1;1;1;1;0;1;1;1;1;1;1;1;1;1;1;1;1;1]
  | D4=>[1;0;1;1;1;1;1;0;1;1;1;1;1;1;1;1;1;1;1;0;1;1;1;1;1;0;1;1;1;1;1;1;1;1;1;1;1;1;1]
  | D5=>[1;1;1;1;1;1;1;1;1;1;1;1;1;0;1;1;1;1;1;0;1;1;1;1;1;1;1;1;1;1;1;1;1]
  | D6=>[1;0;1;1;1;1]
  | D7=>[1;1;1;1;1;1;1;1;1]
  | D8=>[1;0;1;1;1;1;1;0;1;1;1;1;1;1;1;1;1;1;1;1;1]
  | D9=>[1;1;1;1;1;1;1;1;1;1;1;1;1;1;1]
  | D10=>[1;0;1;1;1;1;1;0;1;1;1;1;1;0;1;1;1;1;1;1;1;1;1;1;1;1;1]
  | D11=>[1;1;1;1;1;1;1;0;1;1;1;1;1;1;1;1;1;1;1;1;1]
  | D12=>[1;0;1;1;1;1;1;0;1;1;1;1;1;1;1;1;0;1;1;1;1]
  | D13=>[1;1;1;1;1;1;1;1;1;1;0;1;1;1;1]
  | D14=>[1;0;1;1;1;1;1;0;1;1;1;1;1;1;1;1;1;1]
  | D15=>[1;1;1;1;1;1;1;1;1;1;1;1]
  | D16=>[1;0;1;1;1;1;1;0;1;1;1;1]
  | D17=>[1;1;1;1;1;1]
  | D18=>[1;0;1;1;1;1;1;0;1;1;1;1;1;0;1;1;1;1]
  | D19=>[1;1;1;1;1;1;1;0;1;1;1;1]
  | D20=>[1;0;1;1;1;1;1;0;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1]
  | D21=>[1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1] end.
Definition next p := match p with
  | D0=>D1
  | D1=>D2
  | D2=>D3
  | D3=>D4
  | D4=>D5
  | D5=>D0
  | D6=>D7
  | D7=>D8
  | D8=>D9
  | D9=>D10
  | D10=>D11
  | D11=>D12
  | D12=>D13
  | D13=>D14
  | D14=>D15
  | D15=>D16
  | D16=>D17
  | D17=>D6
  | D18=>D19
  | D19=>D20
  | D20=>D21
  | D21=>D18 end.
Definition take p : nat := match p with
  | D0 | D2 | D3 | D4 | D5 | D8 | D10 | D11 | D12 | D13 | D14 | D15 | D16 | D17 | D18 | D20 | D21=>0
  | D1 | D6 | D7 | D9 | D19=>1 end.
Definition give p : nat := match p with
  | D0 | D2 | D4 | D6 | D8 | D10 | D12 | D14 | D16 | D18 | D20=>1
  | D1 | D3 | D5 | D7 | D9 | D11 | D13 | D15 | D17 | D19 | D21=>0 end.
Definition carry p : nat := match p with
  | D0 | D1 | D2 | D3 | D4 | D5 | D6 | D7 | D8 | D9 | D10 | D12 | D13 | D14 | D16 | D18 | D19 | D20=>0
  | D11 | D15 | D17 | D21=>1 end.

Definition period p : nat := match p with
  | D0 | D1 | D2 | D3 | D4 | D5=>6
  | D6 | D7 | D8 | D9 | D10 | D11 | D12 | D13 | D14 | D15 | D16 | D17=>12
  | D18 | D19 | D20 | D21=>4 end.
Definition cycle_used p : nat := match p with
  | D0 | D1 | D2 | D3 | D4 | D5 | D18 | D19 | D20 | D21=>1
  | D6 | D7 | D8 | D9 | D10 | D11 | D12 | D13 | D14 | D15 | D16 | D17=>3 end.
Definition cycle_given p : nat := match p with
  | D0 | D1 | D2 | D3 | D4 | D5=>3
  | D6 | D7 | D8 | D9 | D10 | D11 | D12 | D13 | D14 | D15 | D16 | D17=>6
  | D18 | D19 | D20 | D21=>2 end.
Definition cycle_sent p : nat := match p with
  | D0 | D1 | D2 | D3 | D4 | D5=>0
  | D6 | D7 | D8 | D9 | D10 | D11 | D12 | D13 | D14 | D15 | D16 | D17=>3
  | D18 | D19 | D20 | D21=>1 end.

Definition total := Sk1CounterMixed.total digit next take give carry.
Definition totalN := Sk1CounterMixed.totalN digit next take give carry
  period cycle_used cycle_given cycle_sent.
Definition batch := Sk1CounterMixed.batch digit next take give carry
  period cycle_used cycle_given cycle_sent.
Definition cell_word := Sk1CounterMixed.cell_word digit W word.
Lemma period_positive p : (0<period p)%nat.
Proof. destruct p; cbn [period]; lia. Qed.
Lemma cycle_ok p : total p (period p)=
  Sk1CounterMixed.Eff digit p (cycle_used p) (cycle_given p) (cycle_sent p).
Proof. destruct p; reflexivity. Qed.
Lemma wall n : segRLs tm h h (W^^n) (W^^n).
Proof. esx. Qed.
Lemma one0 p : segRLs tm h (h^^carry p) (word p ++ W^^take p)
  (W^^give p ++ word(next p)).
Proof. destruct p; cbn [word next take give carry]; esx. Qed.
Lemma one p n : segRLs tm h (h^^carry p) (word p ++ W^^(take p+n))
  (W^^give p ++ word(next p) ++ W^^n).
Proof.
  pose proof(segRLs_concat (one0 p) (segRLs_wall'' (n:=carry p) (wall n))) as I.
  rewrite lpow_add. repeat rewrite app_assoc in *; exact I.
Qed.
Definition start (r:side) := 0inf <* rev U {{D}}> r.
Lemma emit r : 0inf <* <[1;0] <{{A}} [1;0;1;1;1;1] *> r -->* start r.
Proof. unfold start,U. esx. Qed.
Lemma calls_spec t r r' : sideRLs tm (h^^t) r r' -> start r -->* start r'.
Proof.
  gen r r'. induction t; intros r r' H; cbn [lpow h app] in H.
  - inverts H. constructor.
  - inverts H.
    match goal with Hret : sideRL _ _ _ _ _ |- _ => follow100 Hret end.
    follow emit. apply IHt; assumption.
Qed.
Lemma batch_step t xs e ys k r : batch t xs=Some(e,ys) ->
  start(W^^N.to_nat k *> cell_word xs *> r) -->*
  start(W^^N.to_nat(k+e) *> cell_word ys *> r).
Proof.
  intros H. apply (calls_spec (N.to_nat t)).
  rewrite N2Nat.inj_add,lpow_add,Str_app_assoc.
  eapply segRLs_sideRLs_concat; [eapply segRLs_wall'',wall|].
  pose proof(segRLs_sideRLs_concat
    (Sk1CounterMixed.batch_spec digit W word next take give carry
      period cycle_used cycle_given cycle_sent period_positive cycle_ok
      tm h wall one t xs e ys H) (sideRLseq_O tm r)) as I.
  rewrite Str_app_assoc in I. exact I.
Qed.
(* The following functions only propose a batch. bulk_stacks checks it. *)
Fixpoint prefix_cap (f:digit->nat) fuel p (n:N) : N := match fuel with
  | O=>0%N
  | S fuel=>if (N.of_nat(f p)<=?n)%N
    then (1+prefix_cap f fuel (next p) (n-N.of_nat(f p)))%N else 0%N end.
Definition capacity p n :=
  (N.of_nat(period p)*(n/N.of_nat(cycle_used p))+
    prefix_cap take (period p) p (n mod N.of_nat(cycle_used p)))%N.
Definition inverse p n :=
  (N.of_nat(period p)*(n/N.of_nat(cycle_sent p))+
    prefix_cap carry (period p) p (n mod N.of_nat(cycle_sent p)))%N.
Definition order := [D2;D4;D0;D3;D5;D1;D10;D20;D8;D11;D12;D14;D18;D21;D9;D13;D15;D16;D19;D7;D6;D17].
Fixpoint propose fuel r cap : N*list(digit*N) := match fuel with
  | O=>(0%N,[])
  | S fuel=>match Sk1Auto.choose digit W word order r with
    | None=>(0%N,[])
    | Some(p,n,s)=>
      let t:=match cap with None=>capacity p n | Some c=>N.min (capacity p n) c end in
      let u:=Sk1CounterMixed.sentN digit (totalN p t) in
      if (u=?0)%N then (t,[(p,n)])
      else let '(v,xs):=propose fuel s (Some u) in
        (N.min t (if Nat.eqb (cycle_sent p) 0 then t else inverse p v),(p,n)::xs)
    end end.
Definition proposal c :=
  if eqb (RM.state c) D then
    let z:=orient R c in
    match RT.remove (fast_rev U) (RM.left z) with
    | Some l=>if zeros l then
      let '(k,r):=Sk1Auto.count_run 32 W (RM.right z) in
      let '(t,xs):=propose 256 r None in
      if (t=?0)%N then None else Some(t,k,xs)
      else None
    | None=>None end else None.
Definition auto_bulk c := match proposal c with
  | Some(t,k,xs)=>bulk_stacks digit word W batch D U t k xs c | None=>None end.
Lemma auto_bulk_spec c c' : auto_bulk c=Some c' -> RM.denote c -->* RM.denote c'.
Proof.
  unfold auto_bulk. destruct(proposal c) as [[[t k] xs]|]; try discriminate.
  eapply bulk_stacks_spec; exact batch_step.
Qed.

Definition scans : list Sk1Counter.scan := [
  Sk1Counter.Scan A L [0;0;1;0;1;0;1;0;1] [1;1;1;1;0;1;1;1;1] [];
  Sk1Counter.Scan B L [0;0;1;0;1;0;1;0;1] [1;1;1;1;1;0;1;1;1] [1;1;0];
  Sk1Counter.Scan A L [0;1;0;0;1;0;1;0;1] [1;0;1;1;1;1;1;1;1] [];
  Sk1Counter.Scan F L [0;1;0;0;1;0;1;0;1] [1;1;1;1;1;0;1;1;1] [0];
  Sk1Counter.Scan B L [0;1;0;1;0;0;1;0;1] [1;1;1;1;1;0;1;1;1] [1;1;0];
  Sk1Counter.Scan F L [0;1;0;1;0;0;1;0;1] [1;1;0;1;1;1;1;1;1] [0];
  Sk1Counter.Scan A L [0;1;0;1;0;1;0;0;1] [1;0;1;1;1;1;1;1;1] [];
  Sk1Counter.Scan B L [0;1;0;1;0;1;0;0;1] [1;1;0;1;1;1;1;1;1] [1;1;0];
  Sk1Counter.Scan A L [0;1;0;1;0;1;0;1;0] [1;1;1;1;1;0;1;1;1] [1;0];
  Sk1Counter.Scan F L [0;1;0;1;0;1;0;1;0] [1;1;0;1;1;1;1;1;1] [0];
  Sk1Counter.Scan B R [0;1;1;1;1;1;1;1;1] [1;0;1;0;1;0;1;0;0] [];
  Sk1Counter.Scan B L [0;1;1;1;1;1;1;1;1] [0;1;1;1;1;1;1;1;1] [1;1;1;0;1;1];
  Sk1Counter.Scan B L [1;0;0;1;0;1;0;1;0] [1;1;1;0;1;1;1;1;1] [1;1;1;0;1;1];
  Sk1Counter.Scan E L [1;0;0;1;0;1;0;1;0] [1;1;1;1;1;0;1;1;1] [];
  Sk1Counter.Scan A L [1;0;1;0;0;1;0;1;0] [1;1;1;1;1;0;1;1;1] [1;0];
  Sk1Counter.Scan E L [1;0;1;0;0;1;0;1;0] [1;1;0;1;1;1;1;1;1] [];
  Sk1Counter.Scan A L [1;0;1;0;1;0;0;1;0] [1;1;0;1;1;1;1;1;1] [1;0];
  Sk1Counter.Scan B L [1;0;1;0;1;0;0;1;0] [1;1;1;0;1;1;1;1;1] [1;1;1;0;1;1];
  Sk1Counter.Scan B L [1;0;1;0;1;0;1;0;0] [0;1;1;1;1;1;1;1;1] [1;1;1;0;1;1];
  Sk1Counter.Scan E L [1;0;1;0;1;0;1;0;0] [1;1;0;1;1;1;1;1;1] [];
  Sk1Counter.Scan D R [1;0;1;1;1;1;1;1;1] [0;1;0;1;0;1;0;1;0] [];
  Sk1Counter.Scan B R [1;1;0;1;1;1;1;1;1] [1;0;0;1;0;1;0;1;0] [0];
  Sk1Counter.Scan D R [1;1;1;0;1;1;1;1;1] [1;0;0;1;0;1;0;1;0] [];
  Sk1Counter.Scan B R [1;1;1;1;0;1;1;1;1] [1;0;1;0;0;1;0;1;0] [0];
  Sk1Counter.Scan D R [1;1;1;1;1;0;1;1;1] [1;0;1;0;0;1;0;1;0] [];
  Sk1Counter.Scan B R [1;1;1;1;1;1;0;1;1] [1;0;1;0;1;0;0;1;0] [0];
  Sk1Counter.Scan D R [1;1;1;1;1;1;1;0;1] [1;0;1;0;1;0;0;1;0] [];
  Sk1Counter.Scan C R [1;1;1;1;1;1;1;1;0] [0;1;0;1;0;1;0;0;1] [];
  Sk1Counter.Scan A L [0;1;0;1;0;1] [1;0;1;1;1;1] [];
  Sk1Counter.Scan B L [0;1;0;1;0;1] [1;1;0;1;1;1] [1;1;0];
  Sk1Counter.Scan F L [0;1;0;1;0;1] [1;1;0;1;1;1] [0];
  Sk1Counter.Scan A L [1;0;1;0;1;0] [1;1;0;1;1;1] [1;0];
  Sk1Counter.Scan B L [1;0;1;0;1;0] [0;1;1;1;1;1] [1;1;1;0;1;1];
  Sk1Counter.Scan E L [1;0;1;0;1;0] [1;1;0;1;1;1] [];
  Sk1Counter.Scan B R [1;1] [1;0] [0];
  Sk1Counter.Scan D R [1;1] [1;0] [];
  Sk1Counter.Scan B L [1] [1] []].
Lemma scans_valid : Forall (Sk1Counter.scan_valid tm) scans.
Proof.
  unfold scans. repeat (apply Forall_cons; [solve [unfold Sk1Counter.scan_valid;
    cbn [Sk1Counter.scan_q Sk1Counter.scan_dir Sk1Counter.scan_in
      Sk1Counter.scan_out Sk1Counter.scan_context rev app]; intros; shift_rule; es]|]).
  constructor.
Qed.

Definition glider_check c :=
  if eqb (RM.state c) A then
    let c:=orient L c in
    match RT.remove <[0;1;0;0] (RM.left c),
      RT.remove [1;0;1;1;0;1;1;1;1;1;0;1;1;1;1;1;1;0] (RM.right c) with
    | Some _,Some r=>zeros r | _,_=>false end
  else false.
Lemma glider_check_spec c : glider_check c=true -> ~halts tm (RM.denote c).
Proof.
  unfold glider_check. destruct(eqb_spec (RM.state c) A); [|discriminate].
  pose proof(orient_direction L c) as Hd. pose proof(orient_state L c) as Hq.
  rewrite <-(orient_spec L c). remember(orient L c) as z.
  destruct z as [l r q d]; cbn [RM.left RM.right RM.state RM.direction] in *; subst.
  destruct(RT.remove <[0;1;0;0] l) as [l0|] eqn:El; [|discriminate].
  destruct(RT.remove [1;0;1;1;0;1;1;1;1;1;0;1;1;1;1;1;1;0] r) as [r0|] eqn:Er; [|discriminate].
  intros E. cbn [RM.denote RM.left RM.right RM.state RM.direction].
  rewrite (RT.remove_spec _ _ _ El),(RT.remove_spec _ _ _ Er),(zeros_spec _ E).
  rewrite e. apply glider_nonhalt.
Qed.
Definition advance c : RM.config+unit :=
  if glider_check c then inr tt else
    match Sk1Auto.advance 1 auto_bulk tm scans c with
    | inl c'=>inl c' | inr _=>inl c end.
Lemma advance_spec c : match advance c with
  | inl c'=>RM.denote c -->* RM.denote c' | inr _=>~halts tm (RM.denote c) end.
Proof.
  unfold advance. destruct(glider_check c) eqn:E; [apply glider_check_spec,E|].
  pose proof(Sk1Auto.advance_spec 1 auto_bulk tm scans scans_valid auto_bulk_spec c) as I.
  destruct(Sk1Auto.advance 1 auto_bulk tm scans c); [exact I|constructor].
Qed.
Definition check fuel := match N_iter_until advance (inl initial) fuel with
  | inl _=>false | inr _=>true end.
Theorem check_spec fuel : check fuel=true -> ~halts tm c0.
Proof.
  pose proof(@N_iter_until_spec RM.config unit advance (inl initial) fuel
    (fun c=>c0 -->* RM.denote c) (fun _=>~halts tm c0)) as I.
  assert (S:forall c,c0 -->* RM.denote c ->
    match advance c with inl c'=>c0 -->* RM.denote c' | inr _=>~halts tm c0 end).
  { intros c E. pose proof(advance_spec c) as J. destruct(advance c).
    - eapply evstep_trans; eauto.
    - eapply multistep_nonhalt; eauto. }
  specialize(I S ltac:(constructor)). unfold check.
  destruct(N_iter_until advance (inl initial) fuel); [discriminate|intros _; exact I].
Qed.
Theorem nonhalt: ~halts tm c0.
Proof. apply (check_spec 300000%N). native_check_eq. Qed.
End TM17.

Module TM91.
Import Sk1Tape.
Import BusyCoq.Eqb.

Open Scope sym_scope.
Definition tm := Eval compute in (TM_from_str "1RB0RC_1LC1RF_1RA1LD_1RD0LE_1LD1LC_0RE---").
Notation "c -->* c'" := (c -[tm]->* c') (at level 40).
Definition h : list(DH0*DH0) := [((C,[0]),(C,[1]))].
Definition h' : list(DH0*DH0) := [((C,[0]),(D,[1]))].
Definition W : list Sym := [0;1].
Definition bval (p:bool) : nat := if p then 1 else 0.
Definition bit (p:bool) : list Sym := if p then [0] else [1].
Definition first {A} (xs:list(bool*A)) := match xs with
  | []=>false | (p,_)::_=>p end.
Fixpoint words (xs:list(bool*nat)) : list Sym := match xs with
  | []=>[] | (p,n)::xs=>bit p ++ W^^n ++ words xs end.
Open Scope nat_scope.

(* k calls into the next column must be safe before its last return.
   The guard uses both phases of that column; it never borrows a future gift. *)
Inductive Batch : nat -> list(bool*nat) -> nat -> list(bool*nat) -> Prop :=
| BNil : Batch 0 [] 0 []
| BCons t p n xs k p' f ys m :
    t+bval p=k*2+bval p' ->
    Batch k xs f ys ->
    (k=0 \/ k+2<=n+bval(first xs)+bval(first ys)) ->
    m+k*2=n+f ->
    Batch t ((p,n)::xs) (k*2) ((p',m)::ys).

Lemma batch_head t xs e ys : Batch t xs e ys ->
  t+bval(first xs)=e+bval(first ys).
Proof. intros H; destruct H; cbn [first bval]; lia. Qed.
Lemma batch_even t xs e ys : Batch t xs e ys -> exists k,e=k*2.
Proof. intros H; destruct H; [exists 0|exists k]; reflexivity. Qed.
Lemma batch_nil t e ys : Batch t [] e ys -> t=0 /\ e=0 /\ ys=[].
Proof. intros H; inverts H; auto. Qed.
Lemma batch_refl xs : Batch 0 xs 0 xs.
Proof.
  induction xs as [|[p n] xs IH]; [constructor|].
  apply BCons with (k:=0) (f:=0); cbn; auto.
Qed.
Lemma batch_zero xs e ys : Batch 0 xs e ys -> e=0 /\ ys=xs.
Proof.
  gen e ys. induction xs as [|[p n] xs IH]; intros e ys H.
  - apply batch_nil in H; tauto.
  - inversion H as [|t0 p0 n0 xs0 k p' f zs m Hcount HB HG Hgap]; subst.
    assert (k=0 /\ p'=p) as [E E'] by (destruct p,p'; cbn [bval] in *; intuition lia).
    subst k p'. apply IH in HB. destruct HB; subst. split; [reflexivity|f_equal; f_equal; lia].
Qed.
Lemma first_one xs f ys : Batch 1 xs f ys ->
  bval(first xs)+bval(first ys)=1 /\ f=bval(first xs)*2.
Proof.
  intros H. pose proof(batch_head _ _ _ _ H).
  destruct(batch_even _ _ _ _ H) as [k E].
  destruct(first xs), (first ys); cbn [bval] in *; lia.
Qed.
Lemma guard_positive k xs f ys n : 0<k -> Batch k xs f ys ->
  k+2<=n+bval(first xs)+bval(first ys) -> 2<=n.
Proof.
  intros H B G. pose proof(batch_head _ _ _ _ B).
  destruct(batch_even _ _ _ _ B) as [j E].
  destruct(first xs), (first ys); cbn [bval] in *; lia.
Qed.

Lemma batch_split t xs e ys : Batch (1+t) xs e ys ->
  exists f zs g, Batch 1 xs f zs /\ Batch t zs g ys /\ e=f+g.
Proof.
  gen t e ys. induction xs as [|[p n] xs IH]; intros t e ys H.
  - apply batch_nil in H; lia.
  - inversion H as [|t0 p0 n0 xs0 k p' f tail m Hcount HB HG Hgap]; subst.
    destruct p; cbn [bval] in Hcount.
    + assert (0<k) by (destruct p'; cbn [bval] in *; lia).
      destruct k as [|k]; [lia|].
      destruct (IH k f tail HB) as [f1 [zs [f2 [B1 [B2 E]]]]].
      pose proof(first_one _ _ _ B1) as [F1 F2].
      assert (2<=n) by (eapply guard_positive; eauto; destruct HG; lia).
      exists 2,((false,n-2+f1)::zs),(k*2).
      split; [eapply BCons with (k:=1); cbn [bval]; eauto; lia|].
      split; [|lia]. eapply BCons with (k:=k) (f:=f2); cbn [bval]; eauto; lia.
    + exists 0,((true,n)::xs),(k*2).
      split; [eapply BCons with (k:=0) (f:=0); cbn [bval]; eauto using batch_refl|].
      split; [eapply BCons; cbn [bval]; eauto; lia|lia].
Qed.

Open Scope sym_scope.
Lemma wall n : segRLs tm h h (W^^n) (W^^n).
Proof. esx. Qed.
Lemma wall' n : segRLs tm h' h' (W^^n) (W^^n).
Proof. esx. Qed.
Lemma inc : segRLs tm h [] [1] [0].
Proof. esx. Qed.
Lemma carry0 : segRLs tm h h [0;0;1;0;1] [0;1;0;1;1].
Proof. esx. Qed.
Lemma carry' : segRLs tm h' h' [0;0;1;0;1] [0;1;1;0;1].
Proof. esx. Qed.
Lemma leaf0 : segRLs tm h' [] [0;0;0] [0;1;1].
Proof. esx. Qed.
Lemma leaf1 : segRLs tm h' [] [0;0;1;0;0] [1;0;1;0;0].
Proof. esx. Qed.
Lemma stop l r : halts tm (l <* [0] {{C}}> [0;0;1;1] *> r).
Proof.
  eapply halts_evstep with (c':=l <* [0] <* [1;1;1] {{F}}> [1] *> r).
  2: es. apply halted_halts. reflexivity.
Qed.
Lemma carry n : segRLs tm h h (bit true ++ W^^(2+n))
  (W^^2 ++ bit false ++ W^^n).
Proof. apply (segRLs_concat carry0 (wall n)). Qed.
Open Scope nat_scope.

Lemma batch_one xs e ys : Batch 1 xs e ys ->
  segRLs tm h [] (words xs) (W^^e ++ words ys).
Proof.
  gen e ys. induction xs as [|[p n] xs IH]; intros e ys H.
  - apply batch_nil in H; lia.
  - inversion H as [|t0 p0 n0 xs0 k p' f tail m E HB HG F]; subst.
    assert (k=bval p /\ p'=negb p) as [Ek Ep]
      by (destruct p,p'; cbn [bval] in *; intuition lia).
    subst k p'. destruct p; cbn [bval negb] in *.
    + assert (2<=n) by (eapply guard_positive; eauto; destruct HG; lia).
      specialize (IH _ _ HB).
      replace m with (n-2+f) by lia.
      cbn [words]. rewrite lpow_add. repeat rewrite app_assoc.
      pose proof (segRLs_concat (carry (n-2)) IH) as I.
      repeat rewrite app_assoc in I. applys_eq I; flia.
    + apply batch_zero in HB. destruct HB; subst.
      assert (m=n) by lia. subst m.
      change (segRLs tm h [] (bit false++W^^n++words xs) (bit true++W^^n++words xs)).
      repeat rewrite <-app_assoc. eapply segRLs_concat; [exact inc|constructor].
Qed.
Lemma batch_spec t xs e ys : Batch t xs e ys ->
  segRLs tm (h^^t) [] (words xs) (W^^e ++ words ys).
Proof.
  gen xs e ys. induction t; intros xs e ys H.
  - apply batch_zero in H. destruct H; subst. constructor.
  - destruct (batch_split _ _ _ _ H) as [f [zs [g [B1 [B2 E]]]]].
    subst e. rewrite lpow_add,<-app_assoc.
    change (segRLs tm (h++h^^t) ([]++[]) (words xs) (W^^f++(W^^g++words ys))).
    eapply segRLs_trans; [apply batch_one,B1|].
    eapply segRLs_concat; [eapply segRLs_wall'',wall|apply IHt,B2].
Qed.

Definition bn (p:bool) : N := if p then 1%N else 0%N.
Definition half (n:N) : N*bool := match n with
  | N0=>(0%N,false) | Npos xH=>(0%N,true)
  | Npos (xO p)=>(Npos p,false) | Npos (xI p)=>(Npos p,true) end.
Lemma bn_spec p : N.to_nat(bn p)=bval p.
Proof. destruct p; reflexivity. Qed.
Lemma half_spec n :
  N.to_nat n = N.to_nat(fst(half n))*2+bval(snd(half n)).
Proof. destruct n as [|[p|p|]]; cbn [half fst snd bval]; lia. Qed.
Definition natcells (xs:list(bool*N)) := map (fun '(p,n)=>(p,N.to_nat n)) xs.
Lemma first_natcells xs : first (natcells xs)=first xs.
Proof. destruct xs as [|[]]; reflexivity. Qed.

Fixpoint batch (t:N) (xs:list(bool*N)) : option(N*list(bool*N)) := match xs with
  | []=>if (t=?0)%N then Some(0%N,[]) else None
  | (p,n)::xs=>
    let '(k,p'):=half (t+bn p)%N in
    match batch k xs with
    | None=>None
    | Some(f,ys)=>
      if (if (k=?0)%N then true else (k+2<=?n+bn(first xs)+bn(first ys))%N) then
      if (2*k<=?n+f)%N then Some((2*k)%N,(p',(n+f-2*k)%N)::ys) else None
      else None end end.
Lemma batch_correct t xs e ys : batch t xs=Some(e,ys) ->
  Batch (N.to_nat t) (natcells xs) (N.to_nat e) (natcells ys).
Proof.
  gen t e ys. induction xs as [|[p n] xs IH]; intros t e ys H; cbn [batch] in H.
  - destruct(N.eqb_spec t 0); inverts H; subst; constructor.
  - pose proof(half_spec (t+bn p)) as E.
    destruct(half (t+bn p)%N) as [k p']; cbn [fst snd] in E.
    destruct(batch k xs) as [[f zs]|] eqn:HB; try discriminate.
    destruct(N.eqb_spec k 0) as [Ek|Ek].
    + destruct(N.leb_spec (2*k) (n+f)); inverts H.
      change (Batch (N.to_nat t) (natcells ((p,n)::xs))
        (N.to_nat (2*k)) (natcells ((p',(n+f-2*k)%N)::zs))).
      rewrite (N.mul_comm 2 k).
      cbn [natcells map]. rewrite N2Nat.inj_mul. eapply BCons with (k:=N.to_nat k) (f:=N.to_nat f);
        rewrite ?N2Nat.inj_mul,?N2Nat.inj_add,?bn_spec in *; eauto; lia.
    + destruct(N.leb_spec (k+2) (n+bn(first xs)+bn(first zs))) as [Hg|Hg]; try discriminate.
      assert (Hg':N.to_nat(k+2)<=N.to_nat(n+bn(first xs)+bn(first zs))) by lia.
      rewrite !N2Nat.inj_add,!bn_spec in Hg'.
      destruct(N.leb_spec (2*k) (n+f)); inverts H.
      change (Batch (N.to_nat t) (natcells ((p,n)::xs))
        (N.to_nat (2*k)) (natcells ((p',(n+f-2*k)%N)::zs))).
      rewrite (N.mul_comm 2 k).
      cbn [natcells map]. rewrite N2Nat.inj_mul. eapply BCons with (k:=N.to_nat k) (f:=N.to_nat f);
        rewrite ?first_natcells,?N2Nat.inj_mul,?N2Nat.inj_add,?bn_spec in *; eauto; lia.
Qed.

Open Scope sym_scope.
Definition putbit (b:Sym) (r:Runs.t) := match b,r with
  | 0,[]=>[]
  | 0,_=>let '(c,s):=Runs.pop r in
    if eqb c 1 then Runs.push W 1 s else Runs.push [0] 1 r
  | 1,_=>Runs.push [1] 1 r end.
Lemma putbit_spec b r : Runs.denote(putbit b r)=b >> Runs.denote r.
Proof.
  destruct b.
  - destruct r as [|[w n] r]; [apply const_unfold|]. cbn [putbit].
    pose proof(Runs.pop_spec ((w,n)::r)) as E.
    destruct(Runs.pop ((w,n)::r)) as [b s].
    destruct b; cbn [fst snd] in E.
    + change (Runs.denote(Runs.push [0] 1 ((w,n)::r)) = 0 >> Runs.denote((w,n)::r)).
      rewrite Runs.push_spec. reflexivity.
    + change (Runs.denote(Runs.push W 1 s) = 0 >> Runs.denote((w,n)::r)).
      rewrite Runs.push_spec,E. reflexivity.
  - cbn [putbit]. rewrite Runs.push_spec. reflexivity.
Qed.
Fixpoint putword w r := match w with
  | []=>r | b::w=>putbit b (putword w r) end.
Lemma putword_spec w r : Runs.denote(putword w r)=w *> Runs.denote r.
Proof. induction w; cbn [putword]; [reflexivity|rewrite putbit_spec,IHw; reflexivity]. Qed.
Definition takeW r : N*Runs.t := match r with
  | (w,n)::r'=>if eqb w W then (n,r') else (0%N,r)
  | []=>(0%N,r) end.
Lemma takeW_spec r : Runs.denote r =
  W^^N.to_nat(fst(takeW r)) *> Runs.denote(snd(takeW r)).
Proof.
  destruct r as [|[w n] r]; [reflexivity|].
  cbn [takeW]. destruct(eqb_spec w W); subst; reflexivity.
Qed.
Fixpoint parse fuel r : list(bool*N)*Runs.t := match fuel,r with
  | O,_=>([],r) | _,[]=>([],r)
  | S fuel,_=>let '(b,s):=Runs.pop r in let '(n,s):=takeW s in
    let '(xs,s):=parse fuel s in ((eqb b 0,n)::xs,s) end.
Lemma parse_spec fuel r : Runs.denote r =
  words(natcells(fst(parse fuel r))) *> Runs.denote(snd(parse fuel r)).
Proof.
  gen r. induction fuel; intros r; [reflexivity|].
  destruct r as [|[w n] r]; [reflexivity|].
  cbn [parse]. pose proof(Runs.pop_spec ((w,n)::r)) as E.
  destruct(Runs.pop ((w,n)::r)) as [b s]; cbn [fst snd] in E.
  pose proof(takeW_spec s) as E'.
  destruct(takeW s) as [m s']; cbn [fst snd] in E'.
  specialize(IHfuel s'). destruct(parse fuel s') as [xs z]; cbn [fst snd] in *.
  rewrite E,E',IHfuel. destruct b; cbn [eqb natcells map words bit].
  all: rewrite !Str_app_assoc; reflexivity.
Qed.
Fixpoint putcells xs r := match xs with
  | []=>r | (p,n)::xs=>putword (bit p) (Runs.push W n (putcells xs r)) end.
Lemma putcells_spec xs r : Runs.denote(putcells xs r)=
  words(natcells xs) *> Runs.denote r.
Proof.
  induction xs as [|[p n] xs IH]; [reflexivity|].
  cbn [putcells natcells map words]. rewrite putword_spec,Runs.push_spec,IH,!Str_app_assoc.
  reflexivity.
Qed.

Local Opaque Runs.push Runs.pop Runs.remove.
Definition H (b:bool) := if b then h' else h.
Definition start (r:side) := 0inf <* [0] {{C}}> r.
Lemma single b r r' : sideRLs tm (H b) r r' ->
  sideRL tm (C,[0]) ((if b then D else C),[1]) r r'.
Proof.
  destruct b; intros I; inverts I;
    match goal with J:sideRLs _ [] _ _ |- _=>inverts J end; assumption.
Qed.
Lemma emit (b:bool) r :
  0inf <{{if b then D else C}} [1] *> r -->*
  start ((if b then [0;1;0] else W) *> r).
Proof. destruct b; es. Qed.
Lemma returned k r r' : sideRLs tm h r r' ->
  start (W^^k *> r) -->* start (W^^(1+k) *> r').
Proof.
  intros I. pose proof(segRLs_sideRLs_concat (wall k) I) as J.
  follow100 (single false _ _ J 0inf). follow (emit false (W^^k *> r')). finish.
Qed.
Lemma calls t r r' : sideRLs tm (h^^t) r r' ->
  forall k, start (W^^k *> r) -->* start (W^^(k+t) *> r').
Proof.
  gen r r'. induction t; intros r r' I k.
  - inverts I. replace (k+0) with k by lia. constructor.
  - cbn [lpow h app] in I. inverts I.
    match goal with J:sideRL _ _ _ _ _ |- _=>
      follow (returned k _ _ ltac:(econstructor; [exact J|constructor])) end.
    applys_eq (IHt _ _ ltac:(eassumption) (1+k)); flia.
Qed.
Lemma bulk_rule t xs e ys k r : batch t xs=Some(e,ys) ->
  start (W^^N.to_nat k *> words(natcells xs) *> r) -->*
  start (W^^N.to_nat(k+t+e) *> words(natcells ys) *> r).
Proof.
  intros I. pose proof(segRLs_sideRLs_concat
    (batch_spec _ _ _ _ (batch_correct _ _ _ _ I)) (sideRLseq_O tm r)) as J.
  rewrite Str_app_assoc in J.
  pose proof(calls _ _ _ J (N.to_nat k)) as K.
  repeat rewrite <-Str_app_assoc in K. rewrite <-lpow_add in K.
  repeat rewrite Str_app_assoc in K. applys_eq K; flia.
Qed.

(* This bound is only a proposal; batch checks the exact linear guard. *)
Fixpoint limit (xs:list(bool*N)) : N := match xs with
  | []=>0%N
  | (p,n)::xs=>
    let cap:=(2*limit xs+1-bn p)%N in
    match xs with
    | []=>cap
    | (q,_)::_=>N.min cap (2*N.max 1 (2*N.div2 n+bn q)-bn p-1)%N end end.
Definition bulk r := let '(k,s):=takeW r in
  let '(xs,z):=parse 4096 s in let t:=limit xs in
  if (t=?0)%N then None else match batch t xs with
  | Some(e,ys)=>Some(Runs.push W (k+t+e) (putcells ys z))
  | None=>None end.
Lemma bulk_correct r s : bulk r=Some s -> start(Runs.denote r) -->* start(Runs.denote s).
Proof.
  unfold bulk. pose proof(takeW_spec r) as E.
  destruct(takeW r) as [k r0]; cbn [fst snd] in E.
  pose proof(parse_spec 4096 r0) as E'.
  destruct(parse 4096 r0) as [xs z]; cbn [fst snd] in E'.
  destruct(N.eqb (limit xs) 0); try discriminate.
  destruct(batch (limit xs) xs) as [[e ys]|] eqn:I; intros J; [|discriminate].
  injection J as J. subst s.
  rewrite E,E',Runs.push_spec,putcells_spec. apply bulk_rule,I.
Qed.

Inductive outcome := Failed | Returned (b:bool) (r:Runs.t) | Stopped.
Definition outcome_spec (r:side) o := match o with
  | Failed=>True
  | Returned b s=>sideRLs tm (H b) r (Runs.denote s)
  | Stopped=>forall l,halts tm (l <* [0] {{C}}> r) end.
Definition resume (f:bool->Runs.t->Runs.t) o := match o with
  | Returned b s=>Returned b (f b s) | Failed=>Failed | Stopped=>Stopped end.
Lemma resume_correct w v f r o :
  (forall b,segRLs tm (H b) (H b) w (v b)) ->
  (forall b s,Runs.denote(f b s)=v b *> Runs.denote s) ->
  outcome_spec r o -> outcome_spec (w *> r) (resume f o).
Proof.
  intros R F I. destruct o; cbn [outcome_spec resume] in *; [trivial| |].
  - rewrite F. eapply segRLs_sideRLs_concat; eauto.
  - intros l. apply (sideRLs_halt_single tm (C,[0]) (C,[1]) (w *> r)).
    eapply segRLs_sideRLs_halt_concat; [apply (R false)|constructor; exact I].
Qed.
Lemma leaf_correct b w v r s :
  segRLs tm (H b) [] w v -> Runs.remove w r=Some s ->
  outcome_spec (Runs.denote r) (Returned b (putword v s)).
Proof.
  intros R E. cbn [outcome_spec]. rewrite (Runs.remove_spec _ _ _ E),putword_spec.
  exact (segRLs_sideRLs_concat R (sideRLseq_O tm _)).
Qed.
Fixpoint call fuel r : outcome := match fuel with
  | O=>Failed
  | S fuel=>let '(n,s):=takeW r in
    if (n=?0)%N then
      match Runs.remove [1] r with
      | Some s=>Returned false (putword [0] s)
      | None=>match Runs.remove [0;0;0] r with
        | Some s=>Returned true (putword [0;1;1] s)
        | None=>match Runs.remove [0;0;1;0;0] r with
          | Some s=>Returned true (putword [1;0;1;0;0] s)
          | None=>match Runs.remove [0;0;1;1] r with
            | Some _=>Stopped
            | None=>match Runs.remove [0;0;1;0;1] r with
              | Some s=>resume (fun b=>putword (if b then [0;1;1;0;1] else [0;1;0;1;1])) (call fuel s)
              | None=>Failed end end end end end
    else resume (fun _=>Runs.push W n) (call fuel s) end.
Lemma call_correct fuel r : outcome_spec (Runs.denote r) (call fuel r).
Proof.
  gen r. induction fuel; intros r; [exact I|].
  cbn [call]. pose proof(takeW_spec r) as E.
  destruct(takeW r) as [n s]; cbn [fst snd] in E.
  destruct(N.eqb n 0).
  - destruct(Runs.remove [1] r) as [s1|] eqn:E1.
    + eapply leaf_correct; [exact inc|exact E1].
    + destruct(Runs.remove [0;0;0] r) as [s1|] eqn:E1'.
      * eapply leaf_correct; [exact leaf0|exact E1'].
      * destruct(Runs.remove [0;0;1;0;0] r) as [s1|] eqn:E2.
        -- eapply leaf_correct; [exact leaf1|exact E2].
        -- destruct(Runs.remove [0;0;1;1] r) as [s1|] eqn:E3.
           ++ cbn [outcome_spec]. rewrite (Runs.remove_spec _ _ _ E3). intros l; apply stop.
           ++ destruct(Runs.remove [0;0;1;0;1] r) as [s1|] eqn:E4; [|exact I].
              rewrite (Runs.remove_spec _ _ _ E4).
              eapply resume_correct with
                (v:=fun b:bool=>if b then [0;1;1;0;1] else [0;1;0;1;1]).
              ** intros []; [exact carry'|exact carry0].
              ** intros; apply putword_spec.
              ** apply IHfuel.
  - rewrite E. eapply resume_correct with (v:=fun _=>W^^N.to_nat n).
    + intros []; [apply wall'|apply wall].
    + intros; apply Runs.push_spec.
    + apply IHfuel.
Qed.
Definition advance r : Runs.t+unit := match bulk r with
  | Some s=>inl s
  | None=>match call 4096 r with
    | Returned b s=>inl(putword (if b then [0;1;0] else W) s)
    | Stopped=>inr tt | Failed=>inl r end end.
Lemma advance_correct r : match advance r with
  | inl s=>start(Runs.denote r) -->* start(Runs.denote s)
  | inr _=>halts tm (start(Runs.denote r)) end.
Proof.
  unfold advance. destruct(bulk r) as [s|] eqn:E; [eapply bulk_correct; exact E|].
  pose proof(call_correct 4096 r) as I.
  destruct(call 4096 r); cbn [outcome_spec] in I; [constructor| |exact(I 0inf)].
  rewrite putword_spec. follow100 (single _ _ _ I 0inf). apply emit.
Qed.
Definition initial : Runs.t := [(W,2%N)].
Lemma init : c0 -->* start(Runs.denote initial).
Proof. unfold start,initial,Runs.denote,W. esx. Qed.
Definition check fuel := match N_iter_until advance (inl initial) fuel with
  | inl _=>false | inr _=>true end.
Theorem check_spec fuel : check fuel=true -> halts tm c0.
Proof.
  pose proof(@N_iter_until_spec Runs.t unit advance (inl initial) fuel
    (fun r=>c0 -->* start(Runs.denote r)) (fun _=>halts tm c0)) as I.
  assert (S:forall r,c0 -->* start(Runs.denote r) ->
    match advance r with
    | inl s=>c0 -->* start(Runs.denote s) | inr _=>halts tm c0 end).
  { intros r E. pose proof(advance_correct r) as J. destruct(advance r).
    - eapply evstep_trans; eauto.
    - eapply halts_evstep; eauto. }
  specialize(I S init).
  assert (F:forall x:Runs.t+unit,
    (match x with inl r=>c0 -->* start(Runs.denote r) | inr _=>halts tm c0 end) ->
    (match x with inl _=>false | inr _=>true end)=true -> halts tm c0).
  { intros [r|u]; cbn; [discriminate|tauto]. }
  exact (F _ I).
Qed.

Local Transparent Runs.push Runs.pop Runs.remove.
Theorem halt: halts tm c0.
Proof. apply (check_spec 100000%N). native_check_eq. Qed.
End TM91.

Module TM94.
Import Sk1Check Sk1Counter7 Sk1Auto94.
Open Scope sym_scope.

Definition tm := Eval compute in (TM_from_str "1RB1RB_1LC1RF_1RA1LD_1RE0LC_---1RC_1LC0RD").
Notation "c -->* c'" := (c -[tm]->* c') (at level 40).
Definition h : list (DH0*DH0) := [((D,<[1;1;1;1;1;0]),(C,[0;1;0;1]))].
Definition start (r:side) := 0inf <* <[1;1;1;1;1;0] {{D}}> r.
Lemma wall n : segRLs tm h h (W^^n) (W^^n).
Proof. esx. Qed.
Lemma inc0 : segRLs tm h [] (word D0)
  (W ++ word D1).
Proof. esx. Qed.
Lemma inc1 : segRLs tm h [] (word D1 ++ W)
  (W ++ word D2).
Proof. esx. Qed.
Lemma inc2 : segRLs tm h [] (word D2 ++ W)
  (word D3).
Proof. esx. Qed.
Lemma inc3 : segRLs tm h [] (word D3)
  (W ++ word D4).
Proof. esx. Qed.
Lemma inc4 : segRLs tm h [] (word D4)
  (word D5).
Proof. esx. Qed.
Lemma inc5 : segRLs tm h [] (word D5)
  (W ++ word D6).
Proof. esx. Qed.
Lemma inc6 : segRLs tm h h (word D6)
  (word D0).
Proof. esx. Qed.
Lemma one p n : segRLs tm h (h^^carry p) (word p ++ W^^(take p+n))
  (W^^give p ++ word (next p) ++ W^^n).
Proof.
  destruct p; cbn [take give carry next lpow Nat.add]; rewrite ?app_nil_r;
    repeat rewrite app_assoc; eapply segRLs_concat;
    eauto using inc0,inc1,inc2,inc3,inc4,inc5,inc6,segRLs_O,wall.
Qed.
Lemma emit r : 0inf <{{C}} [0;1;0;1] *> r -->* start r.
Proof. es. Qed.
Lemma calls_spec t r r' : sideRLs tm (h^^t) r r' -> start r -->* start r'.
Proof.
  gen r r'. induction t; intros r r' H; cbn [lpow h app] in H.
  - inverts H. constructor.
  - inverts H.
    match goal with Hret : sideRL _ _ _ _ _ |- _ => follow100 Hret end.
    follow emit. apply IHt; assumption.
Qed.
Lemma batch_step t xs e ys k r : batch t xs=Some(e,ys) ->
  start (W^^N.to_nat k *> cell_word xs *> r) -->*
  start (W^^N.to_nat(k+e) *> cell_word ys *> r).
Proof.
  intros H. apply (calls_spec (N.to_nat t)).
  rewrite N2Nat.inj_add,lpow_add,Str_app_assoc.
  eapply segRLs_sideRLs_concat; [apply walls,wall|].
  pose proof (segRLs_sideRLs_concat
    (batch_spec tm h wall one t xs e ys H) (sideRLseq_O tm r)) as I.
  rewrite Str_app_assoc in I. exact I.
Qed.
Definition scans : list Sk1Counter.scan := [
  Sk1Counter.Scan D R [0;1;0;1;1;1] [1;1;1;1;1;0] [];
  Sk1Counter.Scan C L [0;1;1;1;1;1] [0;1;0;1;1;1] [];
  Sk1Counter.Scan D L [1;0;1;1;1;1] [1;0;1;0;1;1] [];
  Sk1Counter.Scan C L [1;1;0;1;1;1] [1;0;1;0;1;1] [0];
  Sk1Counter.Scan C L [1;1;1;1;0;1] [1;0;1;0;1;1] [0;1;0];
  Sk1Counter.Scan D L [1;1;1;1;0;1] [1;0;1;0;1;1] [1;0];
  Sk1Counter.Scan C L [1;1;1;1;1;0] [1;0;1;0;1;1] [0;1;0];
  Sk1Counter.Scan D L [1;1;1;1;1;0] [1;0;1;0;1;1] [1;0;1;0];
  Sk1Counter.Scan D R [1;1;1] [1;1;1] [0];
  Sk1Counter.Scan C L [0;1] [1;1] [0;1;0];
  Sk1Counter.Scan D L [0;1] [1;1] [1;0];
  Sk1Counter.Scan C L [1;1] [0;1] [];
  Sk1Counter.Scan D L [1;1] [1;0] []].
Lemma scans_valid : Forall (Sk1Counter.scan_valid tm) scans.
Proof.
  unfold scans. repeat (apply Forall_cons; [solve [unfold Sk1Counter.scan_valid;
    cbn [Sk1Counter.scan_q Sk1Counter.scan_dir Sk1Counter.scan_in
      Sk1Counter.scan_out Sk1Counter.scan_context rev app]; intros; shift_rule; es]|]).
  constructor.
Qed.
Theorem halt: halts tm c0.
Proof.
  apply (Sk1Auto.check_spec 1 Sk1Auto94.auto_bulk tm scans scans_valid
    (Sk1Auto94.auto_bulk_spec tm batch_step) 700000%N).
  native_check_eq.
Qed.
End TM94.

Module TM104.
Import Sk1Counter Sk1Check Sk1Auto Sk1Auto6.
Open Scope sym_scope.

Definition tm := Eval compute in (TM_from_str "1LB0RD_1RC0LD_1LE0LA_1RE0LF_1RA1LC_0RB---").
Notation "c -->* c'" := (c -[tm]->* c') (at level 40).
Definition h : list (DH0*DH0) := [((C,<[1;0;1]),(C,[1]))].

Lemma wall n : segRLs tm h h (W^^n) (W^^n).
Proof. esx. Qed.
Lemma inc0 : segRLs tm h [] (word D0) (word D1).
Proof. esx. Qed.
Lemma inc1 : segRLs tm h [] (word D1 ++ W) (W ++ word D2).
Proof. esx. Qed.
Lemma inc2 : segRLs tm h [] (word D2) (word D3).
Proof. esx. Qed.
Lemma inc3 : segRLs tm h [] (word D3 ++ W) (W ++ word D4).
Proof. esx. Qed.
Lemma inc4 : segRLs tm h [] (word D4) (word D5).
Proof. esx. Qed.
Lemma inc5 : segRLs tm h h (word D5) (W ++ word D0).
Proof. esx. Qed.
Lemma one p n : segRLs tm h (h^^carry p) (word p ++ W^^(take p+n))
  (W^^give p ++ word (next p) ++ W^^n).
Proof.
  destruct p; cbn [take give carry next lpow Nat.add]; rewrite ?app_nil_r;
    repeat rewrite app_assoc; eapply segRLs_concat;
    eauto using inc0,inc1,inc2,inc3,inc4,inc5,segRLs_O,wall.
Qed.
Lemma emit r : 0inf <{{C}} [1] *> r -->* 0inf <* <[1;0;1] {{C}}> r.
Proof. es. Qed.
Lemma batch_step t xs e ys k r : batch t xs=Some (e,ys) ->
  start C (W^^N.to_nat k *> cell_word xs *> r) -->*
  start C (W^^N.to_nat (k+e) *> cell_word ys *> r).
Proof. apply (batch_root tm C emit wall one). Qed.
Definition scans : list scan := [
  Scan E L [0;1;1;0;0;1;1;0;1;1] [1;1;1;1;0;1;1;1;1;1] [];
  Scan E L [0;1;1;1;0;1;1;0;1;1] [1;1;1;1;0;1;1;1;1;1] [];
  Scan D L [1;0;1;1;0;0;1;1;0;1] [1;1;1;1;1;0;1;1;1;1] [0;1;0];
  Scan A L [1;1;0;1;1;0;0;1;1;0] [1;1;1;1;0;1;1;1;1;1] [0;1];
  Scan D R [1;1;0;1;1;1;1;1;1;1] [0;0;1;1;0;1;1;0;1;1] [0];
  Scan A R [1;1;1;1;1;1;1;1;1;0] [0;1;1;0;1;1;0;0;1;1] [];
  Scan E L [0;1;1;0;1;1] [1;1;1;1;0;1] [];
  Scan D L [1;0;1;1;0;1] [1;0;1;1;1;1] [0];
  Scan A L [1;1;0;1;1;0] [0;1;1;1;1;1] [];
  Scan D R [1;1;1] [0;1;1] [0]].
Lemma scans_valid : Forall (scan_valid tm) scans.
Proof.
  unfold scans. repeat (apply Forall_cons; [solve [unfold scan_valid;
    cbn [scan_q scan_dir scan_in scan_out scan_context rev app]; intros; shift_rule; es]|]).
  constructor.
Qed.
Theorem halt: halts tm c0.
Proof.
  apply (Sk1Auto.check_spec 3 (Sk1Auto6.auto_bulk C) tm scans scans_valid
    (Sk1Auto6.auto_bulk_spec tm C batch_step) 200000%N).
  native_check_eq.
Qed.
End TM104.

Module TM105.
Import Sk1Counter Sk1Check Sk1Auto Sk1Auto6.
Open Scope sym_scope.

Definition tm := Eval compute in (TM_from_str "1RB1RE_1RC1LE_1LD0RA_1LF0LA_1LB0LC_---1RA").
Notation "c -->* c'" := (c -[tm]->* c') (at level 40).
Definition h : list (DH0*DH0) := [((E,<[1;0;1]),(E,[1]))].

Lemma wall n : segRLs tm h h (W^^n) (W^^n).
Proof. esx. Qed.
Lemma inc0 : segRLs tm h [] (word D0) (word D1).
Proof. esx. Qed.
Lemma inc1 : segRLs tm h [] (word D1 ++ W) (W ++ word D2).
Proof. esx. Qed.
Lemma inc2 : segRLs tm h [] (word D2) (word D3).
Proof. esx. Qed.
Lemma inc3 : segRLs tm h [] (word D3 ++ W) (W ++ word D4).
Proof. esx. Qed.
Lemma inc4 : segRLs tm h [] (word D4) (word D5).
Proof. esx. Qed.
Lemma inc5 : segRLs tm h h (word D5) (W ++ word D0).
Proof. esx. Qed.
Lemma one p n : segRLs tm h (h^^carry p) (word p ++ W^^(take p+n))
  (W^^give p ++ word (next p) ++ W^^n).
Proof.
  destruct p; cbn [take give carry next lpow Nat.add]; rewrite ?app_nil_r;
    repeat rewrite app_assoc; eapply segRLs_concat;
    eauto using inc0,inc1,inc2,inc3,inc4,inc5,segRLs_O,wall.
Qed.
Lemma emit r : 0inf <{{E}} [1] *> r -->* 0inf <* <[1;0;1] {{E}}> r.
Proof. es. Qed.
Lemma batch_step t xs e ys k r : batch t xs=Some (e,ys) ->
  start E (W^^N.to_nat k *> cell_word xs *> r) -->*
  start E (W^^N.to_nat (k+e) *> cell_word ys *> r).
Proof. apply (batch_root tm E emit wall one). Qed.

Definition scans : list scan := [
  Scan A L [1;0;1;1;0;0;1;1;0;1] [1;1;1;1;1;0;1;1;1;1] [0;1;0];
  Scan E R [1;0;1;1;1;1;1;1;1;1] [0;1;1;0;1;1;0;1;1;0] [1];
  Scan C L [1;1;0;1;1;0;0;1;1;0] [1;1;1;1;0;1;1;1;1;1] [0;1];
  Scan C L [1;1;1;0;1;1;0;1;1;0] [0;1;1;1;0;1;1;1;1;1] [];
  Scan E R [1;1;1;1;0;1;1;1;1;1] [1;0;1;1;0;0;1;1;0;1] [1;0;1];
  Scan E L [1;1;0;1;1;0;0;1;1;0] [1;1;1;1;1;0;1;1;1;1] [1;1;1;0];
  Scan E L [1;1;0;1;1;0;1;1;0;0] [1;1;1;1;0;1;1;1;1;1] [1;1;1;0;1];
  Scan B L [0;1;1;0;1;1] [1;1;1;1;0;1] [];
  Scan A L [1;0;1;1;0;1] [1;0;1;1;1;1] [0];
  Scan C L [1;1;0;1;1;0] [0;1;1;1;1;1] [];
  Scan E L [1;1;0;1;1;0] [1;1;1;0;1;1] [];
  Scan B R [0;1;1;1] [1;0;0;1] [];
  Scan E R [1;0;1;1] [0;1;1;0] [1];
  Scan A R [1;1;0;1] [0;1;1;0] [];
  Scan A R [1;1;1] [1;0;1] [1;0];
  Scan E R [1;1;1] [1;0;1] [1;0;1]].
Lemma scans_valid : Forall (scan_valid tm) scans.
Proof.
  unfold scans. repeat (apply Forall_cons; [solve [unfold scan_valid;
    cbn [scan_q scan_dir scan_in scan_out scan_context rev app]; intros; shift_rule; es]|]).
  constructor.
Qed.
Theorem halt: halts tm c0.
Proof.
  apply (Sk1Auto.check_spec 3 (Sk1Auto6.auto_bulk E) tm scans scans_valid
    (Sk1Auto6.auto_bulk_spec tm E batch_step) 200000%N).
  native_check_eq.
Qed.
End TM105.
