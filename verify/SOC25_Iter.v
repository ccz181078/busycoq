From BusyCoq Require Import Helper TM Individual62 BinaryCounter_v2 SimplTape ES_v2 Eqv_WordPairs.
Require Import Lia PeanoNat.
Set Warnings "-abstract-large-number".

(* halts <-> iter_halts for the SOC25Model machines of Eqv_WordPairs.v (TM90-TM97), with an
   explicit step function f and the round map F of an external write-up: F samples the model
   at each left overflow cfgL L 0 X and maps (L, X) to the next (L', X'). *)

Module IterHalts.
Local Open Scope nat_scope.

(* n steps of f; None (halt) absorbs. iter_n f n x = None iff the run from x
   halts within n steps. *)
Fixpoint iter_n {A} (f : A -> option A) (n : nat) (x : A) : option A :=
  match n with
  | O => Some x
  | S n' => match f x with Some y => iter_n f n' y | None => None end
  end.

Lemma iter_n_add {A} (f : A -> option A) a b x :
  iter_n f (a+b) x = match iter_n f a x with Some y => iter_n f b y | None => None end.
Proof.
  revert x. induction a as [|a IH]; intros x; simpl; [reflexivity|].
  destruct (f x); [apply IH | reflexivity].
Qed.

Lemma iter_n_None_le {A} (f : A -> option A) n m x :
  iter_n f n x = None -> n <= m -> iter_n f m x = None.
Proof.
  intros H Hle. replace m with (n + (m - n)) by lia.
  rewrite iter_n_add, H. reflexivity.
Qed.

Lemma iter_halts_step {A} (f : A -> option A) x y :
  f x = Some y -> (iter_halts f x <-> iter_halts f y).
Proof.
  intros E. split; intros H.
  - inversion H; subst; [congruence|]. rewrite E in H0. injection H0 as <-. assumption.
  - eapply iter_halts_S; eassumption.
Qed.

Lemma iter_halts_iter_n {A} (f : A -> option A) n x y :
  iter_n f n x = Some y -> (iter_halts f x <-> iter_halts f y).
Proof.
  revert x. induction n as [|n IH]; intros x H; simpl in H.
  - injection H as <-. tauto.
  - destruct (f x) as [z|] eqn:E; [|discriminate].
    rewrite (iter_halts_step f x z E). apply IH, H.
Qed.

Lemma iter_halts_None {A} (f : A -> option A) x :
  iter_halts f x <-> exists n, iter_n f n x = None.
Proof.
  split.
  - intros H. induction H as [x H|x y H _ [n Hn]].
    + exists 1. simpl. rewrite H. reflexivity.
    + exists (S n). simpl. rewrite H. assumption.
  - intros [n Hn]. revert x Hn. induction n as [|n IH]; intros x Hn; simpl in Hn;
      [discriminate|].
    destruct (f x) as [y|] eqn:E.
    + eapply iter_halts_S; [eassumption | apply IH, Hn].
    + apply iter_halts_O, E.
Qed.

(* Refinement: if each g-step from a P-state is simulated by a positive number
   of f-steps (through C), and a g-halt corresponds to an f-halt, then halting
   is equivalent. *)
Lemma iter_halts_refine {A B} (f : A -> option A) (g : B -> option B) (C : B -> A) (P : B -> Prop) :
  (forall b, P b ->
    match g b with
    | Some b' => (exists n, 0 < n /\ iter_n f n (C b) = Some (C b')) /\ P b'
    | None => iter_halts f (C b)
    end) ->
  forall b0, P b0 -> (iter_halts f (C b0) <-> iter_halts g b0).
Proof.
  intros Hsim b0 Hb0. split.
  - rewrite iter_halts_None. intros [n Hn]. revert b0 Hb0 Hn.
    induction n as [n IH] using (well_founded_induction Nat.lt_wf_0). intros b0 Hb0 Hn.
    pose proof (Hsim b0 Hb0) as Hs. destruct (g b0) as [b'|] eqn:E.
    + destruct Hs as [[k [Hk Hit]] Hb'].
      destruct (Nat.le_gt_cases n k) as [Hle|Hgt].
      * rewrite (iter_n_None_le f n k _ Hn Hle) in Hit. discriminate.
      * replace n with (k + (n - k)) in Hn by lia.
        rewrite iter_n_add, Hit in Hn.
        eapply iter_halts_S; [eassumption|].
        apply (IH (n - k)); [lia | assumption | assumption].
    + apply iter_halts_O, E.
  - intros Hg. revert Hb0. induction Hg as [b E|b b' E _ IH]; intros Hb.
    + pose proof (Hsim b Hb) as Hs. rewrite E in Hs. exact Hs.
    + pose proof (Hsim b Hb) as Hs. rewrite E in Hs.
      destruct Hs as [[k [_ Hit]] Hb'].
      rewrite (iter_halts_iter_n f k _ _ Hit). apply IH, Hb'.
Qed.

End IterHalts.

Module SOC25Iter.
Import IterHalts.
Import SOC25Model.
Close Scope sym.

(* Odd part and 2-adic valuation: m = (x*2+1)*2^i for m <> 0. Fuel m suffices. *)
Fixpoint split_go (fuel n i : nat) : nat * nat :=
  match fuel with
  | O => (0, 0) (* fuel exhausted: unreachable for fuel >= n <> 0; split_lowbit 0 is unspecified *)
  | S fuel' => if Nat.even n then split_go fuel' (Nat.div2 n) (S i) else (Nat.div2 n, i)
  end.

Definition split_lowbit (m : nat) : nat * nat := split_go m m 0.

(* split_go peels factors of 2 off n, counting them in i; the product n*2^i is invariant. *)
Lemma split_go_spec fuel : forall n i, n <> 0 -> n <= fuel ->
  let (x, j) := split_go fuel n i in n * 2^i = (x*2+1)*2^j.
Proof.
  induction fuel as [|fuel IH]; intros n i Hn Hf; [lia|].
  simpl. destruct (Nat.even n) eqn:E.
  - apply Nat.even_spec in E. destruct E as [k Hk]. subst n.
    assert (Nat.div2 (2*k) = k).
    { apply Nat.div2_double. }
    rewrite H. specialize (IH k (S i)). destruct (split_go fuel k (S i)) as [x j].
    rewrite Nat.pow_succ_r' in IH. rewrite <- IH by lia. lia.
  - destruct (Nat.Even_or_Odd n) as [Hev|[k Hk]]; [apply Nat.even_spec in Hev; congruence|].
    subst n. replace (Nat.div2 (2*k+1)) with k.
    + lia.
    + replace (2*k+1) with (S (2*k)) by lia. symmetry. apply Nat.div2_succ_double.
Qed.

Lemma split_lowbit_spec m : m <> 0 ->
  let (x, i) := split_lowbit m in m = (x*2+1)*2^i.
Proof.
  intros Hm. unfold split_lowbit.
  pose proof (split_go_spec m m 0 Hm (le_n m)) as H.
  destruct (split_go m m 0) as [x i]. simpl in H. lia.
Qed.

Lemma split_lowbit_lt x x' i' : x <> 0 -> split_lowbit x = (x', i') -> x' < x.
Proof.
  intros Hx E. pose proof (split_lowbit_spec x Hx) as Hs. rewrite E in Hs.
  pose proof (Nat.pow_nonzero 2 i' ltac:(lia)). nia.
Qed.

(* One step of closed (Eqv_WordPairs.v): None only on RC3_halt. *)
Definition f (c : Config) : option Config :=
  match c with
  | cfgL len O m =>
    if Nat.eqb m (2^len) then
      let l := len - 1 in let a := Nat.div2 l in
      if Nat.even l
      then (* corner_case, RC'_Ov_0 *)
        Some (cfgR (l+1+1+1+(a*5+2)) ((2^(l+1)*2+1)*2^(a*5+2)-1) 0)
      else (* corner_case, RC'_Ov_1 *)
        Some (cfgR (l+1+1+1+(a*5+4)) ((2^(l+1)*2+1)*2^(a*5+4)-1) 1)
    else (* LC_Ov *)
      let (x, i) := split_lowbit m in
      Some (cfgR1 len (2^len-1) i ((2^i-1)*2) x)
  | cfgL len (S k) m => (* LC_Inc *) Some (cfgR len k m)
  | cfgR len k m => (* RC_Inc *) Some (cfgL len k (S m))
  | cfgR1 len k h (S n) m => (* RC1_Inc, LC_Inc *) Some (cfgR1 len (k-1) h n m)
  | cfgR1 len k h O m =>
    let a := Nat.div2 h in
    if Nat.even h then
      if Nat.eqb m 0
      then (* RC1_Ov_0_blank *)
        Some (cfgR (len+1+a*5) ((k*2+1)*2^(a*5)-1) 1)
      else (* RC1_Ov_0 *)
        let (x, i) := split_lowbit m in
        Some (cfgR4 (len+1+a*5) ((k*2+1)*2^(a*5)-1) i ((2^i-1)*2) x)
    else
      if Nat.eqb m 0
      then (* RC1_Ov_1_blank *)
        Some (cfgR (len+1+(a*5+3)) ((k*2+1)*2^(a*5+3)-1) 0)
      else (* RC1_Ov_1 *)
        let (x, i) := split_lowbit m in
        Some (cfgR3 (len+1+(a*5+3)) ((k*2+1)*2^(a*5+3)-1) i ((2^i-1)*2+1) x)
  | cfgR3 len k h (S n) m => (* RC3_Inc, LC_Inc *) Some (cfgR3 len (k-1) h n m)
  | cfgR3 _ _ _ O _ => (* RC3_halt *) None
  | cfgR4 len k h (S n) m => (* RC4_Inc, LC_Inc *) Some (cfgR4 len (k-1) h n m)
  | cfgR4 len k h O m =>
    let a := Nat.div2 h in
    if Nat.even h
    then (* RC4_Ov_0 *)
      Some (cfgR (len+1+(a*5+1)) ((k*2+1)*2^(a*5+1)-1) (m*2+1))
    else if Nat.eqb m 0
    then (* RC4_Ov_1_blank *)
      Some (cfgR (len+1+(a*5+4)) ((k*2+1)*2^(a*5+4)-1) 0)
    else (* RC4_Ov_1 *)
      let (x, i) := split_lowbit m in
      Some (cfgR4 (len+1+(a*5+4)) ((k*2+1)*2^(a*5+4)-1) i ((2^i-1)*2+1) x)
  end.

(* Computable stand-ins for closed's divmod2_cases / lowbit_cases.
   div2_cases h a Hh: case on Nat.even h; a := Nat.div2 h, Hh : h = 2*a+0 or 2*a+1.
   split_lowbit_cases m x i Hm (Hm : m <> 0): case split_lowbit m = (x,i), substituting
   m := (x*2+1)*2^i. *)
Ltac div2_cases h a Hh :=
  let Eh := fresh "Eh" in
  pose proof (Nat.div2_odd h) as Hh; destruct (Nat.even h) eqn:Eh;
  rewrite <- Nat.negb_even, Eh in Hh; cbn [negb Nat.b2n] in Hh;
  remember (Nat.div2 h) as a.
Ltac split_lowbit_cases m x i Hm :=
  let E := fresh "Es" in let Hs := fresh "Hs" in
  destruct (split_lowbit m) as [x i] eqn:E;
  pose proof (split_lowbit_spec m Hm) as Hs; rewrite E in Hs; subst m.

(* f is sound: the premise of halts_iff (TM.v) with C := to_config b.
   Proof mirrors closed (Eqv_WordPairs.v) branch by branch. *)
Lemma f_spec (b : Machine) x : P x ->
  match f x with
  | Some y => to_config b x -[machine b]->+ to_config b y /\ P y
  | None => halts (machine b) (to_config b x)
  end.
Proof.
  intros HP; destruct x as [len k m|len k m|len k h n m|len k h n m|len k h n m];
    cbn [P] in HP; cbn [f].
  - destruct k as [|k].
    + destruct (Nat.eqb m (2^len)) eqn:E.
      * apply Nat.eqb_eq in E; subst m.
        remember (len-1) as l eqn:Hl; assert (len = l+1) by lia; subst len; clear Hl.
        div2_cases l a Hl; cbn [to_config P]; split.
        -- eapply progress_evstep_trans; [apply corner_case|].
           replace (2^(l+1)) with (2^l*2) by arith; replace l with (a*2) by lia.
           apply progress_evstep; apply RC'_Ov_0; arith.
        -- arith.
        -- eapply progress_evstep_trans; [apply corner_case|].
           replace (2^(l+1)) with (2^l*2) by arith; replace l with (a*2+1) by lia.
           apply progress_evstep; apply RC'_Ov_1; arith.
        -- arith.
      * apply Nat.eqb_neq in E; assert (Hm : m <> 0) by lia.
        split_lowbit_cases m x i Hm; cbn [to_config P].
        split; [apply LC_Ov|].
        pose proof (split_bound_v3 x i len ltac:(lia) E); arith.
    + cbn [to_config P]; split; [apply LC_Inc; lia|lia].
  - cbn [to_config P]; split; [apply RC_Inc|lia].
  - destruct n as [|n].
    2: { destruct k as [|k]; [lia|]; replace (S k - 1) with k by lia.
      cbn [to_config P]; split.
      - eapply progress_evstep_trans; [apply RC1_Inc; lia|].
        apply progress_evstep; apply LC_Inc; lia.
      - lia. }
    div2_cases h a Hh; destruct (Nat.eqb m 0) eqn:Em;
      [apply Nat.eqb_eq in Em; subst m|apply Nat.eqb_neq in Em; split_lowbit_cases m x i Em|
       apply Nat.eqb_eq in Em; subst m|apply Nat.eqb_neq in Em; split_lowbit_cases m x i Em];
      cbn [to_config P].
    + replace h with (a*2) by lia; split; [apply RC1_Ov_0_blank; lia|].
      pose proof (append_bounds len k (a*5) ltac:(lia)); lia.
    + replace h with (a*2) by lia; split; [apply RC1_Ov_0; lia|].
      pose proof (append_bounds len k (a*5) ltac:(lia)).
      pose proof (split_bound_v2 x i); arith.
    + replace h with (a*2+1) by lia; split; [apply RC1_Ov_1_blank; lia|].
      pose proof (append_bounds len k (a*5+3) ltac:(lia)); arith.
    + replace h with (a*2+1) by lia; split; [apply RC1_Ov_1; lia|].
      pose proof (append_bounds len k (a*5+3) ltac:(lia)).
      pose proof (split_bound_v2 x i); arith.
  - destruct n as [|n]; [cbn [to_config]; apply RC3_halt|].
    destruct k as [|k]; [lia|]; replace (S k - 1) with k by lia.
    cbn [to_config P]; split.
    + eapply progress_evstep_trans; [apply RC3_Inc; lia|].
      apply progress_evstep; apply LC_Inc; lia.
    + lia.
  - destruct n as [|n].
    2: { destruct k as [|k]; [lia|]; replace (S k - 1) with k by lia.
      cbn [to_config P]; split.
      - eapply progress_evstep_trans; [apply RC4_Inc; lia|].
        apply progress_evstep; apply LC_Inc; lia.
      - lia. }
    div2_cases h a Hh.
    + cbn [to_config P]; replace h with (a*2) by lia.
      split; [apply RC4_Ov_0; lia|].
      pose proof (append_bounds len k (a*5+1) ltac:(lia)); lia.
    + destruct (Nat.eqb m 0) eqn:Em;
        [apply Nat.eqb_eq in Em; subst m|apply Nat.eqb_neq in Em; split_lowbit_cases m x i Em];
        cbn [to_config P]; replace h with (a*2+1) by lia.
      * split; [apply RC4_Ov_1_blank; lia|].
        pose proof (append_bounds len k (a*5+4) ltac:(lia)); arith.
      * split; [apply RC4_Ov_1; lia|].
        pose proof (append_bounds len k (a*5+4) ltac:(lia)).
        pose proof (split_bound_v2 x i); arith.
Qed.

Example f_1 : f (cfgL 1 1 1) = Some (cfgR 1 0 1).            Proof. reflexivity. Qed.
Example f_2 : f (cfgR 1 0 1) = Some (cfgL 1 0 2).            Proof. reflexivity. Qed.
Example f_3 : f (cfgL 1 0 2) = Some (cfgR 5 19 0).           Proof. reflexivity. Qed.  (* corner, l even *)
Example f_4 : f (cfgL 2 0 4) = Some (cfgR 8 143 1).          Proof. reflexivity. Qed.  (* corner, l odd *)
Example f_5 : f (cfgL 5 0 20) = Some (cfgR1 5 31 2 6 2).     Proof. reflexivity. Qed.  (* LC_Ov, even X *)
Example f_6 : f (cfgR1 5 31 2 6 2) = Some (cfgR1 5 30 2 5 2). Proof. reflexivity. Qed.
Example f_7 : f (cfgR1 5 25 2 0 2) = Some (cfgR4 11 1631 1 2 0). Proof. reflexivity. Qed. (* RC1_Ov_0 *)
Example f_8 : f (cfgR4 11 1629 1 0 0) = Some (cfgR 16 52143 0). Proof. reflexivity. Qed. (* RC4_Ov_1_blank *)
Example f_9 : f (cfgL 3 0 6) = Some (cfgR1 3 7 1 2 1).       Proof. reflexivity. Qed.
Example f_10 : f (cfgR1 3 5 1 0 1) = Some (cfgR3 7 87 0 1 0). Proof. reflexivity. Qed. (* RC1_Ov_1 *)
Example f_11 : f (cfgR3 7 87 0 1 0) = Some (cfgR3 7 86 0 0 0). Proof. reflexivity. Qed.
Example f_12 : f (cfgR3 7 86 0 0 0) = None.                   Proof. reflexivity. Qed. (* RC3_halt *)

Example split_lowbit_20  : split_lowbit 20  = (2, 2).  Proof. reflexivity. Qed.
Example split_lowbit_145 : split_lowbit 145 = (72, 0). Proof. reflexivity. Qed.
Example split_lowbit_1   : split_lowbit 1   = (0, 0).  Proof. reflexivity. Qed.
Example split_lowbit_6   : split_lowbit 6   = (1, 1).  Proof. reflexivity. Qed.
Example split_lowbit_540 : split_lowbit 540 = (67, 2). Proof. reflexivity. Qed.

Lemma eqv_model_gen (b : Machine) x0 : P x0 ->
  (halts (machine b) (to_config b x0) <-> iter_halts f x0).
Proof.
  intros HP. apply (halts_iff _ _ _ f (to_config b) P); [|exact HP].
  intros x Px. exact (f_spec b x Px).
Qed.

(* Round map F: from cfgL L 0 X to the next cfgL L' 0 X' (None if f halts first).
   Invariant: the X' of Some (L', X') is (right counter after the overflow) + k' + 1, because
   the countdown from cfgR L' k' r ends at cfgL L' 0 (r+k'+1).
   F_loop fuel L1 k1 i x runs the RC4_Ov rounds from cfgR4 L1 k1 i 0 x (low block of width i
   drained, rest x) until an RC4_Ov_0 or a run-out; fuel S x suffices. *)
Fixpoint F_loop (fuel L1 k1 i x : nat) : nat * nat :=
  match fuel with
  | O => (L1, k1)
  | S fuel' =>
    let a := Nat.div2 i in
    if Nat.even i
    then (* i even, RC4_Ov_0: push x*2+1 at the top; countdown adds k'+1 *)
      (L1+1+(a*5+1), (k1*2+1)*2^(a*5+1) + (x*2+1))
    else
      let L2 := L1+1+(a*5+4) in
      let k2 := (k1*2+1)*2^(a*5+4)-1 in
      if Nat.eqb x 0
      then (* i odd, RC4_Ov_1_blank: no block left; countdown from cfgR L2 k2 0 *)
        (L2, k2+1)
      else (* i odd, RC4_Ov_1: strip the next low block, borrow n = (2^i'-1)*2+1 *)
        let (x', i') := split_lowbit x in
        F_loop fuel' L2 (k2 - ((2^i'-1)*2+1)) i' x'
  end.

Definition F (p : nat * nat) : option (nat * nat) :=
  let (L, X) := p in
  if Nat.eqb X (2^L)
  then (* full right counter: corner_case + RC'_Ov_0/1, then countdown *)
    let l := L-1 in let a := Nat.div2 l in
    if Nat.even l
    then Some (l+1+1+1+(a*5+2), (2^(l+1)*2+1)*2^(a*5+2)-1 + 1)
    else Some (l+1+1+1+(a*5+4), (2^(l+1)*2+1)*2^(a*5+4)-1 + 2)
  else
    (* LC_Ov: strip the low block of X; borrow 2*(2^h-1) from the left counter *)
    let (m, h) := split_lowbit X in
    let k := 2^L-1 - (2^h-1)*2 in
    let a := Nat.div2 h in
    if negb (Nat.even h)
    then (* h odd *)
      if Nat.eqb m 0
      then (* RC1_Ov_1_blank: push at the top *) Some (L+1+(a*5+3), (k*2+1)*2^(a*5+3))
      else (* RC1_Ov_1, RC3_halt *) None
    else
      let L1 := L+1+a*5 in
      let k1 := (k*2+1)*2^(a*5)-1 in
      if Nat.eqb m 0
      then (* h even, RC1_Ov_0_blank: countdown from cfgR L1 k1 1 *) Some (L1, k1+2)
      else (* h even, RC1_Ov_0: strip next low block, borrow n = (2^i-1)*2; then F_loop *)
        let (x, i) := split_lowbit m in
        Some (F_loop (S x) L1 (k1 - (2^i-1)*2) i x).

Example F_1 : F (1,2) = Some (5,20).        Proof. reflexivity. Qed.
Example F_2 : F (5,20) = Some (16,52144).   Proof. vm_check_eq. Qed.
Example F_3 : F (2,4) = Some (8,145).       Proof. reflexivity. Qed.
Example F_4 : F (1,3) = Some (4,11).        Proof. reflexivity. Qed.
Example F_5 : F (4,11) = Some (7,127).      Proof. reflexivity. Qed.
Example F_6 : F (3,6) = None.               Proof. reflexivity. Qed.   (* halt *)
Example F_7 : F (4,13) = Some (12,3643).    Proof. reflexivity. Qed.   (* two blocks *)
Example F_8 : F (3,5) = Some (9,400).       Proof. reflexivity. Qed.   (* run-out, X' even *)

(* Countdown phases: iterates of f through the borrow/carry countdowns. All
   unconditional; truncated subtraction makes k-n line up with (k-1) applied n times. *)
Lemma iter_cfgL len k n : iter_n f (2*k) (cfgL len k n) = Some (cfgL len 0 (n+k)).
Proof.
  revert n. induction k as [|k IH]; intro n.
  - cbn. rewrite Nat.add_0_r. reflexivity.
  - replace (2 * S k) with (S (S (2 * k))) by lia.
    change (iter_n f (2*k) (cfgL len k (S n)) = Some (cfgL len 0 (n + S k))).
    rewrite IH. do 2 f_equal. lia.
Qed.

Lemma iter_cfgR len k n : iter_n f (2*k+1) (cfgR len k n) = Some (cfgL len 0 (n+k+1)).
Proof.
  replace (2*k+1) with (S (2*k)) by lia.
  change (iter_n f (2*k) (cfgL len k (S n)) = Some (cfgL len 0 (n+k+1))).
  rewrite iter_cfgL. do 2 f_equal. lia.
Qed.

Lemma iter_cfgR1 len k h n m : iter_n f n (cfgR1 len k h n m) = Some (cfgR1 len (k-n) h 0 m).
Proof.
  revert k. induction n as [|n IH]; intro k.
  - cbn. rewrite Nat.sub_0_r. reflexivity.
  - change (iter_n f n (cfgR1 len (k-1) h n m) = Some (cfgR1 len (k-S n) h 0 m)).
    rewrite IH. replace (k - 1 - n) with (k - S n) by lia. reflexivity.
Qed.

Lemma iter_cfgR3 len k h n m : iter_n f n (cfgR3 len k h n m) = Some (cfgR3 len (k-n) h 0 m).
Proof.
  revert k. induction n as [|n IH]; intro k.
  - cbn. rewrite Nat.sub_0_r. reflexivity.
  - change (iter_n f n (cfgR3 len (k-1) h n m) = Some (cfgR3 len (k-S n) h 0 m)).
    rewrite IH. replace (k - 1 - n) with (k - S n) by lia. reflexivity.
Qed.

Lemma iter_cfgR4 len k h n m : iter_n f n (cfgR4 len k h n m) = Some (cfgR4 len (k-n) h 0 m).
Proof.
  revert k. induction n as [|n IH]; intro k.
  - cbn. rewrite Nat.sub_0_r. reflexivity.
  - change (iter_n f n (cfgR4 len (k-1) h n m) = Some (cfgR4 len (k-S n) h 0 m)).
    rewrite IH. replace (k - 1 - n) with (k - S n) by lia. reflexivity.
Qed.

(* P is preserved by f (the P y half of f_spec; any Machine works) and so along runs. *)
Lemma f_P x y : P x -> f x = Some y -> P y.
Proof.
  intros HP E. pose proof (f_spec (TM90.model false) x HP) as H. rewrite E in H. apply H.
Qed.

Lemma iter_n_P n x y : P x -> iter_n f n x = Some y -> P y.
Proof.
  revert x. induction n as [|n IH]; intros x HP H; simpl in H.
  - injection H as <-. exact HP.
  - destruct (f x) as [z|] eqn:E; [|discriminate]. exact (IH z (f_P x z HP E) H).
Qed.

Lemma iter_n_step n x y z : f x = Some y -> iter_n f n y = z -> iter_n f (S n) x = z.
Proof. intros E H. simpl. rewrite E. exact H. Qed.

Lemma iter_n_trans n1 n2 x y z : iter_n f n1 x = Some y -> iter_n f n2 y = z -> iter_n f (n1+n2) x = z.
Proof. intros E H. rewrite iter_n_add, E. exact H. Qed.

(* A step into cfgR L' k' r and its countdown reach cfgL L' 0 (r+k'+1). *)
Lemma countdown_spec n0 c x L' k' r X' : P c -> iter_n f n0 c = Some x ->
  f x = Some (cfgR L' k' r) -> X' = r+k'+1 ->
  (exists n, 0 < n /\ iter_n f n c = Some (cfgL L' 0 X')) /\ P (cfgL L' 0 X').
Proof.
  intros HP H0 Ef ->.
  assert (H : iter_n f (n0 + S (2*k'+1)) c = Some (cfgL L' 0 (r+k'+1)))
    by (apply (iter_n_trans _ _ _ _ _ H0), (iter_n_step _ _ _ _ Ef), iter_cfgR).
  split; [exists (n0 + S (2*k'+1)); split; [lia | exact H] | eapply iter_n_P; eassumption].
Qed.

Lemma F_loop_spec fuel L1 k1 i x : x < fuel -> P (cfgR4 L1 k1 i 0 x) ->
  let (L', X') := F_loop fuel L1 k1 i x in
  (exists n, 0 < n /\ iter_n f n (cfgR4 L1 k1 i 0 x) = Some (cfgL L' 0 X')) /\ P (cfgL L' 0 X').
Proof.
  revert L1 k1 i x. induction fuel as [|fuel IH]; intros L1 k1 i x Hx HP; [lia|].
  cbn [F_loop]. div2_cases i a Hi.
  - (* RC4_Ov_0, then countdown *)
    set (k' := (k1*2+1)*2^(a*5+1)-1).
    assert (Ef : f (cfgR4 L1 k1 i 0 x) = Some (cfgR (L1+1+(a*5+1)) k' (x*2+1)))
      by (cbn [f]; rewrite Eh, <- Heqa; reflexivity).
    apply (countdown_spec 0 _ _ _ _ _ _ HP eq_refl Ef).
    pose proof (Nat.pow_nonzero 2 (a*5+1) ltac:(lia)). subst k'. nia.
  - destruct (Nat.eqb x 0) eqn:Ex.
    + (* RC4_Ov_1_blank, then countdown *)
      set (k2 := (k1*2+1)*2^(a*5+4)-1).
      assert (Ef : f (cfgR4 L1 k1 i 0 x) = Some (cfgR (L1+1+(a*5+4)) k2 0))
        by (cbn [f]; rewrite Eh, <- Heqa, Ex; reflexivity).
      apply (countdown_spec 0 _ _ _ _ _ _ HP eq_refl Ef). lia.
    + (* RC4_Ov_1, drain, recurse *)
      destruct (split_lowbit x) as [x' i'] eqn:Es.
      set (L2 := L1+1+(a*5+4)). set (k2 := (k1*2+1)*2^(a*5+4)-1).
      set (n' := (2^i'-1)*2+1).
      assert (Ef : f (cfgR4 L1 k1 i 0 x) = Some (cfgR4 L2 k2 i' n' x'))
        by (cbn [f]; rewrite Eh, <- Heqa, Ex, Es; reflexivity).
      apply Nat.eqb_neq in Ex.
      assert (H1 : iter_n f (S n') (cfgR4 L1 k1 i 0 x) = Some (cfgR4 L2 (k2-n') i' 0 x'))
        by (apply (iter_n_step _ _ _ _ Ef); apply iter_cfgR4).
      assert (Hx' : x' < fuel) by (pose proof (split_lowbit_lt x x' i' Ex Es); lia).
      specialize (IH L2 (k2-n') i' x' Hx' (iter_n_P _ _ _ HP H1)).
      destruct (F_loop fuel L2 (k2-n') i' x') as [L' X'].
      destruct IH as [[n [Hn Hit]] HP'].
      split; [|exact HP'].
      exists (S n' + n). split; [lia|]. exact (iter_n_trans _ _ _ _ _ H1 Hit).
Qed.

Lemma F_spec L X : P (cfgL L 0 X) ->
  match F (L, X) with
  | Some (L', X') =>
      (exists n, 0 < n /\ iter_n f n (cfgL L 0 X) = Some (cfgL L' 0 X')) /\ P (cfgL L' 0 X')
  | None => iter_halts f (cfgL L 0 X)
  end.
Proof.
  intros HP. cbn [F]. destruct (Nat.eqb X (2^L)) eqn:E.
  - (* corner_case + RC'_Ov, then countdown *)
    apply Nat.eqb_eq in E. div2_cases (L-1) a Hl.
    + set (k' := (2^(L-1+1)*2+1)*2^(a*5+2)-1).
      assert (Ef : f (cfgL L 0 X) = Some (cfgR (L-1+1+1+1+(a*5+2)) k' 0))
        by (cbn [f]; rewrite E, Nat.eqb_refl, Eh, <- Heqa; reflexivity).
      apply (countdown_spec 0 _ _ _ _ _ _ HP eq_refl Ef). lia.
    + set (k' := (2^(L-1+1)*2+1)*2^(a*5+4)-1).
      assert (Ef : f (cfgL L 0 X) = Some (cfgR (L-1+1+1+1+(a*5+4)) k' 1))
        by (cbn [f]; rewrite E, Nat.eqb_refl, Eh, <- Heqa; reflexivity).
      apply (countdown_spec 0 _ _ _ _ _ _ HP eq_refl Ef). lia.
  - (* LC_Ov, drain the left counter by (2^h-1)*2 *)
    destruct (split_lowbit X) as [m h] eqn:Es.
    set (k := 2^L-1 - (2^h-1)*2).
    assert (Ef0 : f (cfgL L 0 X) = Some (cfgR1 L (2^L-1) h ((2^h-1)*2) m))
      by (cbn [f]; rewrite E, Es; reflexivity).
    assert (H1 : iter_n f (S ((2^h-1)*2)) (cfgL L 0 X) = Some (cfgR1 L k h 0 m))
      by (apply (iter_n_step _ _ _ _ Ef0); apply iter_cfgR1).
    pose proof (iter_n_P _ _ _ HP H1) as HP1.
    div2_cases h a Hh; cbn [negb].
    + (* h even *)
      set (L1 := L+1+a*5). set (k1 := (k*2+1)*2^(a*5)-1).
      destruct (Nat.eqb m 0) eqn:Em.
      * (* RC1_Ov_0_blank, then countdown *)
        assert (Ef : f (cfgR1 L k h 0 m) = Some (cfgR L1 k1 1))
          by (cbn [f]; rewrite Eh, <- Heqa, Em; reflexivity).
        apply (countdown_spec _ _ _ _ _ _ _ HP H1 Ef). lia.
      * (* RC1_Ov_0, drain, then the F_loop rounds *)
        destruct (split_lowbit m) as [x i] eqn:Es'.
        assert (Ef : f (cfgR1 L k h 0 m) = Some (cfgR4 L1 k1 i ((2^i-1)*2) x))
          by (cbn [f]; rewrite Eh, <- Heqa, Em, Es'; reflexivity).
        assert (H2 : iter_n f (S ((2^i-1)*2)) (cfgR1 L k h 0 m)
                     = Some (cfgR4 L1 (k1 - (2^i-1)*2) i 0 x))
          by (apply (iter_n_step _ _ _ _ Ef); apply iter_cfgR4).
        pose proof (F_loop_spec (S x) L1 (k1 - (2^i-1)*2) i x ltac:(lia)
                      (iter_n_P _ _ _ HP1 H2)) as HL.
        destruct (F_loop (S x) L1 (k1 - (2^i-1)*2) i x) as [L' X'].
        destruct HL as [[n [Hn Hit]] HP'].
        split; [|exact HP'].
        exists (S ((2^h-1)*2) + (S ((2^i-1)*2) + n)). split; [lia|].
        apply (iter_n_trans _ _ _ _ _ H1). exact (iter_n_trans _ _ _ _ _ H2 Hit).
    + (* h odd *)
      destruct (Nat.eqb m 0) eqn:Em.
      * (* RC1_Ov_1_blank, then countdown *)
        set (k' := (k*2+1)*2^(a*5+3)-1).
        assert (Ef : f (cfgR1 L k h 0 m) = Some (cfgR (L+1+(a*5+3)) k' 0))
          by (cbn [f]; rewrite Eh, <- Heqa, Em; reflexivity).
        apply (countdown_spec _ _ _ _ _ _ _ HP H1 Ef).
        pose proof (Nat.pow_nonzero 2 (a*5+3) ltac:(lia)). subst k'. nia.
      * (* RC1_Ov_1, drain, RC3_halt *)
        destruct (split_lowbit m) as [x i] eqn:Es'.
        set (L3 := L+1+(a*5+3)). set (k3 := (k*2+1)*2^(a*5+3)-1).
        set (n3 := (2^i-1)*2+1).
        assert (Ef : f (cfgR1 L k h 0 m) = Some (cfgR3 L3 k3 i n3 x))
          by (cbn [f]; rewrite Eh, <- Heqa, Em, Es'; reflexivity).
        rewrite (iter_halts_iter_n f _ _ _ H1), (iter_halts_step f _ _ Ef),
          (iter_halts_iter_n f _ _ _ (iter_cfgR3 L3 k3 i n3 x)).
        apply iter_halts_O. reflexivity.
Qed.

Lemma F_iter L X : P (cfgL L 0 X) -> (iter_halts f (cfgL L 0 X) <-> iter_halts F (L, X)).
Proof.
  intros HP.
  refine (iter_halts_refine f F (fun p => cfgL (fst p) 0 (snd p))
           (fun p => P (cfgL (fst p) 0 (snd p))) _ (L, X) HP).
  intros [L0 X0] H. cbn [fst snd] in H |- *. pose proof (F_spec L0 X0 H) as HS.
  destruct (F (L0, X0)) as [[L' X']|]; exact HS.
Qed.

(* From cfgL L k X the countdown reaches the round start cfgL L 0 (X+k). *)
Lemma eqv_F_gen L k X : P (cfgL L 0 (X+k)) ->
  (iter_halts f (cfgL L k X) <-> iter_halts F (L, X+k)).
Proof.
  intros HP. rewrite (iter_halts_iter_n f _ _ _ (iter_cfgL L k X)). exact (F_iter L (X+k) HP).
Qed.

(* Closed-form recursion G for F on odd X <> 2^L: m := (X-1)/2, read gaps g of m from the
   low end (m = (m'*2+1)*2^g), accumulator u. Each odd gap 2a+1 followed by another block
   multiplies u by 2^(a*5+5) and subtracts the next borrow; the first even gap ends the round;
   if the blocks run out after an odd gap, L' = Lp + (a*5+5) + 1 and X' is even.
   G_loop fuel Lp u g m is that loop; fuel S m suffices. *)
Fixpoint G_loop (fuel Lp u g m : nat) : nat * nat :=
  match fuel with
  | O => (Lp, u)
  | S fuel' =>
    let a := Nat.div2 g in
    if Nat.even g
    then (* final even gap *) (Lp + (a*5+3), u*2^(a*5+1) + (m*2+1))
    else
      let Lp2 := Lp + (a*5+5) in
      if Nat.eqb m 0
      then (* run-out after an odd gap *) (Lp2 + 1, u*2^(a*5+4))
      else
        let (m', g') := split_lowbit m in
        G_loop fuel' Lp2 (u*2^(a*5+5) - 2^(g'+2) + 1) g' m'
  end.

Definition G (p : nat * nat) : nat * nat :=
  let (L, X) := p in
  let (m, g) := split_lowbit (Nat.div2 (X-1)) in
  G_loop (S m) L (2^(L+2) - 2^(g+2) + 1) g m.

Example G_1 : G (4,11) = (7,127).    Proof. reflexivity. Qed.
Example G_2 : G (4,13) = (12,3643).  Proof. reflexivity. Qed.   (* two blocks *)
Example G_3 : G (3,5) = (9,400).     Proof. reflexivity. Qed.   (* run-out, X' even *)

(* Loop invariant: L1 = Lp+1 and u = k1*2+1 (exact in nat, truncation included). *)
Lemma F_loop_G_loop fuel : forall Lp k1 i x, x < fuel ->
  F_loop fuel (Lp+1) k1 i x = G_loop fuel Lp (k1*2+1) i x.
Proof.
  induction fuel as [|fuel IH]; intros Lp k1 i x Hx; [lia|].
  cbn [F_loop G_loop]. destruct (Nat.even i).
  - f_equal; lia.
  - destruct (Nat.eqb x 0) eqn:Ex.
    + pose proof (Nat.pow_nonzero 2 (Nat.div2 i*5+4) ltac:(lia)). f_equal; nia.
    + apply Nat.eqb_neq in Ex. destruct (split_lowbit x) as [x' i'] eqn:Es.
      assert (Hx' : x' < fuel) by (pose proof (split_lowbit_lt x x' i' Ex Es); lia).
      replace (Lp+1+1+(Nat.div2 i*5+4)) with (Lp+(Nat.div2 i*5+5)+1) by lia.
      rewrite (IH _ _ _ _ Hx'). f_equal.
      replace (2^(Nat.div2 i*5+5)) with (2^(Nat.div2 i*5+4)*2)
        by (replace (Nat.div2 i*5+5) with (S (Nat.div2 i*5+4)) by lia;
            rewrite Nat.pow_succ_r'; lia).
      replace (2^(i'+2)) with (2^i'*4) by (rewrite Nat.pow_add_r; reflexivity).
      pose proof (Nat.pow_nonzero 2 (Nat.div2 i*5+4) ltac:(lia)).
      pose proof (Nat.pow_nonzero 2 i' ltac:(lia)).
      set (A := 2^(Nat.div2 i*5+4)) in *. set (B := 2^i') in *. nia.
Qed.

Lemma split_lowbit_odd X : Nat.odd X = true -> split_lowbit X = (Nat.div2 (X-1), 0).
Proof.
  intros Ho. destruct X as [|X]; [discriminate|].
  rewrite Nat.odd_succ in Ho. apply Nat.even_spec in Ho as [k ->].
  unfold split_lowbit. cbn [split_go].
  replace (Nat.even (S (2*k))) with false
    by (symmetry; rewrite <- Nat.negb_odd, Nat.odd_succ, Nat.even_mul; reflexivity).
  replace (S (2*k) - 1) with (2*k) by lia.
  rewrite Nat.div2_succ_double, Nat.div2_double. reflexivity.
Qed.

(* P (cfgL L 0 X) gives 2 <= X, so odd X >= 3 and m = (X-1)/2 <> 0. *)
Lemma F_G L X : Nat.odd X = true -> X <> 2^L -> P (cfgL L 0 X) -> F (L, X) = Some (G (L, X)).
Proof.
  intros Ho HL HP. cbn [P] in HP.
  cbn [F G]. rewrite (proj2 (Nat.eqb_neq X (2^L)) HL), (split_lowbit_odd X Ho).
  cbn [Nat.div2 Nat.even negb].
  assert (Hm : Nat.div2 (X-1) <> 0).
  { destruct X as [|[|[|X]]]; [lia|lia|cbn in Ho; discriminate|].
    replace (S (S (S X)) - 1) with (S (S X)) by lia. cbn. discriminate. }
  rewrite (proj2 (Nat.eqb_neq _ 0) Hm).
  destruct (split_lowbit (Nat.div2 (X-1))) as [x i] eqn:Es.
  f_equal. replace (L+1+0*5) with (L+1) by lia.
  rewrite (F_loop_G_loop (S x) L _ i x ltac:(lia)). f_equal.
  pose proof (Nat.pow_nonzero 2 L ltac:(lia)). pose proof (Nat.pow_nonzero 2 i ltac:(lia)).
  rewrite !Nat.pow_add_r. cbn [Nat.pow]. nia.
Qed.

End SOC25Iter.

Module TM90_iter.
Import SOC25Model. Close Scope sym.
Lemma eqv_model b : halts (TM90.machine b) c0 <-> iter_halts SOC25Iter.f (cfgL 1 1 1).
Proof.
  rewrite (halts_evstep_iff _ _ _ (TM90.init b)).
  apply (SOC25Iter.eqv_model_gen (TM90.model b)); cbn [P]; lia.
Qed.
Lemma eqv_F b : halts (TM90.machine b) c0 <-> iter_halts SOC25Iter.F (1, 2).
Proof.
  rewrite eqv_model.
  apply (SOC25Iter.eqv_F_gen 1 1 1); cbn [P]; lia.
Qed.
End TM90_iter.

Module TM91_iter.
Import SOC25Model. Close Scope sym.
Lemma eqv_model : halts TM91.tm c0 <-> iter_halts SOC25Iter.f (cfgL 1 1 1).
Proof.
  rewrite (halts_evstep_iff _ _ _ TM91.init).
  apply (SOC25Iter.eqv_model_gen TM91.model); cbn [P]; lia.
Qed.
Lemma eqv_F : halts TM91.tm c0 <-> iter_halts SOC25Iter.F (1, 2).
Proof.
  rewrite eqv_model.
  apply (SOC25Iter.eqv_F_gen 1 1 1); cbn [P]; lia.
Qed.
End TM91_iter.

Module TM92_iter.
Import SOC25Model. Close Scope sym.
Lemma eqv_model : halts TM92.tm c0 <-> iter_halts SOC25Iter.f (cfgL 1 1 1).
Proof.
  rewrite (halts_evstep_iff _ _ _ TM92.init).
  apply (SOC25Iter.eqv_model_gen TM92.model); cbn [P]; lia.
Qed.
Lemma eqv_F : halts TM92.tm c0 <-> iter_halts SOC25Iter.F (1, 2).
Proof.
  rewrite eqv_model.
  apply (SOC25Iter.eqv_F_gen 1 1 1); cbn [P]; lia.
Qed.
End TM92_iter.

Module TM93_iter.
Import SOC25Model. Close Scope sym.
Lemma eqv_model b : halts (TM93.machine b) c0 <-> iter_halts SOC25Iter.f (cfgL 2 3 1).
Proof.
  rewrite (halts_evstep_iff _ _ _ (TM93.init b)).
  apply (SOC25Iter.eqv_model_gen (TM93.model b)); cbn [P]; lia.
Qed.
Lemma eqv_F b : halts (TM93.machine b) c0 <-> iter_halts SOC25Iter.F (2, 4).
Proof.
  rewrite eqv_model.
  apply (SOC25Iter.eqv_F_gen 2 3 1); cbn [P]; lia.
Qed.
End TM93_iter.

Module TM94_iter.
Import SOC25Model. Close Scope sym.
Lemma eqv_model : halts TM94.tm c0 <-> iter_halts SOC25Iter.f (cfgL 2 3 1).
Proof.
  rewrite (halts_evstep_iff _ _ _ TM94.init).
  apply (SOC25Iter.eqv_model_gen TM94.model); cbn [P]; lia.
Qed.
Lemma eqv_F : halts TM94.tm c0 <-> iter_halts SOC25Iter.F (2, 4).
Proof.
  rewrite eqv_model.
  apply (SOC25Iter.eqv_F_gen 2 3 1); cbn [P]; lia.
Qed.
End TM94_iter.

Module TM95_iter.
Import SOC25Model. Close Scope sym.
Lemma eqv_model : halts TM95.tm c0 <-> iter_halts SOC25Iter.f (cfgL 2 3 1).
Proof.
  rewrite (halts_evstep_iff _ _ _ TM95.init).
  apply (SOC25Iter.eqv_model_gen TM95.model); cbn [P]; lia.
Qed.
Lemma eqv_F : halts TM95.tm c0 <-> iter_halts SOC25Iter.F (2, 4).
Proof.
  rewrite eqv_model.
  apply (SOC25Iter.eqv_F_gen 2 3 1); cbn [P]; lia.
Qed.
End TM95_iter.

Module TM96_iter.
Import SOC25Model. Close Scope sym.
Lemma eqv_model : halts TM96.tm c0 <-> iter_halts SOC25Iter.f (cfgL 2 3 1).
Proof.
  rewrite (halts_evstep_iff _ _ _ TM96.init).
  apply (SOC25Iter.eqv_model_gen TM96.model); cbn [P]; lia.
Qed.
Lemma eqv_F : halts TM96.tm c0 <-> iter_halts SOC25Iter.F (2, 4).
Proof.
  rewrite eqv_model.
  apply (SOC25Iter.eqv_F_gen 2 3 1); cbn [P]; lia.
Qed.
End TM96_iter.

Module TM97_iter.
Import SOC25Model. Close Scope sym.
Lemma eqv_model b : halts (TM97.machine b) c0 <-> iter_halts SOC25Iter.f (cfgL 1 1 2).
Proof.
  rewrite (halts_evstep_iff _ _ _ (TM97.init b)).
  apply (SOC25Iter.eqv_model_gen (TM97.model b)); cbn [P]; lia.
Qed.
Lemma eqv_F b : halts (TM97.machine b) c0 <-> iter_halts SOC25Iter.F (1, 3).
Proof.
  rewrite eqv_model.
  apply (SOC25Iter.eqv_F_gen 1 1 2); cbn [P]; lia.
Qed.
End TM97_iter.
