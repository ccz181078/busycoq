(* Completed machines from cubic.txt: TM1, TM17, TM18, TM39, TM41, TM49.
   Five halt proofs and one nonhalt proof. TM17 and TM18 share their one
   long computation. Only BusyCoq and standard-library dependencies. *)
From BusyCoq Require Import Individual62 ES_v3 Eqb Helper.
From BusyCoq Require BigUint.
Require Import ZifyNat ZifyN ZifyUint63 ZArith Lia String List NArith.
Require Uint63.
Open Scope sym.

Module TM1.
Open Scope sym.
Definition tm := Eval compute in (TM_from_str "1RB0LC_1LA1RB_0LD1LC_1RE1LF_0RE0RB_---0LE").
Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Fixpoint LC l := match l with []=>0inf | n::l=>LC l <* [1]^^n <* [0] end.
Fixpoint RC r := match r with []=>0inf | n::r=>[0] *> [1]^^n *> RC r end.
Definition S l a b c r := LC l <* [1]^^a <* [0] <{{D}} [0] *> [1]^^b *> [0] *> [1]^^c *> RC r.
Definition T l a r := LC l <* [1]^^a {{B}}> RC r.
Definition U l a r := LC l <{{C}} [1]^^a *> RC r.
Definition V l a r := LC l {{E}}> [1]^^a *> RC r.
Close Scope sym.
Lemma Inc l a b c r: S l a (2+b) c r -->* S l (1+a) b (1+c) r.
Proof. es. Qed.
Lemma Incs n l a b c r: S l a (n*2+b) c r -->* S l (a+n) b (c+n) r.
Proof. gen a b c. ind n Inc. Qed.
Lemma S0 l a c r: S l a 0 c r -->* V (0::(1+a)::l) c r.
Proof. es. Qed.
Lemma S1 l a c r: S l a 1 c r -->* T ((1+a)::l) (2+c) r.
Proof. es. Qed.
Lemma Tpos l a c r: T l (1+a) (c::r) -->* U l a ((1+c)::r).
Proof. es. Qed.
Lemma Tposnil l a: T l (1+a) [] -->* U l a [1].
Proof. es. Qed.
Lemma T0 l v c r: T (v::l) 0 (c::r) -->* T l (2+c+v) r.
Proof. es. Qed.
Lemma T0nil l v: T (v::l) 0 [] -->* T l (2+v) [].
Proof. es. Qed.
Lemma Tnil c r: T [] 0 (c::r) -->* T [] (2+c) r.
Proof. es. Qed.
Lemma Tnilnil: T [] 0 [] -->* T [] 2 [].
Proof. es. Qed.
Lemma U3 l a b r: U ((3+a)::l) b r -->* U l (2+a) ((1+b)::r).
Proof. es. Qed.
Lemma U00 l v b c r: U (0::v::l) b (c::r) -->* S l v b c r.
Proof. es. Qed.
Lemma U00nil l v b: U (0::v::l) b [] -->* S l v b 0 [].
Proof. es. Qed.
Lemma U0nil b c r: U [0] b (c::r) -->* S [] 0 b c r.
Proof. es. Qed.
Lemma U0nilnil b: U [0] b [] -->* S [] 0 b 0 [].
Proof. es. Qed.
Lemma Unil b c r: U [] b (c::r) -->* S [] 0 b c r.
Proof. es. Qed.
Lemma Unilnil b: U [] b [] -->* S [] 0 b 0 [].
Proof. es. Qed.
Lemma U2 l b r: U (2::l) b r -->* T (0::l) (2+b) r.
Proof. destruct l; es. Qed.
Lemma HU1 l b r: halts tm (U (1::l) b r).
Proof. destruct l; unfold U, LC; cbn; esx. Qed.
Lemma Vpos l a r: V l (1+a) r -->* T (0::l) a r.
Proof. es. Qed.
Lemma V0 l c r: V l 0 (c::r) -->* V (0::l) c r.
Proof. es. Qed.
Lemma Vblank l: ~halts tm (V l 0 []).
Proof.
  apply (progress_nonhalt_simple tm _ (fun l=>V l 0 []) l).
  intro k. exists (0::k). es.
Qed.
Lemma init: c0 -->* S [] 0 0 1 [].
Proof. unfold S, LC, RC; cbn. esx. Qed.

(* Pair a right excursion with its left return. The recursive premise is
   independent of the left context; no temporary left records are needed. *)
Lemma Right l a b c r:
  S l a 0 (2+b) (c::r) -->* S ((1+a)::l) 0 b (1+c) r.
Proof. follow S0. follow Vpos. follow Tpos. follow U00. finish. Qed.
Inductive Pair : nat -> nat -> list nat -> nat -> list nat -> Prop :=
| PairOdd n c d r: Pair (5+n*2) c (d::r) (2+n) ((4+c+n)::(1+d)::r)
| PairOddNil n c: Pair (5+n*2) c [] (2+n) [4+c+n;1]
| PairEven n c d r v s:
    Pair (c+n) (1+d) r v s ->
    Pair (4+n*2) c (d::r) (2+n) ((1+v)::s).
Lemma Pair_spec b c r v s: Pair b c r v s ->
  forall l a, S l a b c r -->* U l (a+v) s.
Proof.
  induction 1; intros.
  - follow (Incs (2+n) l a 1 c (d::r)). follow S1.
    follow Tpos. follow (U3 l (a+n) (3+c+n) ((1+d)::r)). finish.
  - follow (Incs (2+n) l a 1 c []). follow S1.
    follow Tposnil. follow (U3 l (a+n) (3+c+n) [1]). finish.
  - follow (Incs (2+n) l a 0 c (d::r)). follow (Right l (a+2+n) (c+n) d r).
    follow (IHPair ((3+a+n)::l) 0). follow (U3 l (a+n) v s). finish.
Qed.
Lemma U2Return l v b c r: U (2::v::l) b (c::r) -->* S l v (1+b) (1+c) r.
Proof. follow U2. follow Tpos. follow U00. finish. Qed.
Lemma U2Return0 l v b: U (2::v::l) b [] -->* S l v (1+b) 1 [].
Proof. follow U2. follow Tposnil. follow U00. finish. Qed.
Lemma U2ReturnNil b c r: U [2] b (c::r) -->* S [] 0 (1+b) (1+c) r.
Proof. follow U2. follow Tpos. follow U0nil. finish. Qed.
Lemma U2ReturnNil0 b: U [2] b [] -->* S [] 0 (1+b) 1 [].
Proof. follow U2. follow Tposnil. follow U0nil. finish. Qed.

(* Direct machine-integer kernel. Natural numbers occur only in the proof
   interpretation and the centralized mass bound, never in runtime counters. *)
Module Kernel.
Inductive Frame (A : Type) :=
| FS (l : list A) (a b c : A) (r : list A)
| FT (l : list A) (a : A) (r : list A)
| FU (l : list A) (a : A) (r : list A)
| FV (l : list A) (a : A) (r : list A).
Arguments FS {A}. Arguments FT {A}. Arguments FU {A}. Arguments FV {A}.
Definition denote (x : Frame nat) := match x with
| FS l a b c r => S l a b c r | FT l a r => T l a r
| FU l a r => U l a r | FV l a r => V l a r end.
Fixpoint size (l : list nat) := match l with [] => 0 | n::l => n+1+size l end.
Definition mass (x : Frame nat) := match x with
| FS l a b c r => size l+a+b+c+size r+3
| FT l a r | FU l a r | FV l a r => size l+a+size r end.
Lemma Pair_mass b c r v s : Pair b c r v s ->
  v+size s <= b+c+size r+4.
Proof. induction 1; cbn [size] in *; lia. Qed.

Import PrimInt63.
Notation int := PrimInt63.int.
Local Infix "+" := Uint63.add : uint63_scope.
Local Infix "-" := Uint63.sub : uint63_scope.
Local Infix "/" := Uint63.div : uint63_scope.
Local Infix "mod" := Uint63.mod (at level 40, no associativity) : uint63_scope.
Local Infix "=?" := Uint63.eqb (at level 70, no associativity) : uint63_scope.
Local Infix "<=?" := Uint63.leb (at level 70, no associativity) : uint63_scope.
Definition state := Frame int.
Definition to_nat (x : int) := Z.to_nat (Uint63.to_Z x).
Definition read_list := map to_nat.
Definition read (x : state) : Frame nat := match x with
| FS l a b c r => FS (read_list l) (to_nat a) (to_nat b) (to_nat c) (read_list r)
| FT l a r => FT (read_list l) (to_nat a) (read_list r)
| FU l a r => FU (read_list l) (to_nat a) (read_list r)
| FV l a r => FV (read_list l) (to_nat a) (read_list r) end.
Local Open Scope uint63_scope.
Definition head0 (l : list int) := match l with [] => 0 | n::_ => n end.
Fixpoint pair (r : list int) (b c : int) : option (int * list int) :=
  if 4 <=? b then let k := b/2 in
    if b mod 2 =? 0 then match r with
      | [] => None
      | d::r => match pair r (c+k-2) (d+1) with
        | None => None | Some (v,s) => Some (k,(v+1)::s) end
      end
    else Some (k,(c+k+2)::(head0 r+1)::tl r)
  else None.
Fixpoint back (l : list int) (a : int) (r : list int) : state :=
  match l with
  | v::l' =>
    if 3 <=? v then back l' (v-1) ((a+1)::r) else
    if v =? 1 then FU l a r else
    if v =? 2 then FS (tl l') (head0 l') (a+1) (head0 r+1) (tl r)
    else FS (tl l') (head0 l') a (head0 r) (tl r)
  | [] => FS [] 0 a (head0 r) (tl r)
  end.
Definition basic_s l a b c r : state :=
  let k := b/2 in
  if b mod 2 =? 0 then FV (0::(1+a+k)::l) (c+k) r
  else FT ((1+a+k)::l) (2+c+k) r.
Definition next (x : state) : state := match x with
| FS l a b c r => match pair r b c with
    | Some (v,s) => back l (a+v) s | None => basic_s l a b c r end
| FU l a r => back l a r
| FT l a r => if a =? 0 then FT (tl l) (2+head0 r+head0 l) (tl r)
    else FU l (a-1) ((head0 r+1)::tl r)
| FV l a r => if a =? 0 then match r with
    | [] => x | c::r => FV (0::l) c r end
    else FT (0::l) (a-1) r end.
Definition stop (x : state) := match x with
| FU (v::_) _ _ => v =? 1 | _ => false end.
Definition start : state := FS [] 0 0 1 [].
Local Close Scope uint63_scope.

Lemma eqb_nat a b : (a =? b)%uint63 = (to_nat a =? to_nat b)%nat.
Proof. rewrite ZifyUint63.eqb_eq; unfold to_nat; lia. Qed.
Lemma leb_nat a b : (a <=? b)%uint63 = (to_nat a <=? to_nat b)%nat.
Proof. rewrite ZifyUint63.leb_le; unfold to_nat; lia. Qed.
Lemma add_nat a b : to_nat a+to_nat b < 2^63 ->
  to_nat (a+b)%uint63 = to_nat a+to_nat b.
Proof. unfold to_nat; rewrite Uint63.add_spec; unfold Uint63.wB, Uint63.size; intros; rewrite Z.mod_small; lia. Qed.
Lemma sub_nat a b : to_nat b <= to_nat a ->
  to_nat (a-b)%uint63 = to_nat a-to_nat b.
Proof. unfold to_nat; rewrite Uint63.sub_spec; unfold Uint63.wB, Uint63.size; intros; rewrite Z.mod_small; lia. Qed.
Lemma div_nat a b : to_nat (a/b)%uint63 = to_nat a/to_nat b.
Proof. unfold to_nat; rewrite Uint63.div_spec, Z2Nat.inj_div; lia. Qed.
Lemma mod_nat a b : to_nat (a mod b)%uint63 = to_nat a mod to_nat b.
Proof. unfold to_nat; rewrite Uint63.mod_spec, Z2Nat.inj_mod; lia. Qed.
Lemma n0 : to_nat 0%uint63 = 0. Proof. reflexivity. Qed.
Lemma n1 : to_nat 1%uint63 = 1. Proof. reflexivity. Qed.
Lemma n2 : to_nat 2%uint63 = 2. Proof. reflexivity. Qed.
Lemma n3 : to_nat 3%uint63 = 3. Proof. reflexivity. Qed.
Lemma n4 : to_nat 4%uint63 = 4. Proof. reflexivity. Qed.
#[local] Hint Rewrite n0 n1 n2 n3 n4 : uint_const.
Ltac uint :=
  repeat first [rewrite add_nat by uint | rewrite sub_nat by uint
    | rewrite div_nat | rewrite mod_nat | progress autorewrite with uint_const]; try lia.
Ltac tests :=
  repeat first [rewrite eqb_nat | rewrite leb_nat]; autorewrite with uint_const;
  repeat match goal with
  | |- context[if Nat.leb ?a ?b then _ else _] => destruct (Nat.leb_spec a b)
  | |- context[if Nat.eqb ?a ?b then _ else _] => destruct (Nat.eqb_spec a b)
  end.
Ltac rd := cbn [read read_list map mass size denote head0 tl] in *;
  autorewrite with uint_const in *.
Ltac eq_arith := repeat first [reflexivity | solve [fold Nat.add in *; lia] | progress f_equal].
Ltac direct rule := rd; uint; split;
  [applys_eq rule; eq_arith; try lia|lia].

Lemma pair_spec r b c v s :
  to_nat b+to_nat c+size (read_list r)+4 < 2^60 ->
  pair r b c = Some (v,s) ->
  Pair (to_nat b) (to_nat c) (read_list r) (to_nat v) (read_list s).
Proof.
  revert b c v s; induction r as [|d r IH]; intros b c v s H E;
    cbn [pair] in E; rewrite leb_nat, n4 in E;
    destruct (Nat.leb_spec 4 (to_nat b)); try discriminate;
    rewrite eqb_nat, mod_nat, n2, n0 in E;
    destruct (Nat.eqb_spec (to_nat b mod 2) 0).
  - discriminate.
  - inversion E; subst; rd; uint.
    applys_eq (PairOddNil (to_nat b/2-2) (to_nat c)); eq_arith.
  - destruct (pair r (c+b/2-2)%uint63 (d+1)%uint63) as [[v' s']|] eqn:Er; [|discriminate].
    assert (Hr : Pair (to_nat (c+b/2-2)%uint63) (to_nat (d+1)%uint63)
      (read_list r) (to_nat v') (read_list s')).
    { apply IH; [rd; uint|assumption]. }
    assert (Eb : to_nat (c+b/2-2)%uint63 = to_nat c+to_nat b/2-2) by (rd; uint).
    assert (Ed : to_nat (d+1)%uint63 = to_nat d+1) by (rd; uint).
    rewrite Eb, Ed in Hr.
    pose proof (Pair_mass _ _ _ _ _ Hr) as Hm.
    inversion E; subst; rd; uint.
    applys_eq (PairEven (to_nat b/2-2) (to_nat c) (to_nat d) (read_list r)
      (to_nat v') (read_list s')); try eq_arith.
    applys_eq Hr; eq_arith.
  - inversion E; subst; rd; uint.
    applys_eq (PairOdd (to_nat b/2-2) (to_nat c) (to_nat d) (read_list r)); eq_arith.
Qed.

Lemma back_spec l a r : mass (read (FU l a r))+3 < 2^60 ->
  denote (read (FU l a r)) -->* denote (read (back l a r)) /\
  mass (read (back l a r)) <= mass (read (FU l a r))+3.
Proof.
  revert a r; induction l as [|v l IH]; intros a r H.
  - destruct r as [|c r]; cbn [back]; [direct Unilnil|direct Unil].
  - cbn [back]; tests.
    + assert (HM : mass (read (FU l (v-1)%uint63 ((a+1)%uint63::r))) =
        mass (read (FU (v::l) a r))) by (rd; uint).
      destruct (IH (v-1)%uint63 ((a+1)%uint63::r) ltac:(rewrite HM; assumption)) as [Hr Hm].
      split.
      * eapply evstep_trans; [|apply Hr]. rd; uint;
        applys_eq (U3 (read_list l) (to_nat v-3) (to_nat a) (read_list r)); eq_arith.
      * rewrite HM in Hm; assumption.
    + split; [apply evstep_refl|lia].
    + destruct l as [|w l], r as [|c r];
        first [solve [direct U2ReturnNil0]|solve [direct U2ReturnNil]|solve [direct U2Return0]|solve [direct U2Return]].
    + destruct l as [|w l], r as [|c r];
        first [solve [direct U0nilnil]|solve [direct U0nil]|solve [direct U00nil]|solve [direct U00]].
Qed.

Lemma basic_s_spec l a b c r : mass (read (FS l a b c r))+4 < 2^60 ->
  denote (read (FS l a b c r)) -->* denote (read (basic_s l a b c r)) /\
  mass (read (basic_s l a b c r)) = mass (read (FS l a b c r)).
Proof.
  intros H; unfold basic_s; rewrite eqb_nat, mod_nat, n2, n0.
  destruct (Nat.eqb_spec (to_nat b mod 2) 0); rd; uint; split.
  - follow (Incs (to_nat b/2) (read_list l) (to_nat a) 0 (to_nat c) (read_list r)).
    follow S0. finish.
  - lia.
  - follow (Incs (to_nat b/2) (read_list l) (to_nat a) 1 (to_nat c) (read_list r)).
    follow S1. finish.
  - lia.
Qed.

Theorem next_spec x : mass (read x)+4 < 2^60 ->
  denote (read x) -->* denote (read (next x)) /\
  mass (read (next x)) <= mass (read x)+4.
Proof.
  intros H; destruct x as [l a b c r|l a r|l a r|l a r]; cbn [next].
  - destruct (pair r b c) as [[v s]|] eqn:E.
    + assert (HP : Pair (to_nat b) (to_nat c) (read_list r) (to_nat v) (read_list s)).
      { apply pair_spec; [rd; lia|assumption]. }
      pose proof (Pair_mass _ _ _ _ _ HP) as HM.
      assert (HM' : mass (read (FU l (a+v)%uint63 s)) <= mass (read (FS l a b c r))+1)
        by (rd; uint).
      destruct (back_spec l (a+v)%uint63 s ltac:(lia)) as [Hr Hm].
      split; [|lia]. eapply evstep_trans; [|apply Hr]. rd; uint.
      apply Pair_spec; assumption.
    + destruct (basic_s_spec l a b c r H); split; [assumption|lia].
  - tests.
    + destruct l as [|v l], r as [|c r].
      * direct Tnilnil.
      * direct Tnil.
      * direct T0nil.
      * direct T0.
    + destruct r as [|c r]; [direct Tposnil|direct Tpos]; lia.
  - destruct (back_spec l a r ltac:(lia)); split; [assumption|lia].
  - tests.
    + destruct r as [|c r]; [split; [apply evstep_refl|lia]|direct V0].
    + direct Vpos.
Qed.

Lemma stop_sound x : stop x = true -> halts tm (denote (read x)).
Proof.
  destruct x as [l a b c r|l a r|l a r|l a r]; cbn [stop]; try discriminate.
  destruct l as [|v l]; [discriminate|]. rewrite eqb_nat, n1.
  intros H; apply Nat.eqb_eq in H; rd; rewrite H; apply HU1.
Qed.

Fixpoint advance (fuel : nat) (x : state) :=
  match fuel with 0 => x | Datatypes.S n => advance n (next x) end.
Lemma advance_spec fuel x : mass (read x)+4*fuel < 2^60 ->
  denote (read x) -->* denote (read (advance fuel x)) /\
  mass (read (advance fuel x)) <= mass (read x)+4*fuel.
Proof.
  revert x; induction fuel; intros x H; cbn [advance].
  - split; [apply evstep_refl|lia].
  - destruct (next_spec x ltac:(lia)) as [Hr Hm].
    destruct (IHfuel (next x) ltac:(lia)) as [Hrr Hmm].
    split; [eapply evstep_trans; eauto|lia].
Qed.

Definition block_next (s : state*N) : (state*N)+unit :=
  let '(x,budget) := s in
  if stop x then inr tt else match budget with
  | N0 => inl s | Npos _ => inl (advance 1000 x, N.pred budget) end.
Definition checkN (blocks : N) (x : state) :=
  match N_iter_until block_next (inl (x,blocks)) (N.succ blocks) with
  | inl _ => false | inr _ => true end.

Theorem checkN_sound blocks x : mass (read x)+4000*N.to_nat blocks < 2^60 ->
  checkN blocks x = true -> halts tm (denote (read x)).
Proof.
  intros H.
  assert (HI : match N_iter_until block_next (inl (x,blocks)) (N.succ blocks) with
    | inl (y,budget) => denote (read x) -->* denote (read y) /\
        mass (read y)+4000*N.to_nat budget < 2^60
    | inr _ => halts tm (denote (read x)) end).
  { eapply N_iter_until_spec with
      (P := fun s => let '(y,budget) := s in denote (read x) -->* denote (read y) /\
        mass (read y)+4000*N.to_nat budget < 2^60).
    - intros [y budget] [Hr Hm]; unfold block_next; destruct (stop y) eqn:E.
      + eapply halts_evstep; [apply stop_sound, E|apply Hr].
      + destruct budget as [|p]; [split; assumption|].
        destruct (advance_spec 1000 y ltac:(lia)) as [Hrr Hmm].
        split; [eapply evstep_trans; eauto|lia].
    - split; [apply evstep_refl|assumption]. }
  unfold checkN; destruct (N_iter_until block_next (inl (x,blocks)) (N.succ blocks))
    as [[y budget]|u]; [discriminate|intros _; assumption].
Qed.

End Kernel.

Theorem halt_from_check blocks :
  Kernel.mass (Kernel.read Kernel.start)+4000*N.to_nat blocks < 2^60 ->
  Kernel.checkN blocks Kernel.start = true -> halts tm c0.
Proof.
  intros H E; eapply halts_evstep; [apply (Kernel.checkN_sound blocks Kernel.start H E)|apply init].
Qed.

Lemma checker_budget blocks : (blocks <= 1000000000)%N ->
  Kernel.mass (Kernel.read Kernel.start)+4000*N.to_nat blocks < 2^60.
Proof. change ((blocks <= 1000000000)%N -> 4+4000*N.to_nat blocks < 2^60); lia. Qed.

Definition result := Kernel.checkN 35000000%N Kernel.start.
Opaque Kernel.checkN.
Lemma result_sound : result = true -> halts tm c0.
Proof.
  intros H; apply (halt_from_check 35000000%N).
  - apply checker_budget; lia.
  - fold result; assumption.
Qed.

(* The only complete stopping computation: 35 million binary-counted blocks,
   each containing 1000 direct Uint63 next calls. *)
Transparent Kernel.checkN.
Lemma result_check : result = true.
Proof. Helper.native_check_eq. Time Qed.
Opaque Kernel.checkN result.

Theorem halt : halts tm c0.
Proof. apply result_sound, result_check. Qed.

End TM1.

Module Cubic1718.
Close Scope sym.
Inductive Frame (A : Type) :=
| FS (l : list (A*Sym)) (a b : A) (r : list A)
| FU (l : list (A*Sym)) (b : A) (r : list A)
| FT (l : list (A*Sym)) (a b : A) (r : list A)
| FY (l : list (A*Sym)) (a b : A) (r : list A).
Arguments FS {A}.
Arguments FU {A}.
Arguments FT {A}.
Arguments FY {A}.

Definition pad (x : Frame nat) :=
  match x with
  | FS l a b r => FS l a b (r++[0])
  | FU l b r => FU l b (r++[0])
  | FT l a b r => FT l a b (r++[0])
  | FY l a b r => FY l a b (r++[0])
  end.
Inductive Step : Frame nat -> Frame nat -> Prop :=
| Incs n l a b r : Step (FS l a (n*2+b) r) (FS l (a+n) b r)
| S0 l a c r : Step (FS l (1+a) 0 (c::r)) (FU l (a*2) ((2+c)::r))
| S000 l n c r : Step (FS ((n,0%sym)::l) 0 0 (c::r)) (FU l (n*2+2+c) r)
| S001 l n c r : Step (FS ((n,1%sym)::l) 0 0 (c::r))
    (FS ((0,0%sym)::(n,0%sym)::l) 0 c r)
| S00nil c r : Step (FS [] 0 0 (c::r)) (FU [] (2+c) r)
| S1 l a c r : Step (FS l a 1 (c::r)) (FY ((0,1%sym)::(a,1%sym)::l) 0 c r)
| U0 l n b r : Step (FU ((n,0%sym)::l) b r) (FT l n b r)
| U1 l n b r : Step (FU ((n,1%sym)::l) b r) (FU l (n*2) (b::r))
| Unil b r : Step (FU [] b r) (FT [] 0 b r)
| Tpos l a b r : Step (FT l (1+a) b r) (FY ((a,1%sym)::l) 1 b r)
| T00 l n b r : Step (FT ((n,0%sym)::l) 0 b r) (FY l (1+n) b r)
| T01 l n b r : Step (FT ((n,1%sym)::l) 0 b r) (FU l (n*2+2+b) r)
| Tnil b r : Step (FT [] 0 b r) (FY [] 1 b r)
| Y0 l a c r : Step (FY l a 0 (c::r)) (FU l (a*2+1+c) r)
| Y2 l a b r : Step (FY l a (2+b) r) (FS ((0,0%sym)::(a,0%sym)::l) 0 b r)
| Y10 l a c r : Step (FY l a 1 (0::c::r)) (FY ((a,0%sym)::l) 1 c r)
| TReturnPos l a b r : Step (FT l (1+a) (2+b) r)
    (FS ((0,0%sym)::(1,0%sym)::(a,1%sym)::l) 0 b r)
| TReturn00 l n b r : Step (FT ((n,0%sym)::l) 0 (2+b) r)
    (FS ((0,0%sym)::(1+n,0%sym)::l) 0 b r)
| TReturnNil b r : Step (FT [] 0 (2+b) r) (FS [(0,0%sym);(1,0%sym)] 0 b r)
| S1Return l a b r : Step (FS l a 1 ((2+b)::r))
    (FS ((0,0%sym)::(0,0%sym)::(0,1%sym)::(a,1%sym)::l) 0 b r)
| S000Return l n k c r : Step (FS ((n,0%sym)::(1+k,0%sym)::l) 0 0 (c::r))
    (FS ((0,0%sym)::(1,0%sym)::(k,1%sym)::l) 0 (n*2+c) r)
| Loops n l v b c r : Step (FS ((0,0%sym)::(v,0%sym)::l) 0 (n*4+b*2) (c::r))
    (FS ((0,0%sym)::(v+n,0%sym)::l) 0 (b*2) ((n*2+c)::r))
| Rpad x : Step x (pad x).

Definition Halt (x : Frame nat) :=
  match x with FY _ _ 1 ((S _)::_) => True | _ => False end.
Inductive Reach : Frame nat -> Frame nat -> Prop :=
| Reach_refl x : Reach x x
| Reach_step x y z : Step x y -> Reach y z -> Reach x z.
Definition Term x := exists y, Reach x y /\ Halt y.

Fixpoint left_mass (l : list (nat*Sym)) :=
  match l with [] => 0 | (n,_)::l => 2*n+1+left_mass l end.
Fixpoint right_mass (r : list nat) :=
  match r with [] => 0 | n::r => n+1+right_mass r end.
Definition mass (x : Frame nat) :=
  match x with
  | FS l a b r | FY l a b r => left_mass l+2*a+b+right_mass r
  | FU l b r => left_mass l+b+right_mass r
  | FT l a b r => left_mass l+2*a+b+right_mass r+1
  end.
Lemma right_mass_pad r : right_mass (r++[0]) = right_mass r+1.
Proof. induction r; cbn; lia. Qed.
Lemma mass_pad x : mass (pad x) = mass x+1.
Proof. destruct x; cbn [pad mass]; rewrite right_mass_pad; lia. Qed.
Lemma Step_mass x y : Step x y -> mass y <= mass x+1.
Proof. intro H; destruct H; cbn [mass left_mass right_mass]; try lia; rewrite mass_pad; lia. Qed.

Fixpoint check {C : Type} (next : C -> C) (stop : C -> bool) (fuel : nat) (x : C) :=
  if stop x then true else match fuel with 0 => false | S n => check next stop n (next x) end.
Definition seed17 : Frame nat := FY [] 1 0 [].
Definition seed18 : Frame nat := FY [(0,1%sym)] 0 0 [].
Definition join : Frame nat := FS [(0,0%sym);(2,0%sym)] 0 0 [0;4208].
End Cubic1718.

Module Cubic1718Uint63.
Import Cubic1718 PrimInt63.
Close Scope sym.
Notation int := PrimInt63.int.
Local Infix "+" := Uint63.add : uint63_scope.
Local Infix "-" := Uint63.sub : uint63_scope.
Local Infix "*" := Uint63.mul : uint63_scope.
Local Infix "/" := Uint63.div : uint63_scope.
Local Infix "mod" := Uint63.mod (at level 40, no associativity) : uint63_scope.
Local Infix "=?" := Uint63.eqb (at level 70, no associativity) : uint63_scope.
Local Infix "<=?" := Uint63.leb (at level 70, no associativity) : uint63_scope.
Definition state := Frame int.
Definition to_nat (x : int) := Z.to_nat (Uint63.to_Z x).
Definition read_left := map (fun p : int*Sym => (to_nat (fst p), snd p)).
Definition read_right := map to_nat.
Definition read (x : state) : Frame nat :=
  match x with
  | FS l a b r => FS (read_left l) (to_nat a) (to_nat b) (read_right r)
  | FU l b r => FU (read_left l) (to_nat b) (read_right r)
  | FT l a b r => FT (read_left l) (to_nat a) (to_nat b) (read_right r)
  | FY l a b r => FY (read_left l) (to_nat a) (to_nat b) (read_right r)
  end.

Local Open Scope uint63_scope.
Definition return_y l a b r : state :=
  if 2 <=? b then FS ((0,0%sym)::(a,0%sym)::l) 0 (b-2) r else FY l a b r.
Definition tick_t l a b r : state :=
  if a =? 0 then
    match l with
    | [] => return_y [] 1 b r
    | (n,0%sym)::l => return_y l (1+n) b r
    | (n,1%sym)::l => FU l (n*2+2+b) r
    end
  else return_y ((a-1,1%sym)::l) 1 b r.
Definition tick_s0 l a c r : state :=
  if a =? 0 then
    match l with
    | [] => FU [] (2+c) r
    | (n,1%sym)::l => FS ((0,0%sym)::(n,0%sym)::l) 0 c r
    | (n,0%sym)::l =>
      match l with
      | (m,0%sym)::l' =>
        if m =? 0 then FU l (n*2+2+c) r else
          FS ((0,0%sym)::(1,0%sym)::(m-1,1%sym)::l') 0 (n*2+c) r
      | _ => FU l (n*2+2+c) r
      end
    end
  else FU l ((a-1)*2) ((2+c)::r).
Definition tick_s l a b c r : state :=
  let a' := a+b/2 in
  if b mod 2 =? 0 then tick_s0 l a' c r
  else if 2 <=? c then
    FS ((0,0%sym)::(0,0%sym)::(0,1%sym)::(a',1%sym)::l) 0 (c-2) r
  else FY ((0,1%sym)::(a',1%sym)::l) 0 c r.
Definition tick (x : state) : state :=
  match x with
  | FS l a b [] => FS l a b [0]
  | FS l a b (c::r) =>
    match l with
    | (z,0%sym)::(v,0%sym)::l' =>
      if (if a =? 0 then if z =? 0 then
            if 4 <=? b then b mod 2 =? 0 else false
          else false else false) then
        let n := b/4 in
        FS ((0,0%sym)::(v+n,0%sym)::l') 0 (b mod 4) ((n*2+c)::r)
      else tick_s l a b c r
    | _ => tick_s l a b c r
    end
  | FU [] b r => FT [] 0 b r
  | FU ((n,0%sym)::l) b r => FT l n b r
  | FU ((n,1%sym)::l) b r => FU l (n*2) (b::r)
  | FT l a b r => tick_t l a b r
  | FY l a b r =>
    if b =? 0 then
      match r with [] => FY l a b [0] | c::r => FU l (a*2+1+c) r end
    else if b =? 1 then
      match r with
      | [] => FY l a b [0]
      | c::r' => if c =? 0 then
          match r' with
          | [] => FY l a b [c;0]
          | d::r'' => FY ((a,0%sym)::l) 1 d r''
          end
        else x
      end
    else return_y l a b r
  end.
Definition stop (x : state) :=
  match x with FY _ _ b (c::_) => andb (b =? 1) (negb (c =? 0)) | _ => false end.
Local Close Scope uint63_scope.

Lemma eqb_nat a b : (a =? b)%uint63 = (to_nat a =? to_nat b)%nat.
Proof. rewrite ZifyUint63.eqb_eq; unfold to_nat; lia. Qed.
Lemma leb_nat a b : (a <=? b)%uint63 = (to_nat a <=? to_nat b)%nat.
Proof. rewrite ZifyUint63.leb_le; unfold to_nat; lia. Qed.
Lemma add_nat a b : to_nat a+to_nat b < 2^63 ->
  to_nat (a+b)%uint63 = to_nat a+to_nat b.
Proof. unfold to_nat; rewrite Uint63.add_spec; unfold Uint63.wB, Uint63.size; intros; rewrite Z.mod_small; lia. Qed.
Lemma mul_nat a b : to_nat a*to_nat b < 2^63 ->
  to_nat (a*b)%uint63 = to_nat a*to_nat b.
Proof. unfold to_nat; rewrite Uint63.mul_spec; unfold Uint63.wB, Uint63.size; intros; rewrite Z.mod_small; lia. Qed.
Lemma sub_nat a b : to_nat b <= to_nat a ->
  to_nat (a-b)%uint63 = to_nat a-to_nat b.
Proof. unfold to_nat; rewrite Uint63.sub_spec; unfold Uint63.wB, Uint63.size; intros; rewrite Z.mod_small; lia. Qed.
Lemma div_nat a b : to_nat (a/b)%uint63 = to_nat a/to_nat b.
Proof. unfold to_nat; rewrite Uint63.div_spec, Z2Nat.inj_div; lia. Qed.
Lemma mod_nat a b : to_nat (a mod b)%uint63 = to_nat a mod to_nat b.
Proof. unfold to_nat; rewrite Uint63.mod_spec, Z2Nat.inj_mod; lia. Qed.

Lemma n0 : to_nat 0%uint63 = 0. Proof. reflexivity. Qed.
Lemma n1 : to_nat 1%uint63 = 1. Proof. reflexivity. Qed.
Lemma n2 : to_nat 2%uint63 = 2. Proof. reflexivity. Qed.
Lemma n4 : to_nat 4%uint63 = 4. Proof. reflexivity. Qed.
#[local] Hint Rewrite n0 n1 n2 n4 : uint_const.

Ltac arith := autorewrite with uint_const in *; lia.
Ltac uint :=
  repeat first [rewrite add_nat by uint | rewrite mul_nat by uint | rewrite sub_nat by uint
    | rewrite div_nat | rewrite mod_nat | progress autorewrite with uint_const]; try lia.
Ltac tests :=
  repeat first [rewrite eqb_nat | rewrite leb_nat]; autorewrite with uint_const;
  repeat match goal with
  | |- context[if Nat.eqb ?a ?b then _ else _] => destruct (Nat.eqb_spec a b)
  | |- context[if Nat.leb ?a ?b then _ else _] => destruct (Nat.leb_spec a b)
  end.

Lemma Reach_one x y : Step x y -> Reach x y.
Proof. intros; eapply Reach_step; [eassumption|constructor]. Qed.
Lemma Reach_trans x y z : Reach x y -> Reach y z -> Reach x z.
Proof. intros H; induction H; intros; [assumption|eapply Reach_step; eauto]. Qed.

Ltac unfold_read := cbn [read read_left read_right map fst snd] in *; autorewrite with uint_const in *.
Ltac mass_arith := cbn [mass left_mass right_mass] in *; uint; arith.

Lemma return_y_spec l a b r :
  Reach (read (FY l a b r)) (read (return_y l a b r)) /\
  mass (read (return_y l a b r)) = mass (read (FY l a b r)).
Proof.
  unfold return_y; tests; unfold_read; uint; split.
  - apply Reach_one; applys_eq Y2; f_equal; lia.
  - mass_arith.
  - constructor.
  - reflexivity.
Qed.

Ltac ry_mass :=
  match goal with
  | |- context[mass (read (return_y ?l ?a ?b ?r))] => rewrite (proj2 (return_y_spec l a b r))
  end.
Ltac via_y rule :=
  split; [eapply Reach_trans; [|apply return_y_spec]; unfold_read; cbn [mass left_mass right_mass] in *; uint;
           apply Reach_one; applys_eq rule; f_equal; lia
         |ry_mass; unfold_read; mass_arith].

Lemma tick_t_spec l a b r : mass (read (FT l a b r))+1 < 2^60 ->
  Reach (read (FT l a b r)) (read (tick_t l a b r)) /\
  mass (read (tick_t l a b r)) <= mass (read (FT l a b r))+1.
Proof.
  intros H; unfold tick_t; tests.
  - destruct l as [|[n t] l].
    + via_y Tnil.
    + destruct t.
      * via_y T00.
      * unfold_read; cbn [mass left_mass right_mass] in H; uint; split.
        -- apply Reach_one; applys_eq T01; f_equal; lia.
        -- mass_arith.
  - via_y Tpos.
Qed.

Ltac direct rule :=
  unfold_read; cbn [mass left_mass right_mass] in *; uint; split;
    [apply Reach_one; applys_eq rule; repeat f_equal; lia|mass_arith].

Lemma tick_s0_spec l a c r : mass (read (FS l a 0%uint63 (c::r)))+1 < 2^60 ->
  Reach (read (FS l a 0%uint63 (c::r))) (read (tick_s0 l a c r)) /\
  mass (read (tick_s0 l a c r)) <= mass (read (FS l a 0%uint63 (c::r)))+1.
Proof.
  intros H; unfold tick_s0; tests.
  - destruct l as [|[n t] l].
    + direct S00nil.
    + destruct t.
      * destruct l as [|[m t] l].
        -- direct S000.
        -- destruct t; tests.
           ++ direct S000.
           ++ direct (S000Return (read_left l) (to_nat n) (to_nat m-1) (to_nat c) (read_right r)).
           ++ direct S000.
      * direct S001.
  - direct S0.
Qed.

Lemma tick_s_spec l a b c r : mass (read (FS l a b (c::r)))+1 < 2^60 ->
  Reach (read (FS l a b (c::r))) (read (tick_s l a b c r)) /\
  mass (read (tick_s l a b c r)) <= mass (read (FS l a b (c::r)))+1.
Proof.
  intros H; set (a' := (a+b/2)%uint63).
  assert (Ha : to_nat a' = to_nat a+to_nat b/2).
  { unfold a'; unfold_read; cbn [mass left_mass right_mass] in H; uint. }
  unfold tick_s; fold a'; rewrite eqb_nat, mod_nat; autorewrite with uint_const.
  destruct (Nat.eqb_spec (to_nat b mod 2) 0) as [Eb|Eb].
  - assert (HM : mass (read (FS l a' 0%uint63 (c::r))) = mass (read (FS l a b (c::r)))).
    { unfold_read; mass_arith. }
    destruct (tick_s0_spec l a' c r ltac:(rewrite HM; assumption)) as [Hr Hm].
    split.
    + eapply Reach_trans; [|apply Hr]. unfold_read.
      apply Reach_one; applys_eq (Incs (to_nat b/2) (read_left l) (to_nat a) 0 (to_nat c::read_right r));
        repeat f_equal; lia.
    + rewrite HM in Hm; assumption.
  - assert (Eone : to_nat b mod 2 = 1) by lia.
    tests; unfold_read; cbn [mass left_mass right_mass] in H; uint; split.
    + eapply Reach_step with (y := FS (read_left l) (to_nat a') 1 (to_nat c::read_right r)).
      * applys_eq (Incs (to_nat b/2) (read_left l) (to_nat a) 1 (to_nat c::read_right r)); repeat f_equal; lia.
      * apply Reach_one; applys_eq S1Return; repeat f_equal; lia.
    + mass_arith.
    + eapply Reach_step with (y := FS (read_left l) (to_nat a') 1 (to_nat c::read_right r)).
      * applys_eq (Incs (to_nat b/2) (read_left l) (to_nat a) 1 (to_nat c::read_right r)); repeat f_equal; lia.
      * apply Reach_one, S1.
    + mass_arith.
Qed.

Lemma stop_sound x : stop x = true -> Halt (read x).
Proof.
  destruct x as [l a b r|l b r|l a b r|l a b r]; try discriminate.
  destruct r as [|c r]; [discriminate|].
  unfold stop; rewrite Bool.andb_true_iff; intros [Hb Hc].
  rewrite eqb_nat in Hb, Hc; autorewrite with uint_const in *.
  apply Nat.eqb_eq in Hb; apply Bool.negb_true_iff in Hc; apply Nat.eqb_neq in Hc.
  unfold_read; unfold Halt; rewrite Hb.
  destruct (to_nat c); [lia|trivial].
Qed.

Lemma loops_spec l a z v b c r :
  to_nat a = 0 -> to_nat z = 0 -> to_nat b mod 2 = 0 ->
  mass (read (FS ((z,0%sym)::(v,0%sym)::l) a b (c::r)))+1 < 2^60 ->
  let y := FS ((0%uint63,0%sym)::((v+b/4)%uint63,0%sym)::l) 0%uint63
    (b mod 4)%uint63 (((b/4)*2+c)%uint63::r) in
  Reach (read (FS ((z,0%sym)::(v,0%sym)::l) a b (c::r))) (read y) /\
  mass (read y) <= mass (read (FS ((z,0%sym)::(v,0%sym)::l) a b (c::r)))+1.
Proof.
  intros Ha Hz Hb H; cbn zeta; unfold_read; cbn [mass left_mass right_mass] in H; uint; split.
  - apply Reach_one; applys_eq (Loops (to_nat b/4) (read_left l) (to_nat v)
      ((to_nat b mod 4)/2) (to_nat c) (read_right r));
      repeat first [solve [lia] | progress f_equal].
  - mass_arith.
Qed.

Ltac padding := split; [apply Reach_one, Rpad|unfold_read; mass_arith].

Lemma tick_spec x : mass (read x)+1 < 2^60 ->
  Reach (read x) (read (tick x)) /\ mass (read (tick x)) <= mass (read x)+1.
Proof.
  intros H; destruct x as [l a b r|l b r|l a b r|l a b r].
  - destruct r as [|c r]; [cbn [tick]; padding|].
    destruct l as [|[z t] l]; [apply tick_s_spec; assumption|].
    destruct t; [|apply tick_s_spec; assumption].
    destruct l as [|[v t] l]; [apply tick_s_spec; assumption|].
    destruct t; [|apply tick_s_spec; assumption].
    cbn [tick]; tests; try (apply tick_s_spec; assumption).
    apply loops_spec; try assumption.
    rewrite mod_nat, n2 in *; assumption.
  - destruct l as [|[n t] l]; cbn [tick].
    + direct Unil.
    + destruct t; [direct U0|direct U1].
  - apply tick_t_spec; assumption.
  - cbn [tick]; rewrite eqb_nat, n0; destruct (Nat.eqb_spec (to_nat b) 0).
    + destruct r as [|c r]; [padding|direct Y0].
    + rewrite eqb_nat, n1; destruct (Nat.eqb_spec (to_nat b) 1).
      * destruct r as [|c r]; [padding|].
        rewrite eqb_nat, n0; destruct (Nat.eqb_spec (to_nat c) 0).
        -- destruct r as [|d r]; [padding|direct Y10].
        -- split; [constructor|lia].
      * destruct (return_y_spec l a b r); split; [assumption|lia].
Qed.

(* A batch always performs its first tick, including on FS. Later FS frames
   return immediately; exhausting the small internal fuel is not a halt. *)
Fixpoint resume (fuel : nat) (x : state) : state :=
  match fuel with
  | 0 => x
  | S n => if stop x then x else
      match x with FS _ _ _ _ => x | _ => resume n (tick x) end
  end.
Definition next x := if stop x then x else resume 15 (tick x).
Definition run := check next stop.

Lemma resume_spec fuel x : mass (read x)+fuel < 2^60 ->
  Reach (read x) (read (resume fuel x)) /\ mass (read (resume fuel x)) <= mass (read x)+fuel.
Proof.
  revert x; induction fuel; intros x H; cbn [resume].
  - split; [constructor|lia].
  - destruct (stop x); [split; [constructor|lia]|].
    destruct (tick_spec x ltac:(lia)) as [Hr Hm].
    destruct (IHfuel (tick x) ltac:(lia)) as [Hrr Hmm].
    destruct x; split; try apply Reach_refl; try lia;
      eapply Reach_trans; eauto.
Qed.

Lemma next_spec x : mass (read x)+16 < 2^60 ->
  Reach (read x) (read (next x)) /\ mass (read (next x)) <= mass (read x)+16.
Proof.
  intros H; unfold next; destruct (stop x); [split; [constructor|lia]|].
  destruct (tick_spec x ltac:(lia)) as [Hr Hm].
  destruct (resume_spec 15 (tick x) ltac:(lia)) as [Hrr Hmm].
  split; [eapply Reach_trans; eauto|lia].
Qed.

End Cubic1718Uint63.

Module Cubic1718Prefixes.
Import Cubic1718 Cubic1718Uint63 PrimInt63.
Close Scope sym.
Fixpoint advance (fuel : nat) (x : state) :=
  match fuel with 0 => x | S n => advance n (next x) end.
Lemma advance_spec fuel x : mass (read x)+16*fuel < 2^60 ->
  Reach (read x) (read (advance fuel x)) /\
  mass (read (advance fuel x)) <= mass (read x)+16*fuel.
Proof.
  revert x; induction fuel; intros x H; cbn [advance].
  - split; [constructor|lia].
  - destruct (next_spec x ltac:(lia)) as [Hr Hm].
    destruct (IHfuel (next x) ltac:(lia)) as [Hrr Hmm].
    split; [eapply Reach_trans; eauto|lia].
Qed.

Definition start17 : state := FY [] 1%uint63 0%uint63 [].
Definition start18 : state := FY [(0%uint63,1%sym)] 0%uint63 0%uint63 [].
Definition common : state :=
  FS [(0%uint63,0%sym);(2%uint63,0%sym)] 0%uint63 0%uint63 [0%uint63;4208%uint63].

Lemma read_start17 : read start17 = seed17.
Proof. reflexivity. Qed.
Lemma read_start18 : read start18 = seed18.
Proof. reflexivity. Qed.
Lemma read_common : read common = join.
Proof. vm_compute; reflexivity. Qed.

Lemma prefix17_compute : advance 11660 start17 = common.
Proof. vm_compute; reflexivity. Qed.
Lemma prefix18_compute : advance 11759 start18 = common.
Proof. vm_compute; reflexivity. Qed.

Lemma prefix17_sound : Reach seed17 join.
Proof.
  destruct (advance_spec 11660 start17 ltac:(change (2+16*(116*100+60) < 2^60); lia)) as [H _].
  rewrite prefix17_compute, read_start17, read_common in H; assumption.
Qed.
Lemma prefix18_sound : Reach seed18 join.
Proof.
  destruct (advance_spec 11759 start18 ltac:(change (1+16*(117*100+59) < 2^60); lia)) as [H _].
  rewrite prefix18_compute, read_start18, read_common in H; assumption.
Qed.

(* The large external fuel is binary N. Only a constant 1000-next block
   uses nat; N.to_nat and the 2^60 bound occur exclusively in proofs. *)
Definition block_next (s : state*N) : (state*N)+unit :=
  let '(x,budget) := s in
  if stop x then inr tt else
  match budget with
  | N0 => inl s
  | Npos _ => inl (advance 1000 x, N.pred budget)
  end.
Definition checkN (blocks : N) (x : state) :=
  match N_iter_until block_next (inl (x,blocks)) (N.succ blocks) with
  | inl _ => false | inr _ => true
  end.

Theorem checkN_sound blocks x : mass (read x)+(16*1000)*N.to_nat blocks < 2^60 ->
  checkN blocks x = true -> Term (read x).
Proof.
  intros H.
  assert (HI : match N_iter_until block_next (inl (x,blocks)) (N.succ blocks) with
    | inl (y,budget) => Reach (read x) (read y) /\
        mass (read y)+(16*1000)*N.to_nat budget < 2^60
    | inr _ => Term (read x)
    end).
  { eapply N_iter_until_spec with
      (P := fun s => let '(y,budget) := s in Reach (read x) (read y) /\
        mass (read y)+(16*1000)*N.to_nat budget < 2^60).
    - intros [y budget] [Hr Hm]; unfold block_next; destruct (stop y) eqn:E.
      + exists (read y); split; [apply Hr|apply stop_sound, E].
      + destruct budget as [|p]; [split; assumption|].
        destruct (advance_spec 1000 y ltac:(lia)) as [Hrr Hmm].
        split; [eapply Reach_trans; eauto|lia].
    - split; [constructor|assumption]. }
  unfold checkN; destruct (N_iter_until block_next (inl (x,blocks)) (N.succ blocks))
    as [[y budget]|u]; [discriminate|intros _; assumption].
Qed.

Lemma common_mass : mass (read common) = 4216.
Proof. vm_compute; reflexivity. Qed.
Lemma result_budget blocks : (blocks <= 10000000)%N ->
  mass (read common)+(16*1000)*N.to_nat blocks < 2^60.
Proof. intros H; rewrite common_mass; lia. Qed.
Definition result := checkN 10000000%N common.
Opaque checkN.
Lemma result_sound : result = true -> Term join.
Proof.
  intros H; rewrite <- read_common; apply (checkN_sound 10000000%N common).
  - apply result_budget, N.le_refl.
  - fold result; assumption.
Qed.
(* The sole long calculation: 10^7 blocks, each at most 1000 next calls.
   The explicit halt predicate is tested even after the final block. *)
Transparent checkN.
Lemma common_check : result = true.
Proof. Helper.native_check_eq. Time Qed.
Opaque checkN result.
End Cubic1718Prefixes.

Module TM17.
Import Cubic1718 Cubic1718Uint63 Cubic1718Prefixes.
Open Scope sym.
Definition tm := Eval compute in (TM_from_str "1RB0RE_0RC---_1LD0RA_0LA0LD_1LC1RF_1RC0RE").
Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Fixpoint LC (l:list (nat*Sym)) := match l with []=>0inf | (n,t)::l=>LC l <* <[1;0]^^n <* [t] end.
Fixpoint RC r := match r with []=>0inf | n::r=>[0] *> [1]^^n *> RC r end.
Definition S l a b r := LC l <* <[1;0]^^a {{E}}> [1]^^b *> RC r.
Definition U l b r := LC l <{{D}} [1]^^b *> RC r.
Definition T l a b r := LC l <* <[1;0]^^a <{{A}} [0] *> [1]^^b *> RC r.
Definition Y l a b r := LC l <* <[1;0]^^a {{C}}> [1]^^b *> RC r.
Definition W l a b r := LC l <* <[1;0]^^a {{A}}> [1]^^b *> RC r.
Close Scope sym.
Lemma Rblank r: RC r = RC (r++[0]).
Proof. induction r; cbn; [rewrite <- const_unfold; reflexivity|now rewrite <- IHr]. Qed.
Lemma Inc l a b r: S l a (2+b) r -->* S l (1+a) b r.
Proof. es. Qed.
Lemma Incs n l a b r: S l a (n*2+b) r -->* S l (a+n) b r.
Proof. gen a b. ind n Inc. Qed.
Lemma S0 l a c r: S l (1+a) 0 (c::r) -->* U l (a*2) ((2+c)::r).
Proof. es. Qed.
Lemma S000 l n c r: S ((n,0%sym)::l) 0 0 (c::r) -->* U l (n*2+2+c) r.
Proof. es. Qed.
Lemma S001 l n c r: S ((n,1%sym)::l) 0 0 (c::r) -->* W ((n,0%sym)::l) 0 (1+c) r.
Proof. es. Qed.
Lemma S00nil c r: S [] 0 0 (c::r) -->* U [] (2+c) r.
Proof. es. Qed.
Lemma S1 l a c r: S l a 1 (c::r) -->* Y ((0,1%sym)::(a,1%sym)::l) 0 c r.
Proof. es. Qed.
Lemma U0 l n b r: U ((n,0%sym)::l) b r -->* T l n b r.
Proof. es. Qed.
Lemma U1 l n b r: U ((n,1%sym)::l) b r -->* U l (n*2) (b::r).
Proof. es. Qed.
Lemma Unil b r: U [] b r -->* T [] 0 b r.
Proof. es. Qed.
Lemma Tpos l a b r: T l (1+a) b r -->* Y ((a,1%sym)::l) 1 b r.
Proof. es. Qed.
Lemma T00 l n b r: T ((n,0%sym)::l) 0 b r -->* Y l (1+n) b r.
Proof. es. Qed.
Lemma T01 l n b r: T ((n,1%sym)::l) 0 b r -->* S ((n,0%sym)::l) 0 0 (b::r).
Proof. es. Qed.
Lemma Tnil b r: T [] 0 b r -->* Y [] 1 b r.
Proof. es. Qed.
Lemma Y0 l a c r: Y l a 0 (c::r) -->* U l (a*2+1+c) r.
Proof. es. Qed.
Lemma Y1 l a b r: Y l a (1+b) r -->* W ((a,0%sym)::l) 0 b r.
Proof. es. Qed.
Lemma W1 l a b r: W l a (1+b) r -->* S ((a,0%sym)::l) 0 b r.
Proof. es. Qed.
Lemma W00 l a c r: W l a 0 (0::c::r) -->* Y l (1+a) c r.
Proof. es. Qed.
Lemma HW01 l a c r: halts tm (W l a 0 ((1+c)::r)).
Proof. unfold W, RC; cbn; esx. Qed.
(* Paired right return. These eliminate transient Y/W and T frames. *)
Lemma Return2 l a b r: Y l a (2+b) r -->*
  S ((0,0%sym)::(a,0%sym)::l) 0 b r.
Proof. follow (Y1 l a (1+b) r). follow (W1 ((a,0%sym)::l) 0 b r). finish. Qed.
Lemma TReturnPos l a b r: T l (1+a) (2+b) r -->*
  S ((0,0%sym)::(1,0%sym)::(a,1%sym)::l) 0 b r.
Proof. follow (Tpos l a (2+b) r). follow (Return2 ((a,1%sym)::l) 1 b r). finish. Qed.
Lemma TReturn00 l n b r: T ((n,0%sym)::l) 0 (2+b) r -->*
  S ((0,0%sym)::(1+n,0%sym)::l) 0 b r.
Proof. follow (T00 l n (2+b) r). follow (Return2 l (1+n) b r). finish. Qed.
Lemma TReturnNil b r: T [] 0 (2+b) r -->* S [(0,0%sym);(1,0%sym)] 0 b r.
Proof. follow (Tnil (2+b) r). follow (Return2 [] 1 b r). finish. Qed.
Lemma S1Return l a b r: S l a 1 ((2+b)::r) -->*
  S ((0,0%sym)::(0,0%sym)::(0,1%sym)::(a,1%sym)::l) 0 b r.
Proof. follow (S1 l a (2+b) r). follow (Return2 ((0,1%sym)::(a,1%sym)::l) 0 b r). finish. Qed.
Lemma S000Return l n m c r: S ((n,0%sym)::(1+m,0%sym)::l) 0 0 (c::r) -->*
  S ((0,0%sym)::(1,0%sym)::(m,1%sym)::l) 0 (n*2+c) r.
Proof.
  follow (S000 ((1+m,0%sym)::l) n c r). follow (U0 l (1+m) (n*2+2+c) r).
  follow (TReturnPos l m (n*2+c) r). finish.
Qed.
Lemma Loop l v b c r: S ((0,0%sym)::(v,0%sym)::l) 0 (4+b*2) (c::r) -->*
  S ((0,0%sym)::(1+v,0%sym)::l) 0 (b*2) ((2+c)::r).
Proof. es. Qed.
Lemma Loops n l v b c r: S ((0,0%sym)::(v,0%sym)::l) 0 (n*4+b*2) (c::r) -->*
  S ((0,0%sym)::(v+n,0%sym)::l) 0 (b*2) ((n*2+c)::r).
Proof.
  gen v c. induction n; intros; [finish|].
  follow (Loop l v (n*2+b) c r). follow (IHn (1+v) (2+c)). finish.
Qed.
Lemma init: c0 -->* W [] 0 0 [].
Proof. finish. Qed.

Lemma S001_17 l n c r : S ((n,1%sym)::l) 0 0 (c::r)
  -[tm]->* S ((0,0%sym)::(n,0%sym)::l) 0 c r.
Proof. follow (S001 l n c r). follow (W1 ((n,0%sym)::l) 0 c r). finish. Qed.
Lemma T01_17 l n b r : T ((n,1%sym)::l) 0 b r
  -[tm]->* U l (n*2+2+b) r.
Proof. follow (T01 l n b r). follow (S000 l n b r). finish. Qed.
Lemma Y10_17 l a c r : Y l a 1 (0::c::r)
  -[tm]->* Y ((a,0%sym)::l) 1 c r.
Proof. follow (Y1 l a 0 (0::c::r)). follow (W00 ((a,0%sym)::l) 0 c r). finish. Qed.
Lemma halt_17 l a c r : halts tm (Y l a 1 ((1+c)::r)).
Proof. eapply halts_evstep; [apply HW01|apply Y1]. Qed.

Definition denote (x : Frame nat) :=
  match x with
  | FS l a b r => S l a b r
  | FU l b r => U l b r
  | FT l a b r => T l a b r
  | FY l a b r => Y l a b r
  end.
Lemma denote_pad x : denote (pad x) = denote x.
Proof.
  destruct x; cbn [pad denote]; unfold S, U, T, Y;
    rewrite <- Rblank; reflexivity.
Qed.
Lemma Step_sound x y : Step x y -> denote x -->* denote y.
Proof.
  intro H; destruct H; cbn [denote];
    try solve [eauto using Incs, S0, S000, S001_17, S00nil, S1, U0, U1, Unil, Tpos, T00, T01_17, Tnil, Y0, Return2, Y10_17, TReturnPos, TReturn00, TReturnNil, S1Return, S000Return, Loops];
    rewrite denote_pad; apply evstep_refl.
Qed.
Lemma Halt_sound x : Halt x -> halts tm (denote x).
Proof.
  destruct x as [l a b r|l b r|l a b r|l a b r]; cbn [Halt]; try tauto.
  destruct b as [|[|b]], r as [|[|c] r]; cbn; try tauto.
  intros _; apply halt_17.
Qed.
Lemma Reach_sound x y : Reach x y -> denote x -->* denote y.
Proof.
  intro H; induction H; [apply evstep_refl|].
  eapply evstep_trans; [apply Step_sound; eassumption|assumption].
Qed.
Lemma seed_sound : c0 -->* denote seed17.
Proof.
  follow init. cbn [denote seed17].
  unfold W at 1; rewrite (Rblank []); cbn [app].
  rewrite (Rblank [0]); apply W00.
Qed.
Theorem halt : halts tm c0.
Proof.
  destruct (result_sound common_check) as [y [Hr Hh]].
  eapply halts_evstep; [apply Halt_sound; apply Hh|].
  follow seed_sound. apply Reach_sound.
  eapply Reach_trans; [apply prefix17_sound|apply Hr].
Qed.
End TM17.

Module TM18.
Import Cubic1718 Cubic1718Uint63 Cubic1718Prefixes.
Open Scope sym.
Definition tm := Eval compute in (TM_from_str "1RB0RF_1LC0RD_0LD0LC_1RE0RF_0RB---_1LB1RA").
Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Fixpoint LC (l:list (nat*Sym)) := match l with []=>0inf | (n,t)::l=>LC l <* <[1;0]^^n <* [t] end.
Fixpoint RC r := match r with []=>0inf | n::r=>[0] *> [1]^^n *> RC r end.
Definition S l a b r := LC l <* <[1;0]^^a {{F}}> [1]^^b *> RC r.
Definition V l b r := LC l <{{C}} [1]^^b *> RC r.
Definition T l a b r := LC l <* <[1;0]^^a <{{D}} [0] *> [1]^^b *> RC r.
Definition W l a b r := LC l <* <[1;0]^^a {{B}}> [1]^^b *> RC r.
Close Scope sym.
Lemma Rblank r: RC r = RC (r++[0]).
Proof. induction r; cbn; [rewrite <- const_unfold; reflexivity|now rewrite <- IHr]. Qed.
Lemma Inc l a b r: S l a (2+b) r -->* S l (1+a) b r.
Proof. es. Qed.
Lemma Incs n l a b r: S l a (n*2+b) r -->* S l (a+n) b r.
Proof. gen a b. ind n Inc. Qed.
Lemma S0 l a c r: S l (1+a) 0 (c::r) -->* V l (a*2) ((2+c)::r).
Proof. es. Qed.
Lemma S000 l n c r: S ((n,0%sym)::l) 0 0 (c::r) -->* V l (n*2+2+c) r.
Proof. es. Qed.
Lemma S001 l n c r: S ((n,1%sym)::l) 0 0 (c::r) -->* S ((0,0%sym)::(n,0%sym)::l) 0 c r.
Proof. es. Qed.
Lemma S00nil c r: S [] 0 0 (c::r) -->* V [] (2+c) r.
Proof. es. Qed.
Lemma S1 l a c r: S l a 1 (c::r) -->* W ((0,1%sym)::(a,1%sym)::l) 0 c r.
Proof. es. Qed.
Lemma V0 l n b r: V ((n,0%sym)::l) b r -->* T l n b r.
Proof. es. Qed.
Lemma V1 l n b r: V ((n,1%sym)::l) b r -->* V l (n*2) (b::r).
Proof. es. Qed.
Lemma Vnil b r: V [] b r -->* T [] 0 b r.
Proof. es. Qed.
Lemma Tpos l a b r: T l (1+a) b r -->* W ((a,1%sym)::l) 1 b r.
Proof. es. Qed.
Lemma T00 l n b r: T ((n,0%sym)::l) 0 b r -->* W l (1+n) b r.
Proof. es. Qed.
Lemma T01 l n b r: T ((n,1%sym)::l) 0 b r -->* V l (n*2+2+b) r.
Proof. es. Qed.
Lemma Tnil b r: T [] 0 b r -->* W [] 1 b r.
Proof. es. Qed.
Lemma W0 l a c r: W l a 0 (c::r) -->* V l (a*2+1+c) r.
Proof. es. Qed.
Lemma W2 l a b r: W l a (2+b) r -->* S ((0,0%sym)::(a,0%sym)::l) 0 b r.
Proof. es. Qed.
Lemma W10 l a c r: W l a 1 (0::c::r) -->* W ((a,0%sym)::l) 1 c r.
Proof. es. Qed.
Lemma HW11 l a c r: halts tm (W l a 1 ((1+c)::r)).
Proof. unfold W, RC; cbn; esx. Qed.
(* Same paired T return as TM17, but W2 replaces Y1 followed by W1. *)
Lemma TReturnPos l a b r: T l (1+a) (2+b) r -->*
  S ((0,0%sym)::(1,0%sym)::(a,1%sym)::l) 0 b r.
Proof. follow (Tpos l a (2+b) r). follow (W2 ((a,1%sym)::l) 1 b r). finish. Qed.
Lemma TReturn00 l n b r: T ((n,0%sym)::l) 0 (2+b) r -->*
  S ((0,0%sym)::(1+n,0%sym)::l) 0 b r.
Proof. follow (T00 l n (2+b) r). follow (W2 l (1+n) b r). finish. Qed.
Lemma TReturnNil b r: T [] 0 (2+b) r -->* S [(0,0%sym);(1,0%sym)] 0 b r.
Proof. follow (Tnil (2+b) r). follow (W2 [] 1 b r). finish. Qed.
Lemma S1Return l a b r: S l a 1 ((2+b)::r) -->*
  S ((0,0%sym)::(0,0%sym)::(0,1%sym)::(a,1%sym)::l) 0 b r.
Proof. follow (S1 l a (2+b) r). follow (W2 ((0,1%sym)::(a,1%sym)::l) 0 b r). finish. Qed.
Lemma S000Return l n m c r: S ((n,0%sym)::(1+m,0%sym)::l) 0 0 (c::r) -->*
  S ((0,0%sym)::(1,0%sym)::(m,1%sym)::l) 0 (n*2+c) r.
Proof.
  follow (S000 ((1+m,0%sym)::l) n c r). follow (V0 l (1+m) (n*2+2+c) r).
  follow (TReturnPos l m (n*2+c) r). finish.
Qed.
Lemma Loop l v b c r: S ((0,0%sym)::(v,0%sym)::l) 0 (4+b*2) (c::r) -->*
  S ((0,0%sym)::(1+v,0%sym)::l) 0 (b*2) ((2+c)::r).
Proof. es. Qed.
Lemma Loops n l v b c r: S ((0,0%sym)::(v,0%sym)::l) 0 (n*4+b*2) (c::r) -->*
  S ((0,0%sym)::(v+n,0%sym)::l) 0 (b*2) ((n*2+c)::r).
Proof.
  gen v c. induction n; intros; [finish|].
  follow (Loop l v (n*2+b) c r). follow (IHn (1+v) (2+c)). finish.
Qed.
Lemma init: c0 -->* W [(0,1%sym)] 0 0 [].
Proof. es. Qed.

Definition denote (x : Frame nat) :=
  match x with
  | FS l a b r => S l a b r
  | FU l b r => V l b r
  | FT l a b r => T l a b r
  | FY l a b r => W l a b r
  end.
Lemma denote_pad x : denote (pad x) = denote x.
Proof.
  destruct x; cbn [pad denote]; unfold S, V, T, W;
    rewrite <- Rblank; reflexivity.
Qed.
Lemma Step_sound x y : Step x y -> denote x -->* denote y.
Proof.
  intro H; destruct H; cbn [denote];
    try solve [eauto using Incs, S0, S000, S001, S00nil, S1, V0, V1, Vnil, Tpos, T00, T01, Tnil, W0, W2, W10, TReturnPos, TReturn00, TReturnNil, S1Return, S000Return, Loops];
    rewrite denote_pad; apply evstep_refl.
Qed.
Lemma Halt_sound x : Halt x -> halts tm (denote x).
Proof.
  destruct x as [l a b r|l b r|l a b r|l a b r]; cbn [Halt]; try tauto.
  destruct b as [|[|b]], r as [|[|c] r]; cbn; try tauto.
  intros _; apply HW11.
Qed.
Lemma Reach_sound x y : Reach x y -> denote x -->* denote y.
Proof.
  intro H; induction H; [apply evstep_refl|].
  eapply evstep_trans; [apply Step_sound; eassumption|assumption].
Qed.
Lemma seed_sound : c0 -->* denote seed18.
Proof.
  apply init.
Qed.
Theorem halt : halts tm c0.
Proof.
  destruct (result_sound common_check) as [y [Hr Hh]].
  eapply halts_evstep; [apply Halt_sound; apply Hh|].
  follow seed_sound. apply Reach_sound.
  eapply Reach_trans; [apply prefix18_sound|apply Hr].
Qed.
End TM18.


Module TM39.
Import BigUint.
Open Scope sym.
Definition tm := Eval compute in (TM_from_str "1LB0LB_1LC0LD_1RD1LC_1LF0RE_1RC1RE_---0LA").
Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Fixpoint LC l := match l with []=>0inf | n::l=>LC l <* [1]^^n <* [0] end.
Fixpoint RC r := match r with []=>0inf | n::r=>[0;0;0] *> [1]^^n *> RC r end.
Definition S l a b r := LC l <* [1]^^a <{{B}} [0;0] *> [1]^^b *> RC r.
Close Scope sym.
Lemma Lblank l: LC l = LC (l++[0]).
Proof. induction l; cbn; [rewrite <- const_unfold; reflexivity|now rewrite <- IHl]. Qed.
Lemma Rblank r: RC r = RC (r++[0]).
Proof. induction r; cbn; [repeat rewrite <- const_unfold; reflexivity|now rewrite <- IHr]. Qed.
Lemma Spos l a b r: S l (2+a) b r -->* S (a::l) 0 (1+b) r.
Proof. es. Qed.
Lemma S12 l a b r: S ((2+a)::l) 1 b r -->* S l a 1 (b::r).
Proof. es. Qed.
Lemma HS10 l b r: halts tm (S (0::l) 1 b r).
Proof. destruct l; unfold S, LC; cbn; esx. Qed.
Lemma S110 l a b c r: S (1::0::a::b::l) 1 c r -->* S ((2+b)::l) (2+a) (1+c) r.
Proof. es. Qed.
Lemma S112 l a b r: S (1::(2+a)::l) 1 b r -->* S ((2+a)::l) 2 (1+b) r.
Proof. es. Qed.
Lemma S01 l a b c r: S (a::b::l) 0 1 (c::r) -->* S ((2+a)::(1+b)::l) 0 (1+c) r.
Proof. es. Qed.
Lemma S03 l a b c d r: S (a::b::l) 0 (3+c) (d::r) -->* S (c::(2+a)::(1+b)::l) 0 (2+d) r.
Proof. es. Qed.
Lemma S02 l a b c r: S (a::b::l) 0 2 (c::r) -->* S ((1+b)::l) a 1 ((1+c)::r).
Proof. es. Qed.
Lemma Inc l a b c r: S ((2+a)::b::l) 0 2 (c::r) -->* S (a::(1+b)::l) 0 2 ((1+c)::r).
Proof. es. Qed.
Lemma Incs n l a b c r: S ((a+n*2)::b::l) 0 2 (c::r) -->* S (a::(b+n)::l) 0 2 ((c+n)::r).
Proof.
  gen a b c. induction n; intros; [finish|].
  eapply evstep_trans; [applys_eq (Inc l (a+n*2) b c r); flia|].
  applys_eq (IHn a (1+b) (1+c)); flia.
Qed.
Lemma init: c0 -->* S [1] 1 1 [].
Proof. unfold S, LC, RC; cbn; esx. Qed.

Definition N2 := Eval compute in (of_nat 2).
Inductive State := cfg (l:list N') (a b:N') (r:list N').
Definition to_config x := match x with
| cfg l a b r => S (map to_nat l) (to_nat a) (to_nat b) (map to_nat r)
end.
Fixpoint pad k (l:list N') := match k with
| 0 => l
| Datatypes.S k => match l with []=>N0::pad k [] | a::l=>a::pad k l end
end.
Definition prep x := match x with cfg l a b r => cfg (pad 4 l) a b (pad 1 r) end.
Lemma LC_pad k l: LC (map to_nat (pad k l)) = LC (map to_nat l).
Proof. gen l. induction k; intros; cbn; [reflexivity|].
  destruct l; cbn; rewrite IHk; [rewrite <- const_unfold|]; reflexivity.
Qed.
Lemma RC_pad k l: RC (map to_nat (pad k l)) = RC (map to_nat l).
Proof. gen l. induction k; intros; cbn; [reflexivity|].
  destruct l; cbn; rewrite IHk; [repeat rewrite <- const_unfold|]; reflexivity.
Qed.
Lemma prep_eq x: to_config (prep x)=to_config x.
Proof. destruct x; cbn [prep to_config]. unfold S; rewrite LC_pad, RC_pad; reflexivity. Qed.

Definition edge x0 x1 x2 x3 l a b c r :=
let x:=cfg (x0::x1::x2::x3::l) a b (c::r) in
(match pred a with
| Some a1 => match pred a1 with
  | Some a2 => Some (cfg (a2::x0::x1::x2::x3::l) N0 (succ b) (c::r))
  | None => match pred x0 with
    | None => None
    | Some v1 => match pred v1 with
      | Some v2 => Some (cfg (x1::x2::x3::l) v2 N1 (b::c::r))
      | None => match pred x1 with
        | None => Some (cfg ((N2+x3)::l) (N2+x2) (succ b) (c::r))
        | Some w1 => match pred w1 with
          | None => Some x
          | Some _ => Some (cfg (x1::x2::x3::l) N2 (succ b) (c::r))
          end
        end
      end
    end
  end
| None => match pred b with
  | None => Some x
  | Some b1 => match pred b1 with
    | None => Some (cfg ((N2+x0)::succ x1::x2::x3::l) N0 (succ c) r)
    | Some b2 => match pred b2 with
      | Some b3 => Some (cfg (b3::(N2+x0)::succ x1::x2::x3::l) N0 (N2+c) r)
      | None => match pred x0 with
        | Some v1 => match pred v1 with
          | Some _ => match divmod_small x0 N2 with
            | Some (n,d) => Some (cfg (d::(x1+n)::x2::x3::l) N0 N2 ((c+n)::r))
            | None => Some x end
          | None => Some (cfg (succ x1::x2::x3::l) x0 N1 (succ c::r)) end
        | None => Some (cfg (succ x1::x2::x3::l) x0 N1 (succ c::r)) end
      end
    end
  end
end)%N'.
Definition tick x := match x with
| cfg (x0::x1::x2::x3::l) a b (c::r) => edge x0 x1 x2 x3 l a b c r
| _ => Some x
end.
Definition nxt x := tick (prep x).
Ltac des_pred := match goal with
| |- context[match pred ?a with _ => _ end] =>
  let H:=fresh "H" in pose proof (inj_pred a) as H; destruct (pred a)
end.
Ltac nums := rw_N';
  change (to_nat N0) with 0 in *; change (to_nat N1) with 1 in *;
  change (to_nat N2) with 2 in *;
  repeat match goal with H: to_nat ?a = _ |- context[to_nat ?a] => rewrite H end.
Lemma edge_spec x0 x1 x2 x3 l a b c r:
match edge x0 x1 x2 x3 l a b c r with
| Some y => to_config (cfg (x0::x1::x2::x3::l) a b (c::r)) -->* to_config y
| None => halts tm (to_config (cfg (x0::x1::x2::x3::l) a b (c::r)))
end.
Proof.
  unfold edge; repeat des_pred; cbn [to_config map]; nums; try solve [finish].
  all: try (destruct (divmod_small x0 N2) as [[n d]|] eqn:E; [|cbn [to_config map]; nums; finish];
    pose proof (inj_divmod_small _ _ _ _ E); cbn [to_config map]; nums;
    applys_eq (Incs (to_nat n) (map to_nat (x2::x3::l)) (to_nat d) (to_nat x1) (to_nat c) (map to_nat r)); flia).
  all: first [solve [applys_eq Spos; flia] | solve [applys_eq S12; flia] |
    solve [applys_eq HS10; flia] | solve [applys_eq S110; flia] |
    solve [applys_eq S112; flia] | solve [applys_eq S01; flia] |
    solve [applys_eq S02; flia] | solve [applys_eq S03; flia]].
Qed.
Lemma tick_spec x: match tick x with
| Some y => to_config x -->* to_config y | None => halts tm (to_config x) end.
Proof. destruct x as [l a b r]; unfold tick.
  do 4 (destruct l as [|? l]; [finish|]); destruct r; [finish|apply edge_spec].
Qed.
Lemma nxt_spec x: match nxt x with
| Some y => to_config x -->* to_config y | None => halts tm (to_config x) end.
Proof. unfold nxt. pose proof (tick_spec (prep x)) as H.
  destruct (tick (prep x)); rewrite prep_eq in H; exact H.
Qed.
Definition initial := cfg [N1] N1 N1 [].
Definition nxt' x := match nxt x with Some y=>inl y | None=>inr tt end.
Definition run fuel := N_iter_until nxt' (inl initial) fuel.
Definition check fuel := match run fuel with inr _=>true | _=>false end.
Lemma check_spec fuel: check fuel=true -> halts tm c0.
Proof.
  unfold check,run. intro H.
  assert (match N_iter_until nxt' (inl initial) fuel with
    | inl y => c0 -->* to_config y | inr _ => halts tm c0 end) as R.
  { apply N_iter_until_spec.
    - intros x Hx. unfold nxt'. pose proof (nxt_spec x) as E. destruct (nxt x).
      + eapply evstep_trans; eauto.
      + eapply halts_evstep; eauto.
    - apply init. }
  destruct (N_iter_until nxt' (inl initial) fuel); [discriminate|exact R].
Qed.
Theorem halt: halts tm c0.
Proof. apply (check_spec (10^8)%N). native_check_eq. Time Qed.
End TM39.

Module TM41.
Open Scope sym.
Definition tm := Eval compute in (TM_from_str "1RB1RA_1RC1LB_1LD0RA_1LA0LE_---0LF_0RC0LB").
Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).
Fixpoint LC l := match l with []=>0inf | n::l=>LC l <* [1]^^n <* [0] end.
Fixpoint RC r := match r with []=>0inf | n::r=>[0] *> [1]^^n *> RC r end.
Definition S l a b r := LC l <* [1]^^a <{{F}} [0;0] *> [1]^^b *> RC r.
Definition U l a r := LC l <{{B}} [1]^^a *> RC r.
Definition T l a r := LC l <* [1]^^a {{A}}> RC r.
Close Scope sym.
Lemma Inc l v a b r: S (v::l) (2+a) b r -->* S ((1+v)::l) a (1+b) r.
Proof. es. Qed.
Lemma Incs n l v a b r: S (v::l) (n*2+a) b r -->* S ((v+n)::l) a (b+n) r.
Proof. gen v a b. ind n Inc. Qed.
Lemma Sblank a b r: S [] a b r = S [0] a b r.
Proof. unfold S; cbn; rewrite <- const_unfold; reflexivity. Qed.
Lemma S1 l b r: S l 1 b r -->* U l 0 (0::0::b::r).
Proof. es. Qed.
Lemma S0 l v b r: S ((1+v)::l) 0 b r -->* T l (3+v) (b::r).
Proof. es. Qed.
Lemma S00 l v b r: S (0::v::l) 0 b r -->* U l (3+v) (b::r).
Proof. es. Qed.
Lemma S00nil b r: S [0] 0 b r -->* U [] 3 (b::r).
Proof. es. Qed.
Lemma Upos l v a r: U (v::l) (1+a) r -->* T ((1+v)::l) a r.
Proof. es. Qed.
Lemma Uposnil a r: U [] (1+a) r -->* T [1] a r.
Proof. es. Qed.
Lemma U0 l v c r: U ((1+v)::l) 0 (c::r) -->* S l v (1+c) r.
Proof. es. Qed.
Lemma U0nil l v: U ((1+v)::l) 0 [] -->* S l v 1 [].
Proof. es. Qed.
Lemma HU0 l r: halts tm (U (0::l) 0 r).
Proof. destruct l, r; unfold U, LC, RC; cbn; esx. Qed.
Lemma HUnil r: halts tm (U [] 0 r).
Proof. destruct r; unfold U, LC, RC; cbn; esx. Qed.
Lemma Tpos_progress l a c r: T l a ((1+c)::r) -->+ U l (2+a+c) r.
Proof. es. Qed.
Lemma Tpos l a c r: T l a ((1+c)::r) -->* U l (2+a+c) r.
Proof. apply progress_evstep, Tpos_progress. Qed.
Lemma T0pos l a c r: T l a (0::(1+c)::r) -->* T ((2+a)::l) c r.
Proof. es. Qed.
Lemma T00 l a c r: T l a (0::0::c::r) -->* S l a (1+c) r.
Proof. es. Qed.
Lemma T00nil l a: T l a [0;0] -->* S l a 1 [].
Proof. es. Qed.
Lemma T0nil l a: T l a [0] -->* S l a 1 [].
Proof. es. Qed.
Lemma Tnil l a: T l a [] -->* S l a 1 [].
Proof. es. Qed.
Lemma init: c0 -->* U [] 3 [1].
Proof. unfold U, LC, RC; cbn. esx. Qed.

Definition cap k := U [] (4+k*2) [0;1+k*2].
Lemma cap_step k: cap k -->+ cap (3+k).
Proof.
  unfold cap.
  follow Uposnil. follow T0pos. follow Tnil.
  follow (Incs k [1] (5+k*2) 0 1 []). follow S0. follow Tpos. follow Upos. follow Tnil.
  fold Nat.add.
  follow (Incs (4+k*2) [] 2 0 1 []). follow S0. follow Tpos. follow Uposnil. follow Tnil.
  fold Nat.add. follow (Incs (6+k*2) [] 1 1 1 []). follow S1. follow U0.
  fold Nat.add. rewrite Sblank. follow (Incs (3+k) [] 0 0 1 [0;7+k*2]). follow S0.
  applys_eq (Tpos_progress [] (5+k) (3+k) [0;7+k*2]); flia.
Qed.
Lemma cap_nonhalt k: ~halts tm (cap k).
Proof. apply (progress_nonhalt_simple tm _ cap k). intro j. exists (3+j). apply cap_step. Qed.

(* Only the finite prefix is computed. These unbounded binary counters are
   independent of the int64 implementation used to discover the loop. *)
Inductive State :=
| qS (l:list N) (a b:N) (r:list N)
| qU (l:list N) (a:N) (r:list N)
| qT (l:list N) (a:N) (r:list N).
Definition to_config x := match x with
| qS l a b r => S (map N.to_nat l) (N.to_nat a) (N.to_nat b) (map N.to_nat r)
| qU l a r => U (map N.to_nat l) (N.to_nat a) (map N.to_nat r)
| qT l a r => T (map N.to_nat l) (N.to_nat a) (map N.to_nat r)
end.
Definition edge l v b r (odd:bool) := (if odd then qU (v::l) 0 (0::0::b::r)
else if v =? 0 then match l with
| [] => qU [] 3 (b::r) | w::l => qU l (3+w) (b::r) end
else qT l (2+v) (b::r))%N.
Definition nxt x := (match x with
| qS l a b r => let n:=N.div2 a in
  match l with
  | [] => edge [] n (b+n) r (N.odd a)
  | v::l => edge l (v+n) (b+n) r (N.odd a) end
| qU l a r => if a =? 0 then match l with
  | [] => x
  | v::l => if v =? 0 then x else match r with
    | [] => qS l (N.pred v) 1 []
    | b::r => qS l (N.pred v) (1+b) r end end
  else match l with
  | [] => qT [1] (N.pred a) r
  | v::l => qT ((1+v)::l) (N.pred a) r end
| qT l a r => match r with
  | [] => qS l a 1 []
  | v::r => if v =? 0 then match r with
    | [] => qS l a 1 []
    | b::r => if b =? 0 then match r with
      | [] => qS l a 1 []
      | c::r => qS l a (1+c) r end
      else qT ((2+a)::l) (N.pred b) r end
    else qU l (1+a+v) r end
end)%N.
Ltac nums := repeat rewrite ?N2Nat.inj_add, ?N2Nat.inj_mul, ?N2Nat.inj_pred;
  cbn [N.to_nat N.b2n].
Ltac des_eqb := match goal with
| |- context[N.eqb ?a ?b] => let H:=fresh "H" in destruct (N.eqb a b) eqn:H;
  [apply N.eqb_eq in H | apply N.eqb_neq in H]
end.
Lemma edge_spec l v b r (odd:bool):
  S (N.to_nat v::map N.to_nat l) (if odd then 1 else 0) (N.to_nat b) (map N.to_nat r)
  -->* to_config (edge l v b r odd).
Proof.
  destruct odd; cbn [edge to_config map]; [apply S1|].
  des_eqb; [subst v; destruct l; cbn [to_config map]; nums|cbn [to_config map]; nums].
  - apply S00nil.
  - apply S00.
  - applys_eq (S0 (map N.to_nat l) (Nat.pred (N.to_nat v)) (N.to_nat b) (map N.to_nat r)); flia.
Qed.
Lemma nxt_spec x: to_config x -->* to_config (nxt x).
Proof.
  destruct x as [l a b r|l a r|l a r]; cbn [nxt].
  - pose proof (f_equal N.to_nat (N.div2_odd a)) as E.
    rewrite N2Nat.inj_add, N2Nat.inj_mul in E.
    destruct l as [|v l]; cbn [to_config map]; [rewrite Sblank|];
      eapply evstep_trans; [|apply edge_spec| |apply edge_spec].
    + nums. applys_eq (Incs (N.to_nat (N.div2 a)) [] 0
        (if N.odd a then 1 else 0) (N.to_nat b) (map N.to_nat r));
        destruct (N.odd a); cbn [N.b2n N.to_nat] in *; flia.
    + nums. applys_eq (Incs (N.to_nat (N.div2 a)) (map N.to_nat l) (N.to_nat v)
        (if N.odd a then 1 else 0) (N.to_nat b) (map N.to_nat r));
        destruct (N.odd a); cbn [N.b2n N.to_nat] in *; flia.
  - des_eqb.
    + subst a; destruct l as [|v l]; [finish|]. des_eqb; [finish|].
      destruct r; cbn [to_config map]; nums;
        first [solve [applys_eq U0; flia] | solve [applys_eq U0nil; flia]].
    + destruct l; cbn [to_config map]; nums;
        first [solve [applys_eq Upos; flia] | solve [applys_eq Uposnil; flia]].
  - destruct r as [|v r]; [apply Tnil|]. des_eqb.
    + subst v; destruct r as [|b r]; [apply T0nil|]. des_eqb.
      * subst b; destruct r; cbn [to_config map]; nums; [apply T00nil|apply T00].
      * cbn [to_config map]; nums. applys_eq T0pos; flia.
    + cbn [to_config map]; nums.
      applys_eq (Tpos (map N.to_nat l) (N.to_nat a) (Nat.pred (N.to_nat v)) (map N.to_nat r)); flia.
Qed.
Definition capb x := match x with
| qU [] a [0%N;b] => if (a =? 3+b)%N then N.odd b else false
| _ => false end.
Lemma capb_spec x: capb x=true -> ~halts tm (to_config x).
Proof.
  destruct x as [l a b r|l a r|l a r]; cbn [capb]; try discriminate.
  destruct l; [|discriminate]. destruct r as [|v r]; [discriminate|].
  destruct v; [|discriminate]. destruct r as [|b r]; [discriminate|].
  destruct r; [|discriminate]. cbn [capb]. des_eqb; [|discriminate]. intro O.
  pose proof (f_equal N.to_nat (N.div2_odd b)) as E. rewrite O in E.
  rewrite N2Nat.inj_add, N2Nat.inj_mul in E. cbn [N.b2n N.to_nat] in E.
  applys_eq (cap_nonhalt (N.to_nat (N.div2 b))); unfold cap, to_config;
    cbn [map]; nums; flia.
Qed.
Definition initial := qU [] 3%N [1%N].
Definition check fuel := capb (N.iter fuel nxt initial).
Lemma check_spec fuel: check fuel=true -> ~halts tm c0.
Proof.
  intro H. eapply multistep_nonhalt; [|apply capb_spec; exact H].
  apply (N.iter_invariant fuel _ nxt (fun x=>c0 -->* to_config x)).
  - intros x Hx. eapply evstep_trans; [apply Hx|apply nxt_spec].
  - apply init.
Qed.
Theorem nonhalt: ~halts tm c0.
Proof. apply (check_spec 309460%N). native_check_eq. Qed.
End TM41.

Module TM49.
Import BigUint.
Open Scope sym.
Definition tm := Eval compute in (TM_from_str "1RB1LA_0RC1RD_1LC0LA_1LE1RE_0RB0LF_---0LD").
Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Fixpoint LC ls := match ls with []=>0inf | n::t=>LC t <* [1]^^n <* [0] end.
Definition S l a b := LC l <* [1]^^a <{{C}} [1]^^b *> 0inf.
Definition T l a b c := LC l <* [1]^^a {{E}}> [1]^^b *> [0] *> [1]^^c *> 0inf.
Definition U l a b := LC l <* [1]^^a <{{D}} [0;0] *> [1]^^b *> 0inf.
Definition V l b c := LC l <{{A}} [1]^^b *> [0] *> [1]^^c *> 0inf.
Close Scope sym.
Open Scope nat_scope.
Lemma Inc l a b c: T l (2+a) (4+b) c -->* T l (4+a) b (2+c).
Proof. es. Qed.
Lemma Incs n l a b c: T l (2+a) (n*4+b) c -->* T l (2+a+n*2) b (c+n*2).
Proof. gen a b c. ind n Inc. Qed.
Lemma C3 l v a b: S (v::l) (3+a) b -->* T l (3+v) a b.
Proof. es. Qed.
Lemma C3nil a b: S [] (3+a) b -->* T [] 3 a b.
Proof. es. Qed.
Lemma C0 l v b: S (v::l) 0 b -->* S l v (1+b).
Proof. es. Qed.
Lemma T3 l a c: T l a 0 (3+c) -->* S (1::a::l) c 2.
Proof. es. Qed.
Lemma C1 l v b: S (v::l) 1 (2+b) -->* V l (2+v+b) 2.
Proof. es. Qed.
Lemma C2 l v b: S (v::l) 2 (2+b) -->* U l v (3+b).
Proof. es. Qed.
Lemma T2 l a: T l a 0 2 -->* U l a 4.
Proof. es. Qed.
Lemma Upos l a b: U l (1+a) (3+b) -->* T l (4+a) b 2.
Proof. es. Qed.
Lemma Vpos l v b c: V (v::l) (2+b) c -->* T l (3+v) b c.
Proof. es. Qed.
Lemma Vnil b c: V [] (2+b) c -->* T [] 3 b c.
Proof. es. Qed.
Lemma T1 l a c: T l (2+a) 1 c -->* V l a (3+c).
Proof. es. Qed.
Lemma T_2 l a c: T l (2+a) 2 c -->* V l (3+a+c) 2.
Proof. es. Qed.
Lemma T_3 l a c: T l (2+a) 3 c -->* T l (4+a) c 2.
Proof. es. Qed.
Lemma V1 l v c: V ((1+v)::l) 1 (3+c) -->* S ((3+v)::l) c 4.
Proof. es. Qed.
Lemma H1 c: halts tm (V [] 1 (3+c)).
Proof. unfold V; cbn. esx. Qed.
Lemma init: c0 -->* T [] 3 0 2.
Proof. unfold T; cbn. esx. Qed.

Definition N2 := Eval compute in (of_nat 2).
Definition N3 := Eval compute in (of_nat 3).
Definition N4 := Eval compute in (of_nat 4).
Inductive State :=
| qS (l:list N') (a b:N')
| qT (l:list N') (a b c:N')
| qU (l:list N') (a b:N')
| qV (l:list N') (b c:N').
(* qT stores a-2; the side condition needed by Inc is then automatic. *)
Definition to_config x := match x with
| qS l a b => S (map to_nat l) (to_nat a) (to_nat b)
| qT l a b c => T (map to_nat l) (2+to_nat a) (to_nat b) (to_nat c)
| qU l a b => U (map to_nat l) (to_nat a) (to_nat b)
| qV l b c => V (map to_nat l) (to_nat b) (to_nat c)
end.

Definition edge l a b c :=
let x:=qT l a b c in
(match pred b with
| None => match pred c with
  | Some c1 => match pred c1 with
    | Some c2 => match pred c2 with
      | Some c3 => Some (qS (N1::N2+a::l) c3 N2)
      | None => Some (qU l (N2+a) N4)
      end
    | None => Some x end
  | None => Some x end
| Some b1 => match pred b1 with
  | None => Some (qV l a (N3+c))
  | Some b2 => match pred b2 with
    | None => Some (qV l (N3+a+c) N2)
    | Some b3 => match pred b3 with
      | None => Some (qT l (N2+a) c N2)
      | Some _ => Some x end
    end
  end
end)%N'.

Definition nxt x := (match x with
| qS l a b => match pred a with
  | None => match l with
    | [] => Some x | v::l => Some (qS l v (succ b)) end
  | Some a1 => match pred a1 with
    | None => match l,pred b with
      | v::l,Some b1 => match pred b1 with
        | Some _ => Some (qV l (v+b) N2) | None => Some x end
      | _,_ => Some x end
    | Some a2 => match pred a2 with
      | None => match l,pred b with
        | v::l,Some b1 => match pred b1 with
          | Some _ => Some (qU l v (succ b)) | None => Some x end
        | _,_ => Some x end
      | Some a3 => match l with
        | [] => Some (qT [] N1 a3 b)
        | v::l => Some (qT l (succ v) a3 b) end
      end
    end
  end
| qT l a b c =>
  match divmod_small b N4 with
  | Some (n,r) => let d:=N2*n in edge l (a+d) r (c+d)
  | None => Some x end
| qU l a b => match pred a,pred b with
  | Some a1,Some b1 => match pred b1 with
    | Some b2 => match pred b2 with
      | Some b3 => Some (qT l (N2+a1) b3 N2)
      | None => Some x end
    | None => Some x end
  | _,_ => Some x end
| qV l b c => match pred b with
  | Some b1 => match pred b1 with
    | Some b2 => match l with
      | [] => Some (qT [] N1 b2 c)
      | v::l => Some (qT l (succ v) b2 c) end
    | None => match pred c with
      | Some c1 => match pred c1 with
        | Some c2 => match pred c2 with
          | Some c3 => match l with
            | [] => None
            | v::l => match pred v with
              | Some v1 => Some (qS (N3+v1::l) c3 N4)
              | None => Some x end
            end
          | None => Some x end
        | None => Some x end
      | None => Some x end
    end
  | None => Some x end
end)%N'.

Ltac des_pred := match goal with
| |- context[match pred ?a with _ => _ end] =>
  let H:=fresh "H" in pose proof (inj_pred a) as H; destruct (pred a)
end.
Ltac nums := rw_N';
  change (to_nat N0) with 0 in *; change (to_nat N1) with 1 in *;
  change (to_nat N2) with 2 in *; change (to_nat N3) with 3 in *;
  change (to_nat N4) with 4 in *;
  repeat match goal with H: to_nat ?a = _ |- context[to_nat ?a] => rewrite H end.

Lemma edge_spec l a b c:
match edge l a b c with
| Some y => to_config (qT l a b c) -->* to_config y
| None => halts tm (to_config (qT l a b c))
end.
Proof.
  unfold edge; repeat des_pred; cbn [to_config map]; nums; try solve [finish].
  all: first [solve [applys_eq T3; flia] | solve [applys_eq T2; flia] |
    solve [applys_eq T1; flia] | solve [applys_eq T_2; flia] |
    solve [applys_eq T_3; flia]].
Qed.

Lemma nxt_spec x:
match nxt x with
| Some y => to_config x -->* to_config y
| None => halts tm (to_config x)
end.
Proof.
  destruct x as [l a b|l a b c|l a b|l b c]; cbn [nxt].
  - repeat des_pred; destruct l; repeat des_pred; cbn [to_config map]; nums; try solve [finish].
    all: first [solve [applys_eq C0; flia] | solve [applys_eq C1; flia] |
      solve [applys_eq C2; flia] | solve [applys_eq C3; flia] |
      solve [applys_eq C3nil; flia]].
  - destruct (divmod_small b N4) as [[n r]|] eqn:E; [|finish].
    pose proof (inj_divmod_small _ _ _ _ E) as D.
    pose proof (edge_spec l (a+N2*n)%N' r (c+N2*n)%N') as H.
    destruct (edge l (a+N2*n)%N' r (c+N2*n)%N').
    + eapply evstep_trans; [|apply H]. cbn [to_config]; nums.
      applys_eq (Incs (to_nat n) (map to_nat l) (to_nat a) (to_nat r) (to_nat c)); flia.
    + eapply halts_evstep; [apply H|]. cbn [to_config]; nums.
      applys_eq (Incs (to_nat n) (map to_nat l) (to_nat a) (to_nat r) (to_nat c)); flia.
  - repeat des_pred; cbn [to_config map]; nums; try solve [finish].
    applys_eq Upos; flia.
  - repeat des_pred; destruct l; repeat des_pred; cbn [to_config map]; nums;
      try solve [finish].
    all: first [solve [applys_eq Vpos; flia] | solve [applys_eq Vnil; flia] |
      solve [applys_eq V1; flia] | solve [applys_eq H1; flia]].
Qed.

Definition initial := qT [] N1 N0 N2.
Definition nxt' x := match nxt x with Some y=>inl y | None=>inr tt end.
Definition run fuel := N_iter_until nxt' (inl initial) fuel.
Definition check fuel := match run fuel with inr _=>true | _=>false end.
Lemma check_spec fuel: check fuel=true -> halts tm c0.
Proof.
  unfold check,run. intro H.
  assert (match N_iter_until nxt' (inl initial) fuel with
    | inl y => c0 -->* to_config y | inr _ => halts tm c0 end) as R.
  { apply N_iter_until_spec.
    - intros x Hx. unfold nxt'. pose proof (nxt_spec x) as E. destruct (nxt x).
      + eapply evstep_trans; eauto.
      + eapply halts_evstep; eauto.
    - apply init. }
  destruct (N_iter_until nxt' (inl initial) fuel); [discriminate|exact R].
Qed.

Theorem halt: halts tm c0.
Proof. apply (check_spec (10^9)%N). native_check_eq. Time Qed.
End TM49.
