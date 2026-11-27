(** * 1RB1LB_1RC0RD_0LA1RE_0RF1LC_1LA0RB_---1LC halts

    The run is organised in levels.  At the start of a level the tape holds a binary
    counter word [b] with value [T] (least significant bit first).  The level first counts
    a long block of cells up through every value below 4^(2 + 2T); then an end phase eats
    the counter word and leaves a new one, which is, up to a fixed head and tail, the old
    word divided by 3.  The remainder of the division decides the class of the next level.
    The values grow like a power tower: about 4 million at level 2, a number with 17
    million bits at level 3.

    The file follows the machine through 14 levels.  The counter words are block words,
    literals and periods repeated a number of times; the repeat counts are never computed,
    and only their residues modulo powers of 2 and 3 are carried from level to level.  The
    end phase of level 14 reaches the undefined transition (state F reading 0).

    The machine is studied through the word-pair model [TM80], a verbatim copy of module
    [TM80] of busycoq's Eqv_WordPairs.v by ccz181078 (commit d3c52f5), with its [tm] and
    [tm'] renamed [tm_base] and [tm_prime] ([tm_prime] is this file's [tm]), so that the
    file defines [tm] once.  The model covers both machines of a pair, so the file also
    names the other one, 1LB1RE_0LC1LF_1RD1LD_1RA0RB_1LC0RD_0LC---; only [tm] is used.

    Layout (one module per part, in dependency order):
      T694_levels                  the machine, the word-pair model [TM80], digits and ticks
      End694, Lev694, Lvl1_694     the end of a level, the tick that ends it, level 1
      Sym694                       the end phase with a first counter of symbolic width
      Eng694, Cert694, Run694      one level as a step: the end phase and the division by 3,
                                   the level statement [Lvl], runs and cycles certified round
                                   by round, the carry chain
      Res694                       residues of block words modulo powers of 3
      Gen694                       helpers of the generated levels
      L23, L34, L45, L56           levels 2 -> 6
      L6i, L67a/b ... L1314a/b     levels 6 -> 14 (generated): counts and residues, the end
                                   phase (a) and the division (b) of each level
      Gate694, L14h                from level 14 to the halt
    The final theorem is [halt] at the end of the file.

    The first part of the module [T694_levels] was written with the help of GPT-6 Astra (OpenAI).

    AI assistance: this proof, the scripts and the checks were produced with the help of Claude (Anthropic). *)

From BusyCoq Require Import Individual62.
From BusyCoq Require BinaryCounter_v2 SimplTape ES_v2.
Require ZifyNat Lia PeanoNat String Bool NArith Arith ZArith.
From Coq Require Lists.List.

Import (notations) Coq.Strings.String.

Definition tm : TM := Eval compute in (TM_from_str "1RB1LB_1RC0RD_0LA1RE_0RF1LC_1LA0RB_---1LC").

Module T694_levels.

(** * The machine, its word-pair model and the counter levels
    Machine: 1RB1LB_1RC0RD_0LA1RE_0RF1LC_1LA0RB_---1LC = Eqv_WordPairs.TM80.tm' *)

Import Individual62 BinaryCounter_v2 SimplTape ES_v2.
Import ZifyNat Lia PeanoNat String.
Import Coq.Lists.List.
Import ListNotations.

(** ** 1. Eqv_WordPairs.TM80 Equivalence Bridge (halts tm c0 <-> iter_halts TM80.f TM80.cfg0) *)

Module TM80.
Definition tm_base := Eval compute in (TM_from_str "1LB1RE_0LC1LF_1RD1LD_1RA0RB_1LC0RD_0LC---").
Definition tm_prime := Eval compute in tm.
Definition machine (b:bool) := if b then tm_prime else tm_base.

Inductive Word := W1 | W10.
Fixpoint toLC l := match l with
| [] => 0inf << 1 << 1
| W1::l => toLC l << 1
| W10::l => toLC l << 1 << 0
end.
Inductive Head := H0 | H1 | H2 | H3 | H4 | H5.
Inductive Config := run (h:Head) (l:list Word) (r:side) | ret (l:list Word) (r:side).
Definition to_config (b:bool) c := match c with
| run H0 l r => if b then toLC l << 1 << 0 {{B}}> r else toLC l << 1 << 0 {{D}}> r
| run H1 l r => if b then toLC l <* <[1;0;1] {{C}}> r else toLC l <* <[1;0;1] {{A}}> r
| run H2 l r => if b then toLC l <* <[1;0;0] {{D}}> r else toLC l <* <[1;0;0] {{B}}> r
| run H3 l r => toLC l <* <[1;0;1;1] {{E}}> r
| run H4 l r => if b then toLC l << 0 << 0 {{F}}> r else toLC l << 1 << 1 {{A}}> r
| run H5 l r => toLC l <* <[1;1;1] {{E}}> r
| ret l r => if b then toLC l <{{B}} [1;0] *> r else toLC l <{{D}} [1;0] *> r
end.
Definition f c := match c with
| run H0 l (0>>r) => Some (run H1 l r)
| run H0 l (1>>r) => Some (run H2 l r)
| run H1 l (0>>r) => Some (ret l ([1;1] *> r))
| run H1 l (1>>r) => Some (run H3 l r)
| run H2 l (0>>r) => Some (run H4 (W10::l) r)
| run H2 l (1>>r) => Some (run H5 (W1::l) r)
| run H3 l (0>>r) => Some (run H0 (W1::W1::W1::l) r)
| run H3 l (1>>r) => Some (run H0 (W1::W10::l) r)
| run H4 _ (0>>_) => None
| run H4 l (1>>r) => Some (run H5 l r)
| run H5 l (0>>r) => Some (ret l ([1;1] *> r))
| run H5 l (1>>r) => Some (run H0 (W1::W1::l) r)
| ret (W10::l) r => Some (ret l ([1;1] *> r))
| ret (W1::W1::l) r => Some (ret l ([1;0] *> r))
| ret (W1::W10::l) r => Some (run H2 l ([1;0] *> r))
| ret [W1] r => Some (run H0 [] ([1;1;1;0] *> r))
| ret [] r => Some (run H4 [W10] r)
end.
Definition cfg0 := run H0 [] ([1;1] *> 0inf).

Lemma f_spec b c: match f c with
| Some c' => to_config b c -[machine b]->+ to_config b c'
| None => halts (machine b) (to_config b c)
end.
Proof.
  destruct b; destruct c as [[] l [s r]|l r]; unfold f; try destruct s;
  repeat match goal with
  | |- context[match ?l with [] => _ | _::_ => _ end] => destruct l as [|[] l]
  end; cbn [to_config toLC]; esx.
Qed.

Lemma eqv_model b: halts (machine b) c0 <-> iter_halts f cfg0.
Proof.
  erewrite <-(halts_iff _ _ cfg0 f (to_config b) (fun _=>True)); trivial.
  - apply halts_evstep_iff; destruct b; cbn [cfg0 to_config toLC]; esx.
  - intros c _; specialize (f_spec b c); destruct (f c); tauto.
Qed.

Lemma eqv: halts tm_base c0 <-> halts tm_prime c0.
Proof. rewrite (eqv_model false), (eqv_model true); tauto. Qed.
End TM80.

Lemma tm_eq_tm80_prime :
  tm = TM80.tm_prime.
Proof.
  reflexivity.
Qed.

Lemma c0_enters_cfg0 :
  c0 -[tm]->+ TM80.to_config true TM80.cfg0.
Proof.
  cbn [TM80.cfg0 TM80.to_config TM80.toLC]; esx.
Qed.

Theorem halts_tm_iff_iter :
  halts tm c0 <-> iter_halts TM80.f TM80.cfg0.
Proof.
  exact (TM80.eqv_model true).
Qed.

(** ** 2. Multi-Step Iteration Principles and Invariant Non-Halting Lemmas *)

Fixpoint iter_opt {A : Type} (f : A -> option A) (n : nat) (x : A) : option A :=
  match n with
  | O => Some x
  | S n' =>
    match f x with
    | Some x' => iter_opt f n' x'
    | None => None
    end
  end.

Definition f_steps (n : nat) (c : TM80.Config) : option TM80.Config :=
  iter_opt TM80.f n c.

Definition steps (c : TM80.Config) (k : nat) (c' : TM80.Config) : Prop :=
  iter_opt TM80.f k c = Some c'.

Lemma iter_opt_0 {A : Type} (f : A -> option A) (x : A) :
  iter_opt f O x = Some x.
Proof.
  reflexivity.
Qed.

Lemma iter_opt_1 {A : Type} (f : A -> option A) (x : A) :
  iter_opt f 1 x = f x.
Proof.
  cbn; destruct (f x); reflexivity.
Qed.

Lemma iter_opt_add {A : Type} (f : A -> option A) : forall n m (x x1 : A),
  iter_opt f n x = Some x1 ->
  iter_opt f (n + m) x = iter_opt f m x1.
Proof.
  induction n as [| n IH]; intros m x x1 Hn.
  - cbn in Hn |- *. injection Hn as Heq; subst x1; reflexivity.
  - cbn in Hn |- *.
    destruct (f x) as [x' |] eqn:Efx; [| discriminate].
    exact (IH m x' x1 Hn).
Qed.

Lemma iter_opt_trans {A : Type} (f : A -> option A) : forall n m (x x1 x2 : A),
  iter_opt f n x = Some x1 ->
  iter_opt f m x1 = Some x2 ->
  iter_opt f (n + m) x = Some x2.
Proof.
  intros n m x x1 x2 H1 H2.
  rewrite (iter_opt_add f n m x x1 H1).
  exact H2.
Qed.

Lemma steps_0 : forall c,
  steps c O c.
Proof.
  intro c; reflexivity.
Qed.

Lemma steps_1 : forall c c',
  TM80.f c = Some c' ->
  steps c 1 c'.
Proof.
  intros c c' H.
  unfold steps; rewrite iter_opt_1; exact H.
Qed.

Lemma steps_trans : forall k1 k2 c1 c2 c3,
  steps c1 k1 c2 ->
  steps c2 k2 c3 ->
  steps c1 (k1 + k2) c3.
Proof.
  intros k1 k2 c1 c2 c3 H1 H2.
  exact (iter_opt_trans TM80.f k1 k2 c1 c2 c3 H1 H2).
Qed.

Lemma nonhalt_from_inv {A : Type} (f : A -> option A) (Inv : A -> Prop) :
  (forall x, Inv x -> exists y, f x = Some y /\ Inv y) ->
  forall x, Inv x -> ~ iter_halts f x.
Proof.
  intros Hstep x Hinv Hhalt.
  induction Hhalt as [x Hnone | x y Hsome Hhalt IH].
  - destruct (Hstep x Hinv) as [y [Hsome _]]. congruence.
  - destruct (Hstep x Hinv) as [y' [Hsome' Hinv']].
    assert (y' = y) by congruence; subst y'.
    exact (IH Hinv').
Qed.

Lemma nonhalt_from_reachable_inv : forall (Inv : TM80.Config -> Prop),
  Inv TM80.cfg0 ->
  (forall c, Inv c -> exists c', TM80.f c = Some c' /\ Inv c') ->
  ~ halts tm c0.
Proof.
  intros Inv H0 Hstep.
  rewrite halts_tm_iff_iter.
  exact (nonhalt_from_inv TM80.f Inv Hstep TM80.cfg0 H0).
Qed.

Lemma nonhalt_from_multi_step (P : TM80.Config -> Prop) :
  (forall x, P x -> exists k y, k > O /\ iter_opt TM80.f k x = Some y /\ P y) ->
  forall x0, (exists k0 y0, iter_opt TM80.f k0 x0 = Some y0 /\ P y0) ->
  ~ iter_halts TM80.f x0.
Proof.
  intros Hstep x0 Hinit.
  set (Inv := fun x => exists k y, iter_opt TM80.f k x = Some y /\ P y).
  apply (nonhalt_from_inv TM80.f Inv); [| exact Hinit].
  intros x [k [y [Hk Hy]]].
  destruct k as [| k'].
  - cbn in Hk. injection Hk as Heq; subst y.
    destruct (Hstep x Hy) as [m [z [Hm [Hz Hpz]]]].
    destruct m as [| m']; [lia |].
    cbn in Hz.
    destruct (TM80.f x) as [x1 |] eqn:Efx; [| discriminate].
    exists x1. split; [reflexivity |].
    exists m', z. split; [exact Hz | exact Hpz].
  - cbn in Hk.
    destruct (TM80.f x) as [x1 |] eqn:Efx; [| discriminate].
    exists x1. split; [reflexivity |].
    exists k', y. split; [exact Hk | exact Hy].
Qed.

(** ** 3. Unconditional Return-Tape Invariant RetStartsWith1 *)

Definition RetStartsWith1 (c : TM80.Config) : Prop :=
  match c with
  | TM80.ret _ (b >> _) => b = 1
  | _ => True
  end.

Lemma RetStartsWith1_cfg0 :
  RetStartsWith1 TM80.cfg0.
Proof.
  exact I.
Qed.

Lemma RetStartsWith1_preserved : forall c c',
  RetStartsWith1 c ->
  TM80.f c = Some c' ->
  RetStartsWith1 c'.
Proof.
  intros c c' Hret Hstep.
  destruct c as [h l [b r] | l r].
  - destruct h, b; cbn in Hstep; try discriminate;
      injection Hstep as Heq; subst c'; cbn; reflexivity || exact I.
  - destruct l as [| [|] [| [|] l']]; cbn in Hstep;
      injection Hstep as Heq; subst c'; cbn; reflexivity || exact I.
Qed.

Lemma RetStartsWith1_steps : forall n c c',
  RetStartsWith1 c ->
  iter_opt TM80.f n c = Some c' ->
  RetStartsWith1 c'.
Proof.
  induction n as [| n IH]; intros c c' Hc Hn.
  - cbn in Hn. injection Hn as Heq; subst c'; exact Hc.
  - cbn in Hn.
    destruct (TM80.f c) as [c1 |] eqn:Efc; [| discriminate].
    apply (IH c1 c'); [| exact Hn].
    exact (RetStartsWith1_preserved c c1 Hc Efc).
Qed.

Theorem RetStartsWith1_reachable : forall n c,
  iter_opt TM80.f n TM80.cfg0 = Some c ->
  RetStartsWith1 c.
Proof.
  intros n c Hn.
  exact (RetStartsWith1_steps n TM80.cfg0 c RetStartsWith1_cfg0 Hn).
Qed.

(** ** 4. Regular Right-Tape Automaton No00 and 1-Step Closure Theorem (StateGood694) *)

(** Every 0 in the active right-tape word w before 0inf is immediately followed by 1. *)
Inductive No00 : list Sym -> Prop :=
| no00_nil :
    No00 []
| no00_1 w :
    No00 w ->
    No00 (1 :: w)
| no00_01 w :
    No00 w ->
    No00 (0 :: 1 :: w).

Ltac solve_No00 :=
  repeat (apply no00_nil || apply no00_1 || apply no00_01).

Lemma No00_app : forall u v,
  No00 u ->
  No00 v ->
  No00 (u ++ v).
Proof.
  intros u v Hu Hv.
  induction Hu as [| w Hw IH | w Hw IH]; cbn.
  - exact Hv.
  - apply no00_1, IH.
  - apply no00_01, IH.
Qed.

Lemma No00_repeat_1 : forall k w,
  No00 w ->
  No00 (repeat 1 k ++ w).
Proof.
  induction k as [| k IH]; intros w Hw; cbn.
  - exact Hw.
  - apply no00_1, IH, Hw.
Qed.

Lemma No00_01_concat_10 : forall k w,
  No00 w ->
  No00 (0 :: concat (repeat [1; 0] k) ++ 1 :: w).
Proof.
  induction k as [| k IH]; intros w Hw; cbn.
  - apply no00_01, Hw.
  - apply no00_01, IH, Hw.
Qed.

Lemma No00_concat_10 : forall k w,
  No00 w ->
  No00 (concat (repeat [1; 0] k) ++ 1 :: w).
Proof.
  intros [| k] w Hw; cbn.
  - apply no00_1, Hw.
  - apply no00_1, No00_01_concat_10, Hw.
Qed.

(** Coinductive/stream view on side matching No00 * 0inf. *)
Inductive GoodR694 : side -> Prop :=
| G694_0inf :
    GoodR694 0inf
| G694_1 r :
    GoodR694 r ->
    GoodR694 (1 >> r)
| G694_01 r :
    GoodR694 r ->
    GoodR694 (0 >> 1 >> r).

Lemma No00_implies_GoodR694 : forall w,
  No00 w ->
  GoodR694 (w *> 0inf).
Proof.
  intros w Hw.
  induction Hw as [| w' Hw' IH | w' Hw' IH]; cbn.
  - exact G694_0inf.
  - apply G694_1, IH.
  - apply G694_01, IH.
Qed.

Lemma GoodR694_implies_No00 : forall r,
  GoodR694 r ->
  exists w, r = w *> 0inf /\ No00 w.
Proof.
  intros r Hr.
  induction Hr as [| r' Hr' [w [Heq Hw]] | r' Hr' [w [Heq Hw]]].
  - exists ([] : list Sym). split; [reflexivity | exact no00_nil].
  - exists (1 :: w). split; [cbn; congruence | apply no00_1, Hw].
  - exists (0 :: 1 :: w). split; [cbn; congruence | apply no00_01, Hw].
Qed.

Lemma GoodR694_iff_No00 : forall r,
  GoodR694 r <-> exists w, r = w *> 0inf /\ No00 w.
Proof.
  intro r; split.
  - apply GoodR694_implies_No00.
  - intros [w [Heq Hw]]; subst r; apply No00_implies_GoodR694, Hw.
Qed.

Definition StateGood694 (c : TM80.Config) : Prop :=
  match c with
  | TM80.run TM80.H4 _ r => exists w, r = (1 :: w) *> 0inf /\ No00 w
  | TM80.ret _ r => exists w, r = (1 :: w) *> 0inf /\ No00 w
  | TM80.run _ _ r => exists w, r = w *> 0inf /\ No00 w
  end.

Definition NoH2AtEnd (c : TM80.Config) : Prop :=
  forall l, c <> TM80.run TM80.H2 l 0inf.

Definition H2_0_lookahead (c : TM80.Config) : Prop :=
  forall l r, c = TM80.run TM80.H2 l (0 >> r) -> exists r', r = 1 >> r'.

Lemma StateGood694_cfg0 :
  StateGood694 TM80.cfg0.
Proof.
  unfold TM80.cfg0, StateGood694.
  exists [1; 1].
  split; [reflexivity | solve_No00].
Qed.

Lemma StateGood694_implies_RetStartsWith1 : forall c,
  StateGood694 c ->
  RetStartsWith1 c.
Proof.
  intros [h l r | l r] Hgood; [exact I |].
  destruct Hgood as [w [Hr _]].
  subst r; cbn; reflexivity.
Qed.

Lemma const0_unfold :
  (0inf : side) = 0 >> 0inf.
Proof.
  apply const_unfold.
Qed.

Lemma H2_0_lookahead_implies_NoH2AtEnd : forall c,
  H2_0_lookahead c ->
  NoH2AtEnd c.
Proof.
  intros c Hlook l Heq.
  subst c.
  assert (H0 : TM80.run TM80.H2 l 0inf = TM80.run TM80.H2 l (0 >> 0inf)).
  { f_equal. exact const0_unfold. }
  destruct (Hlook l 0inf H0) as [r' Hr'].
  rewrite const0_unfold in Hr'.
  inversion Hr'.
Qed.

Lemma StateGood694_NoH2AtEnd_implies_H2_0_lookahead : forall c,
  StateGood694 c ->
  NoH2AtEnd c ->
  H2_0_lookahead c.
Proof.
  intros c Hgood Hno l r Heq.
  subst c.
  destruct Hgood as [w [Hr Hw]].
  destruct Hw as [| w' Hw' | w' Hw'].
  - cbn in Hr. exfalso. apply (Hno l). f_equal. exact Hr.
  - cbn in Hr. inversion Hr.
  - cbn in Hr. inversion Hr; subst.
    exists (w' *> 0inf). reflexivity.
Qed.

(** Main 1-Step Closure Theorem:
    Under StateGood694, all 16 non-H2(0) clauses AND internal 0s at H2 (via no00_01)
    step in 1 step to Some c' satisfying StateGood694 c'. Only c = run H2 l 0inf is excluded. *)
Theorem StateGood694_step_from_NoH2AtEnd : forall c,
  StateGood694 c ->
  NoH2AtEnd c ->
  exists c', TM80.f c = Some c' /\ StateGood694 c'.
Proof.
  intros [h l r | l r] Hgood Hno.
  - destruct h.
    + (* H0 *)
      destruct Hgood as [w [Hr Hw]]; subst r.
      destruct Hw as [| w' Hw' | w' Hw'].
      * cbn [Str_app]. rewrite const0_unfold. cbn [TM80.f].
        eexists; split; [reflexivity |].
        exists ([] : list Sym); split; [reflexivity | exact no00_nil].
      * cbn [Str_app TM80.f].
        eexists; split; [reflexivity |].
        exists w'; split; [reflexivity | exact Hw'].
      * cbn [Str_app TM80.f].
        eexists; split; [reflexivity |].
        exists (1 :: w'); split; [reflexivity | apply no00_1, Hw'].
    + (* H1 *)
      destruct Hgood as [w [Hr Hw]]; subst r.
      destruct Hw as [| w' Hw' | w' Hw'].
      * cbn [Str_app]. rewrite const0_unfold. cbn [TM80.f].
        eexists; split; [reflexivity |].
        exists [1]; split; [reflexivity | solve_No00].
      * cbn [Str_app TM80.f].
        eexists; split; [reflexivity |].
        exists w'; split; [reflexivity | exact Hw'].
      * cbn [Str_app TM80.f].
        eexists; split; [reflexivity |].
        exists (1 :: 1 :: w'); split; [reflexivity | repeat apply no00_1; exact Hw'].
    + (* H2 *)
      destruct Hgood as [w [Hr Hw]]; subst r.
      destruct Hw as [| w' Hw' | w' Hw'].
      * (* w = [] : c = run H2 l 0inf, refuted by NoH2AtEnd *)
        exfalso. apply (Hno l). reflexivity.
      * (* w = 1 :: w' *)
        cbn [Str_app TM80.f].
        eexists; split; [reflexivity |].
        exists w'; split; [reflexivity | exact Hw'].
      * (* w = 0 :: 1 :: w' : internal 0 steps to run H4 (W10::l) ((1 :: w') *> 0inf)! *)
        cbn [Str_app TM80.f].
        eexists; split; [reflexivity |].
        exists w'; split; [reflexivity | exact Hw'].
    + (* H3 *)
      destruct Hgood as [w [Hr Hw]]; subst r.
      destruct Hw as [| w' Hw' | w' Hw'].
      * cbn [Str_app]. rewrite const0_unfold. cbn [TM80.f].
        eexists; split; [reflexivity |].
        exists ([] : list Sym); split; [reflexivity | exact no00_nil].
      * cbn [Str_app TM80.f].
        eexists; split; [reflexivity |].
        exists w'; split; [reflexivity | exact Hw'].
      * cbn [Str_app TM80.f].
        eexists; split; [reflexivity |].
        exists (1 :: w'); split; [reflexivity | apply no00_1, Hw'].
    + (* H4 *)
      destruct Hgood as [w [Hr Hw]]; subst r.
      cbn [Str_app TM80.f].
      eexists; split; [reflexivity |].
      exists w; split; [reflexivity | exact Hw].
    + (* H5 *)
      destruct Hgood as [w [Hr Hw]]; subst r.
      destruct Hw as [| w' Hw' | w' Hw'].
      * cbn [Str_app]. rewrite const0_unfold. cbn [TM80.f].
        eexists; split; [reflexivity |].
        exists [1]; split; [reflexivity | solve_No00].
      * cbn [Str_app TM80.f].
        eexists; split; [reflexivity |].
        exists w'; split; [reflexivity | exact Hw'].
      * cbn [Str_app TM80.f].
        eexists; split; [reflexivity |].
        exists (1 :: 1 :: w'); split; [reflexivity | repeat apply no00_1; exact Hw'].
  - (* ret l r *)
    destruct Hgood as [w [Hr Hw]]; subst r.
    destruct l as [| [|] [| [|] l']].
    + (* ret [] *)
      cbn [TM80.f].
      eexists; split; [reflexivity |].
      exists w; split; [reflexivity | exact Hw].
    + (* ret [W1] *)
      cbn [TM80.f].
      eexists; split; [reflexivity |].
      exists (1 :: 1 :: 1 :: 0 :: 1 :: w).
      split; [reflexivity | repeat apply no00_1; apply no00_01, Hw].
    + (* ret (W1 :: W1 :: l') *)
      cbn [TM80.f].
      eexists; split; [reflexivity |].
      exists (0 :: 1 :: w).
      split; [reflexivity | apply no00_01, Hw].
    + (* ret (W1 :: W10 :: l') *)
      cbn [TM80.f].
      eexists; split; [reflexivity |].
      exists (1 :: 0 :: 1 :: w).
      split; [reflexivity | apply no00_1, no00_01, Hw].
    + (* ret [W10] *)
      cbn [TM80.f].
      eexists; split; [reflexivity |].
      exists (1 :: 1 :: w).
      split; [reflexivity | repeat apply no00_1; exact Hw].
    + (* ret (W10 :: W1 :: l') *)
      cbn [TM80.f].
      eexists; split; [reflexivity |].
      exists (1 :: 1 :: w).
      split; [reflexivity | repeat apply no00_1; exact Hw].
    + (* ret (W10 :: W10 :: l') *)
      cbn [TM80.f].
      eexists; split; [reflexivity |].
      exists (1 :: 1 :: w).
      split; [reflexivity | repeat apply no00_1; exact Hw].
Qed.

Theorem StateGood694_step_from_H2_0 : forall c,
  StateGood694 c ->
  H2_0_lookahead c ->
  exists c', TM80.f c = Some c' /\ StateGood694 c'.
Proof.
  intros c Hgood Hlook.
  apply StateGood694_step_from_NoH2AtEnd; [exact Hgood |].
  exact (H2_0_lookahead_implies_NoH2AtEnd c Hlook).
Qed.

Lemma StateGood694_reachable_from_NoH2AtEnd :
  (forall n c, iter_opt TM80.f n TM80.cfg0 = Some c -> NoH2AtEnd c) ->
  forall n, exists c, iter_opt TM80.f n TM80.cfg0 = Some c /\ StateGood694 c.
Proof.
  intros Hno n.
  induction n as [| n [c [Hc Hgood]]].
  - exists TM80.cfg0. split; [reflexivity | exact StateGood694_cfg0].
  - specialize (Hno n c Hc).
    destruct (StateGood694_step_from_NoH2AtEnd c Hgood Hno) as [c' [Hstep Hgood']].
    exists c'. split; [| exact Hgood'].
    rewrite <- Nat.add_1_r.
    exact (iter_opt_trans TM80.f n 1 TM80.cfg0 c c' Hc (steps_1 c c' Hstep)).
Qed.

Theorem nonhalt_from_NoH2AtEnd :
  (forall n c, iter_opt TM80.f n TM80.cfg0 = Some c -> NoH2AtEnd c) ->
  ~ halts tm c0.
Proof.
  intros Hno.
  set (Inv := fun c => exists n, iter_opt TM80.f n TM80.cfg0 = Some c /\ StateGood694 c).
  apply (nonhalt_from_reachable_inv Inv).
  - exists O. split; [reflexivity | exact StateGood694_cfg0].
  - intros c [n [Hn Hgood]].
    specialize (Hno n c Hn).
    destruct (StateGood694_step_from_NoH2AtEnd c Hgood Hno) as [c' [Hstep Hgood']].
    exists c'. split; [exact Hstep |].
    exists (n + 1). split; [| exact Hgood'].
    exact (iter_opt_trans TM80.f n 1 TM80.cfg0 c c' Hn (steps_1 c c' Hstep)).
Qed.

Theorem nonhalt_from_H2_0_lookahead :
  (forall n c, iter_opt TM80.f n TM80.cfg0 = Some c -> H2_0_lookahead c) ->
  ~ halts tm c0.
Proof.
  intros Hlook.
  apply nonhalt_from_NoH2AtEnd.
  intros n c Hn.
  exact (H2_0_lookahead_implies_NoH2AtEnd c (Hlook n c Hn)).
Qed.

(** ** 5. Context-Polymorphic ret Stack Elimination Laws *)

Lemma Str_app_assoc_local : forall (u v : list Sym) (r : side),
  u *> (v *> r) = (u ++ v) *> r.
Proof.
  intros u v r.
  symmetry.
  apply Str_app_assoc.
Qed.

Lemma repeat_app_local {A : Type} (x : A) : forall n m,
  repeat x (n + m) = repeat x n ++ repeat x m.
Proof.
  induction n as [| n IH]; intro m; cbn.
  - reflexivity.
  - f_equal. exact (IH m).
Qed.

Lemma repeat_comm_app {A : Type} (x : A) : forall n m (l : list A),
  repeat x n ++ repeat x m ++ l = repeat x m ++ repeat x n ++ l.
Proof.
  intros n m l.
  rewrite !app_assoc.
  rewrite <- !repeat_app_local.
  replace (n + m) with (m + n) by lia.
  reflexivity.
Qed.

Lemma ret_W10_step : forall l r,
  steps (TM80.ret (TM80.W10 :: l) r) 1 (TM80.ret l ([1; 1] *> r)).
Proof.
  intros l r; reflexivity.
Qed.

Lemma ret_W10_chain : forall k l r,
  steps (TM80.ret (repeat TM80.W10 k ++ l) r) k (TM80.ret l (repeat 1 (2 * k) *> r)).
Proof.
  induction k as [| k IH]; intros l r.
  - cbn. reflexivity.
  - replace (S k) with (1 + k) by lia.
    eapply steps_trans.
    + exact (ret_W10_step (repeat TM80.W10 k ++ l) r).
    + pose proof (IH l ([1; 1] *> r)) as Hk.
      replace (repeat 1 (2 * (1 + k)) *> r) with (repeat 1 (2 * k) *> ([1; 1] *> r)).
      * exact Hk.
      * rewrite Str_app_assoc_local.
        f_equal.
        replace (2 * (1 + k)) with (2 * k + 2) by lia.
        rewrite repeat_app_local.
        reflexivity.
Qed.

Lemma ret_W1_W1_step : forall l r,
  steps (TM80.ret (TM80.W1 :: TM80.W1 :: l) r) 1 (TM80.ret l ([1; 0] *> r)).
Proof.
  intros l r; reflexivity.
Qed.

Lemma concat_repeat_10_snoc : forall k,
  concat (repeat [1; 0] k) ++ [1; 0] = [1; 0] ++ concat (repeat [1; 0] k).
Proof.
  induction k as [| k IH]; cbn.
  - reflexivity.
  - repeat f_equal. exact IH.
Qed.

Lemma ret_W1_W1_chain : forall k l r,
  steps (TM80.ret (repeat TM80.W1 (2 * k) ++ l) r) k (TM80.ret l (concat (repeat [1; 0] k) *> r)).
Proof.
  induction k as [| k IH]; intros l r.
  - cbn. reflexivity.
  - replace (2 * S k) with (2 + 2 * k) by lia.
    replace (S k) with (1 + k) by lia.
    cbn [repeat app].
    eapply steps_trans.
    + exact (ret_W1_W1_step (repeat TM80.W1 (2 * k) ++ l) r).
    + pose proof (IH l ([1; 0] *> r)) as Hk.
      replace (concat (repeat [1; 0] (1 + k)) *> r)
        with (concat (repeat [1; 0] k) *> ([1; 0] *> r)).
      * exact Hk.
      * rewrite Str_app_assoc_local.
        cbn [repeat concat].
        rewrite concat_repeat_10_snoc.
        reflexivity.
Qed.

Lemma ret_W1_W10_step : forall l r,
  steps (TM80.ret (TM80.W1 :: TM80.W10 :: l) r) 1 (TM80.run TM80.H2 l ([1; 0] *> r)).
Proof.
  intros l r; reflexivity.
Qed.

Lemma ret_single_W1_root : forall r,
  steps (TM80.ret [TM80.W1] r) 1 (TM80.run TM80.H0 [] ([1; 1; 1; 0] *> r)).
Proof.
  intro r; reflexivity.
Qed.

Lemma ret_nil_root : forall b r,
  b = 1 ->
  steps (TM80.ret [] (b >> r)) 2 (TM80.run TM80.H5 [TM80.W10] r).
Proof.
  intros b r Hb; subst b; reflexivity.
Qed.

Lemma ret_odd_W1_W10_chain : forall k l r,
  steps (TM80.ret (repeat TM80.W1 (2 * k + 1) ++ TM80.W10 :: l) r)
        (k + 1)
        (TM80.run TM80.H2 l ([1; 0] *> (concat (repeat [1; 0] k) *> r))).
Proof.
  intros k l r.
  rewrite repeat_app_local, <- app_assoc.
  cbn [repeat app].
  eapply steps_trans.
  - exact (ret_W1_W1_chain k (TM80.W1 :: TM80.W10 :: l) r).
  - exact (ret_W1_W10_step l (concat (repeat [1; 0] k) *> r)).
Qed.

Lemma ret_odd_W1_only_chain : forall k r,
  steps (TM80.ret (repeat TM80.W1 (2 * k + 1)) r)
        (k + 1)
        (TM80.run TM80.H0 [] ([1; 1; 1; 0] *> (concat (repeat [1; 0] k) *> r))).
Proof.
  intros k r.
  rewrite repeat_app_local.
  cbn [repeat].
  eapply steps_trans.
  - exact (ret_W1_W1_chain k [TM80.W1] r).
  - exact (ret_single_W1_root (concat (repeat [1; 0] k) *> r)).
Qed.

(** ** 6. Forward Block Consumption Laws (H0, H1, H2, H3, H5 on [1;0], [1;1], [1;1;1;0], and 0inf) *)

Lemma run_H0_0inf_turnaround : forall l,
  steps (TM80.run TM80.H0 l 0inf) 2 (TM80.ret l ([1; 1] *> 0inf)).
Proof.
  intro l.
  unfold steps; cbn [iter_opt].
  rewrite const0_unfold at 1. cbn [TM80.f].
  rewrite const0_unfold at 1. cbn [TM80.f].
  reflexivity.
Qed.

Lemma run_H1_0inf_turnaround : forall l,
  steps (TM80.run TM80.H1 l 0inf) 1 (TM80.ret l ([1; 1] *> 0inf)).
Proof.
  intro l.
  unfold steps; cbn [iter_opt].
  rewrite const0_unfold at 1. cbn [TM80.f].
  reflexivity.
Qed.

Lemma run_H3_0inf_turnaround : forall l,
  steps (TM80.run TM80.H3 l 0inf) 3 (TM80.ret (TM80.W1 :: TM80.W1 :: TM80.W1 :: l) ([1; 1] *> 0inf)).
Proof.
  intro l.
  unfold steps; cbn [iter_opt].
  rewrite const0_unfold at 1. cbn [TM80.f].
  rewrite const0_unfold at 1. cbn [TM80.f].
  rewrite const0_unfold at 1. cbn [TM80.f].
  reflexivity.
Qed.

Lemma run_H5_0inf_turnaround : forall l,
  steps (TM80.run TM80.H5 l 0inf) 1 (TM80.ret l ([1; 1] *> 0inf)).
Proof.
  intro l.
  unfold steps; cbn [iter_opt].
  rewrite const0_unfold at 1. cbn [TM80.f].
  reflexivity.
Qed.

Lemma run_H0_10_step : forall l r,
  steps (TM80.run TM80.H0 l ([1; 0] *> r)) 2 (TM80.run TM80.H4 (TM80.W10 :: l) r).
Proof.
  intros l r; reflexivity.
Qed.

Lemma run_H0_101_step : forall l r,
  steps (TM80.run TM80.H0 l ([1; 0; 1] *> r)) 3 (TM80.run TM80.H5 (TM80.W10 :: l) r).
Proof.
  intros l r; reflexivity.
Qed.

Lemma run_H0_11_step : forall l r,
  steps (TM80.run TM80.H0 l ([1; 1] *> r)) 2 (TM80.run TM80.H5 (TM80.W1 :: l) r).
Proof.
  intros l r; reflexivity.
Qed.

Lemma run_H0_111_step : forall l r,
  steps (TM80.run TM80.H0 l ([1; 1; 1] *> r)) 3 (TM80.run TM80.H0 (TM80.W1 :: TM80.W1 :: TM80.W1 :: l) r).
Proof.
  intros l r; reflexivity.
Qed.

Lemma run_H0_1110_step : forall l r,
  steps (TM80.run TM80.H0 l ([1; 1; 1; 0] *> r)) 4 (TM80.run TM80.H1 (TM80.W1 :: TM80.W1 :: TM80.W1 :: l) r).
Proof.
  intros l r; reflexivity.
Qed.

Lemma run_H2_01_step : forall l r,
  steps (TM80.run TM80.H2 l ([0; 1] *> r)) 2 (TM80.run TM80.H5 (TM80.W10 :: l) r).
Proof.
  intros l r; reflexivity.
Qed.

Lemma run_H2_10_step : forall l r,
  steps (TM80.run TM80.H2 l ([1; 0] *> r)) 2 (TM80.ret (TM80.W1 :: l) ([1; 1] *> r)).
Proof.
  intros l r; reflexivity.
Qed.

Lemma run_H2_101_step : forall l r,
  steps (TM80.run TM80.H2 l ([1; 0; 1] *> r)) 2 (TM80.ret (TM80.W1 :: l) ([1; 1; 1] *> r)).
Proof.
  intros l r; reflexivity.
Qed.

Lemma run_H2_11_step : forall l r,
  steps (TM80.run TM80.H2 l ([1; 1] *> r)) 2 (TM80.run TM80.H0 (TM80.W1 :: TM80.W1 :: TM80.W1 :: l) r).
Proof.
  intros l r; reflexivity.
Qed.

Lemma run_H2_1110_step : forall l r,
  steps (TM80.run TM80.H2 l ([1; 1; 1; 0] *> r)) 4
        (TM80.run TM80.H4 (TM80.W10 :: TM80.W1 :: TM80.W1 :: TM80.W1 :: l) r).
Proof.
  intros l r; reflexivity.
Qed.

Lemma run_H5_10_step : forall l r,
  steps (TM80.run TM80.H5 l ([1; 0] *> r)) 2 (TM80.run TM80.H1 (TM80.W1 :: TM80.W1 :: l) r).
Proof.
  intros l r; reflexivity.
Qed.

Lemma run_H5_11_step : forall l r,
  steps (TM80.run TM80.H5 l ([1; 1] *> r)) 2 (TM80.run TM80.H2 (TM80.W1 :: TM80.W1 :: l) r).
Proof.
  intros l r; reflexivity.
Qed.

Lemma run_H5_111_step : forall l r,
  steps (TM80.run TM80.H5 l ([1; 1; 1] *> r)) 3 (TM80.run TM80.H5 (TM80.W1 :: TM80.W1 :: TM80.W1 :: l) r).
Proof.
  intros l r; reflexivity.
Qed.

Lemma run_H5_111_chain : forall k l r,
  steps (TM80.run TM80.H5 l (repeat 1 (3 * k) *> r)) (3 * k)
        (TM80.run TM80.H5 (repeat TM80.W1 (3 * k) ++ l) r).
Proof.
  induction k as [| k IH]; intros l r.
  - cbn. reflexivity.
  - replace (3 * S k) with (3 + 3 * k) by lia.
    cbn [repeat app].
    eapply steps_trans.
    + exact (run_H5_111_step l (repeat 1 (3 * k) *> r)).
    + pose proof (IH (TM80.W1 :: TM80.W1 :: TM80.W1 :: l) r) as Hk.
      replace (repeat TM80.W1 (3 + 3 * k) ++ l)
        with (repeat TM80.W1 (3 * k) ++ TM80.W1 :: TM80.W1 :: TM80.W1 :: l).
      * exact Hk.
      * replace (3 + 3 * k) with (3 * k + 3) by lia.
        rewrite repeat_app_local, <- app_assoc.
        reflexivity.
Qed.

(** ** 7. Concrete Root Orbit Transitions (root0 .. root14, 272 f-steps from cfg0) *)

Definition root0_w : list Sym := [1; 1].
Definition root1_w : list Sym := [1; 1; 1; 0; 1; 1].
Definition root2_w : list Sym := [1; 0; 1; 0; 1; 1; 1; 1].
Definition root3_w : list Sym := [1; 1; 1; 1; 1; 0; 1; 1; 1; 1].
Definition root4_w : list Sym := [1; 1; 1; 0; 1; 1; 1; 0; 1; 0; 1; 1; 1; 0; 1; 1].
Definition root5_w : list Sym := [1; 0; 1; 0; 1; 1; 1; 1; 1; 1; 1; 1; 1; 0; 1; 1].
Definition root6_w : list Sym := [1; 1; 1; 1; 1; 0; 1; 1; 1; 1; 1; 1; 1; 1; 1; 0; 1; 1].
Definition root7_w : list Sym := [1; 1; 1; 0; 1; 0; 1; 0; 1; 1; 1; 0; 1; 0; 1; 0; 1; 1; 1; 0; 1; 1].
Definition root8_w : list Sym := [1; 1; 1; 0; 1; 1; 1; 1; 1; 0; 1; 1; 1; 0; 1; 0; 1; 0; 1; 1; 1; 0; 1; 1].
Definition root9_w : list Sym := [1; 1; 1; 0; 1; 1; 1; 0; 1; 0; 1; 0; 1; 1; 1; 1; 1; 1; 1; 0; 1; 1; 1; 0; 1; 1].
Definition root10_w : list Sym := [1; 1; 1; 0; 1; 1; 1; 0; 1; 1; 1; 1; 1; 0; 1; 1; 1; 1; 1; 1; 1; 0; 1; 1; 1; 0; 1; 1].
Definition root11_w : list Sym := [1; 1; 1; 0; 1; 1; 1; 0; 1; 1; 1; 0; 1; 0; 1; 0; 1; 1; 1; 0; 1; 0; 1; 1; 1; 1; 1; 0; 1; 1].
Definition root12_w : list Sym := [1; 1; 1; 0; 1; 1; 1; 0; 1; 1; 1; 0; 1; 1; 1; 1; 1; 0; 1; 1; 1; 0; 1; 0; 1; 1; 1; 1; 1; 0; 1; 1].
Definition root13_w : list Sym := [1; 1; 1; 0; 1; 1; 1; 0; 1; 1; 1; 0; 1; 1; 1; 0; 1; 0; 1; 0; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 0; 1; 1].
Definition root14_w : list Sym := [1; 1; 1; 0; 1; 1; 1; 0; 1; 1; 1; 0; 1; 1; 1; 0; 1; 1; 1; 1; 1; 0; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 0; 1; 1].

Definition root0 : TM80.Config := TM80.run TM80.H0 [] (root0_w *> 0inf).
Definition root1 : TM80.Config := TM80.run TM80.H0 [] (root1_w *> 0inf).
Definition root2 : TM80.Config := TM80.ret [] (root2_w *> 0inf).
Definition root3 : TM80.Config := TM80.ret [] (root3_w *> 0inf).
Definition root4 : TM80.Config := TM80.run TM80.H0 [] (root4_w *> 0inf).
Definition root5 : TM80.Config := TM80.ret [] (root5_w *> 0inf).
Definition root6 : TM80.Config := TM80.ret [] (root6_w *> 0inf).
Definition root7 : TM80.Config := TM80.ret [] (root7_w *> 0inf).
Definition root8 : TM80.Config := TM80.ret [] (root8_w *> 0inf).
Definition root9 : TM80.Config := TM80.ret [] (root9_w *> 0inf).
Definition root10 : TM80.Config := TM80.ret [] (root10_w *> 0inf).
Definition root11 : TM80.Config := TM80.ret [] (root11_w *> 0inf).
Definition root12 : TM80.Config := TM80.ret [] (root12_w *> 0inf).
Definition root13 : TM80.Config := TM80.ret [] (root13_w *> 0inf).
Definition root14 : TM80.Config := TM80.ret [] (root14_w *> 0inf).

Lemma root0_eq_cfg0 :
  root0 = TM80.cfg0.
Proof.
  reflexivity.
Qed.

Lemma No00_root0 : No00 root0_w. Proof. unfold root0_w; solve_No00. Qed.
Lemma No00_root1 : No00 root1_w. Proof. unfold root1_w; solve_No00. Qed.
Lemma No00_root2 : No00 root2_w. Proof. unfold root2_w; solve_No00. Qed.
Lemma No00_root3 : No00 root3_w. Proof. unfold root3_w; solve_No00. Qed.
Lemma No00_root4 : No00 root4_w. Proof. unfold root4_w; solve_No00. Qed.
Lemma No00_root5 : No00 root5_w. Proof. unfold root5_w; solve_No00. Qed.
Lemma No00_root6 : No00 root6_w. Proof. unfold root6_w; solve_No00. Qed.
Lemma No00_root7 : No00 root7_w. Proof. unfold root7_w; solve_No00. Qed.
Lemma No00_root8 : No00 root8_w. Proof. unfold root8_w; solve_No00. Qed.
Lemma No00_root9 : No00 root9_w. Proof. unfold root9_w; solve_No00. Qed.
Lemma No00_root10 : No00 root10_w. Proof. unfold root10_w; solve_No00. Qed.
Lemma No00_root11 : No00 root11_w. Proof. unfold root11_w; solve_No00. Qed.
Lemma No00_root12 : No00 root12_w. Proof. unfold root12_w; solve_No00. Qed.
Lemma No00_root13 : No00 root13_w. Proof. unfold root13_w; solve_No00. Qed.
Lemma No00_root14 : No00 root14_w. Proof. unfold root14_w; solve_No00. Qed.

Lemma StateGood694_root0 : StateGood694 root0.
Proof. exists root0_w; split; [reflexivity | exact No00_root0]. Qed.

Lemma StateGood694_root1 : StateGood694 root1.
Proof. exists root1_w; split; [reflexivity | exact No00_root1]. Qed.

Lemma StateGood694_root2 : StateGood694 root2.
Proof. exists (tl root2_w); split; [reflexivity | cbn; solve_No00]. Qed.

Lemma StateGood694_root3 : StateGood694 root3.
Proof. exists (tl root3_w); split; [reflexivity | cbn; solve_No00]. Qed.

Lemma StateGood694_root4 : StateGood694 root4.
Proof. exists root4_w; split; [reflexivity | exact No00_root4]. Qed.

Lemma StateGood694_root5 : StateGood694 root5.
Proof. exists (tl root5_w); split; [reflexivity | cbn; solve_No00]. Qed.

Lemma StateGood694_root6 : StateGood694 root6.
Proof. exists (tl root6_w); split; [reflexivity | cbn; solve_No00]. Qed.

Lemma StateGood694_root7 : StateGood694 root7.
Proof. exists (tl root7_w); split; [reflexivity | cbn; solve_No00]. Qed.

Lemma StateGood694_root8 : StateGood694 root8.
Proof. exists (tl root8_w); split; [reflexivity | cbn; solve_No00]. Qed.

Lemma StateGood694_root9 : StateGood694 root9.
Proof. exists (tl root9_w); split; [reflexivity | cbn; solve_No00]. Qed.

Lemma StateGood694_root10 : StateGood694 root10.
Proof. exists (tl root10_w); split; [reflexivity | cbn; solve_No00]. Qed.

Lemma StateGood694_root11 : StateGood694 root11.
Proof. exists (tl root11_w); split; [reflexivity | cbn; solve_No00]. Qed.

Lemma StateGood694_root12 : StateGood694 root12.
Proof. exists (tl root12_w); split; [reflexivity | cbn; solve_No00]. Qed.

Lemma StateGood694_root13 : StateGood694 root13.
Proof. exists (tl root13_w); split; [reflexivity | cbn; solve_No00]. Qed.

Lemma StateGood694_root14 : StateGood694 root14.
Proof. exists (tl root14_w); split; [reflexivity | cbn; solve_No00]. Qed.

Lemma iter_opt_S_0inf : forall n h l,
  iter_opt TM80.f (S n) (TM80.run h l 0inf) =
  iter_opt TM80.f (S n) (TM80.run h l (0 >> 0inf)).
Proof.
  intros n h l.
  f_equal. f_equal. exact const0_unfold.
Qed.

Ltac step_0inf :=
  unfold steps, root0, root1, root2, root3, root4, root5, root6, root7, root8,
         root9, root10, root11, root12, root13, root14,
         root0_w, root1_w, root2_w, root3_w, root4_w, root5_w, root6_w, root7_w, root8_w,
         root9_w, root10_w, root11_w, root12_w, root13_w, root14_w;
  cbn [iter_opt TM80.f Str_app];
  repeat (rewrite iter_opt_S_0inf; cbn [iter_opt TM80.f Str_app]);
  reflexivity.

Lemma root0_to_root1 :
  steps root0 4 root1.
Proof.
  step_0inf.
Qed.

Lemma root1_to_root2 :
  steps root1 13 root2.
Proof.
  step_0inf.
Qed.

Lemma root2_to_root3 :
  steps root2 4 root3.
Proof.
  step_0inf.
Qed.

Lemma root3_to_root4 :
  steps root3 20 root4.
Proof.
  step_0inf.
Qed.

Lemma root4_to_root5 :
  steps root4 16 root5.
Proof.
  step_0inf.
Qed.

Lemma root5_to_root6 :
  steps root5 4 root6.
Proof.
  step_0inf.
Qed.

Lemma root6_to_root7 :
  steps root6 33 root7.
Proof.
  step_0inf.
Qed.

Lemma root7_to_root8 :
  steps root7 10 root8.
Proof.
  step_0inf.
Qed.

Lemma root8_to_root9 :
  steps root8 27 root9.
Proof.
  step_0inf.
Qed.

Lemma root9_to_root10 :
  steps root9 16 root10.
Proof.
  step_0inf.
Qed.

Lemma root10_to_root11 :
  steps root10 36 root11.
Proof.
  step_0inf.
Qed.

Lemma root11_to_root12 :
  steps root11 22 root12.
Proof.
  step_0inf.
Qed.

Lemma root12_to_root13 :
  steps root12 39 root13.
Proof.
  step_0inf.
Qed.

Lemma root13_to_root14 :
  steps root13 28 root14.
Proof.
  step_0inf.
Qed.

Theorem cfg0_to_root8 :
  steps TM80.cfg0 104 root8.
Proof.
  rewrite <- root0_eq_cfg0.
  change 104 with (4 + (13 + (4 + (20 + (16 + (4 + (33 + 10))))))).
  eapply steps_trans; [exact root0_to_root1 |].
  eapply steps_trans; [exact root1_to_root2 |].
  eapply steps_trans; [exact root2_to_root3 |].
  eapply steps_trans; [exact root3_to_root4 |].
  eapply steps_trans; [exact root4_to_root5 |].
  eapply steps_trans; [exact root5_to_root6 |].
  eapply steps_trans; [exact root6_to_root7 |].
  exact root7_to_root8.
Qed.

Theorem cfg0_to_root14 :
  steps TM80.cfg0 272 root14.
Proof.
  change 272 with (104 + (27 + (16 + (36 + (22 + (39 + 28)))))).
  eapply steps_trans; [exact cfg0_to_root8 |].
  eapply steps_trans; [exact root8_to_root9 |].
  eapply steps_trans; [exact root9_to_root10 |].
  eapply steps_trans; [exact root10_to_root11 |].
  eapply steps_trans; [exact root11_to_root12 |].
  eapply steps_trans; [exact root12_to_root13 |].
  exact root13_to_root14.
Qed.

(** ** Digit layer *)

(** A digit is a two-cell block on the right tape: [1;1] is digit 1, [1;0] is digit 0. *)
Definition dsym (d : bool) : list Sym := if d then [1; 1] else [1; 0].

Fixpoint dsyms (ds : list bool) : list Sym :=
  match ds with
  | [] => []
  | d :: ds => dsym d ++ dsyms ds
  end.

Lemma dsyms_cons : forall d ds r,
  dsyms (d :: ds) *> r = dsym d *> (dsyms ds *> r).
Proof.
  intros d ds r. cbn [dsyms]. symmetry. apply Str_app_assoc_local.
Qed.

Lemma dsyms_app : forall ds1 ds2 r,
  dsyms (ds1 ++ ds2) *> r = dsyms ds1 *> (dsyms ds2 *> r).
Proof.
  induction ds1 as [| d ds1 IH]; intros ds2 r.
  - reflexivity.
  - rewrite <- app_comm_cons, !dsyms_cons, IH. reflexivity.
Qed.

(** Scan states of the left-to-right pass. *)
Inductive St := Q0 | Q1 | Q2 | Q4 | Q5.

Definition hd (s : St) : TM80.Head :=
  match s with
  | Q0 => TM80.H0 | Q1 => TM80.H1 | Q2 => TM80.H2 | Q4 => TM80.H4 | Q5 => TM80.H5
  end.

(** One digit: [Some (s', p)] = move to [s'] prepending [p] (top first) to the stack;
    [None] = the pass stops on this digit. *)
Definition step1 (s : St) (d : bool) : option (St * list TM80.Word) :=
  match s, d with
  | Q4, true  => Some (Q0, [TM80.W1; TM80.W1])
  | Q4, false => None
  | Q0, true  => Some (Q5, [TM80.W1])
  | Q0, false => Some (Q4, [TM80.W10])
  | Q5, true  => Some (Q2, [TM80.W1; TM80.W1])
  | Q5, false => Some (Q1, [TM80.W1; TM80.W1])
  | Q2, true  => Some (Q0, [TM80.W1; TM80.W1; TM80.W1])
  | Q2, false => None
  | Q1, true  => Some (Q0, [TM80.W1; TM80.W10])
  | Q1, false => Some (Q0, [TM80.W1; TM80.W1; TM80.W1])
  end.

(** Words pushed by a stopping digit. *)
Definition stopstk (s : St) : list TM80.Word :=
  match s with Q2 => [TM80.W1] | _ => [] end.

Lemma step1_spec : forall s d s' p l r,
  step1 s d = Some (s', p) ->
  steps (TM80.run (hd s) l (dsym d *> r)) 2 (TM80.run (hd s') (p ++ l) r).
Proof.
  intros [] [] s' p l r H; cbn in H; try discriminate;
    injection H as <- <-; reflexivity.
Qed.

Lemma step1_stop_spec : forall s d l r,
  step1 s d = None ->
  steps (TM80.run (hd s) l (dsym d *> r)) 2 (TM80.ret (stopstk s ++ l) ([1; 1] *> r)).
Proof.
  intros [] [] l r H; cbn in H; try discriminate; reflexivity.
Qed.

Inductive ScanRes := Fin (s : St) (p : list TM80.Word) | Stop (p : list TM80.Word) (rest : list bool).

Fixpoint scanr (s : St) (ds : list bool) : ScanRes :=
  match ds with
  | [] => Fin s []
  | d :: ds' =>
    match step1 s d with
    | Some (s1, p1) =>
      match scanr s1 ds' with
      | Fin s2 p2 => Fin s2 (p2 ++ p1)
      | Stop p2 rest => Stop (p2 ++ p1) rest
      end
    | None => Stop (stopstk s) ds'
    end
  end.

Definition scan (s : St) (ds : list bool) : option (St * list TM80.Word) :=
  match scanr s ds with Fin s' p => Some (s', p) | Stop _ _ => None end.

Lemma scanr_app : forall ds1 ds2 s,
  scanr s (ds1 ++ ds2) =
  match scanr s ds1 with
  | Fin s1 p1 =>
    match scanr s1 ds2 with
    | Fin s2 p2 => Fin s2 (p2 ++ p1)
    | Stop p2 rest => Stop (p2 ++ p1) rest
    end
  | Stop p rest => Stop p (rest ++ ds2)
  end.
Proof.
  induction ds1 as [| d ds1 IH]; intros ds2 s.
  - cbn. destruct (scanr s ds2); rewrite app_nil_r; reflexivity.
  - cbn [app scanr]. destruct (step1 s d) as [[s1 p1] |]; [| reflexivity].
    rewrite IH. destruct (scanr s1 ds1) as [s2 p2 | p2 rest]; [| reflexivity].
    destruct (scanr s2 ds2); rewrite app_assoc; reflexivity.
Qed.

Lemma scanr_fin_steps : forall ds s s' p l r,
  scanr s ds = Fin s' p ->
  exists n, steps (TM80.run (hd s) l (dsyms ds *> r)) n (TM80.run (hd s') (p ++ l) r).
Proof.
  induction ds as [| d ds IH]; intros s s' p l r H.
  - cbn in H. injection H as <- <-. exists O. reflexivity.
  - cbn [scanr] in H.
    destruct (step1 s d) as [[s1 p1] |] eqn:E; [| discriminate].
    destruct (scanr s1 ds) as [s2 p2 | p2 rest] eqn:E2; [| discriminate].
    injection H as <- <-.
    destruct (IH s1 s2 p2 (p1 ++ l) r E2) as [n Hn].
    exists (2 + n). rewrite dsyms_cons.
    eapply steps_trans; [exact (step1_spec s d s1 p1 l _ E) |].
    rewrite <- app_assoc. exact Hn.
Qed.

Lemma scanr_stop_steps : forall ds s p rest l r,
  scanr s ds = Stop p rest ->
  exists n, steps (TM80.run (hd s) l (dsyms ds *> r)) n
                  (TM80.ret (p ++ l) ([1; 1] *> (dsyms rest *> r))).
Proof.
  induction ds as [| d ds IH]; intros s p rest l r H.
  - discriminate.
  - cbn [scanr] in H. rewrite dsyms_cons.
    destruct (step1 s d) as [[s1 p1] |] eqn:E.
    + destruct (scanr s1 ds) as [s2 p2 | p2 rest'] eqn:E2; [discriminate |].
      injection H as <- <-.
      destruct (IH s1 p2 rest' (p1 ++ l) r E2) as [n Hn].
      exists (2 + n).
      eapply steps_trans; [exact (step1_spec s d s1 p1 l _ E) |].
      rewrite <- app_assoc. exact Hn.
    + injection H as <- <-. exists 2.
      exact (step1_stop_spec s d l _ E).
Qed.

Lemma scan_steps : forall ds s s' p l r,
  scan s ds = Some (s', p) ->
  exists n, steps (TM80.run (hd s) l (dsyms ds *> r)) n (TM80.run (hd s') (p ++ l) r).
Proof.
  intros ds s s' p l r H. unfold scan in H.
  destruct (scanr s ds) as [s2 p2 |] eqn:E; [| discriminate].
  injection H as <- <-. exact (scanr_fin_steps ds s s2 p2 l r E).
Qed.

(** *** END of input (the right tape is 0inf) *)

Definition safe_end (s : St) : bool :=
  match s with Q0 | Q1 | Q5 => true | Q2 | Q4 => false end.

Lemma end_Q0 : forall l,
  steps (TM80.run (hd Q0) l 0inf) 2 (TM80.ret l ([1; 1] *> 0inf)).
Proof. exact run_H0_0inf_turnaround. Qed.

Lemma end_Q5 : forall l,
  steps (TM80.run (hd Q5) l 0inf) 1 (TM80.ret l ([1; 1] *> 0inf)).
Proof. exact run_H5_0inf_turnaround. Qed.

Lemma end_Q1 : forall l,
  steps (TM80.run (hd Q1) l 0inf) 1 (TM80.ret l ([1; 1] *> 0inf)).
Proof. exact run_H1_0inf_turnaround. Qed.

Lemma end_Q4_halts : forall l,
  TM80.f (TM80.run (hd Q4) l 0inf) = None.
Proof. intro l. cbn [hd]. rewrite const0_unfold. reflexivity. Qed.

Lemma end_Q2_step : forall l,
  TM80.f (TM80.run (hd Q2) l 0inf) = Some (TM80.run TM80.H4 (TM80.W10 :: l) 0inf).
Proof. intro l. cbn [hd]. rewrite const0_unfold at 1. reflexivity. Qed.

Lemma end_Q2_halts : forall l,
  iter_opt TM80.f 2 (TM80.run (hd Q2) l 0inf) = None.
Proof.
  intro l. cbn [iter_opt]. rewrite end_Q2_step.
  pose proof (end_Q4_halts (TM80.W10 :: l)) as H. cbn [hd] in H. rewrite H. reflexivity.
Qed.

Lemma end_safe_steps : forall s l,
  safe_end s = true ->
  exists n, steps (TM80.run (hd s) l 0inf) n (TM80.ret l ([1; 1] *> 0inf)).
Proof.
  intros [] l H; cbn in H; try discriminate.
  - exists 2. exact (end_Q0 l).
  - exists 1%nat. exact (end_Q1 l).
  - exists 1%nat. exact (end_Q5 l).
Qed.

Lemma end_unsafe_halts : forall s l,
  safe_end s = false ->
  exists n, iter_opt TM80.f n (TM80.run (hd s) l 0inf) = None.
Proof.
  intros [] l H; cbn in H; try discriminate.
  - exists 2. exact (end_Q2_halts l).
  - exists 1%nat. cbn [iter_opt]. rewrite end_Q4_halts. reflexivity.
Qed.

(** A pass that consumes the whole digit string and reaches 0inf. *)
Lemma scan_to_end_safe : forall ds s s' p l,
  scanr s ds = Fin s' p -> safe_end s' = true ->
  exists n, steps (TM80.run (hd s) l (dsyms ds *> 0inf)) n
                  (TM80.ret (p ++ l) ([1; 1] *> 0inf)).
Proof.
  intros ds s s' p l H Hs.
  destruct (scanr_fin_steps ds s s' p l 0inf H) as [n1 H1].
  destruct (end_safe_steps s' (p ++ l) Hs) as [n2 H2].
  exists (n1 + n2). exact (steps_trans _ _ _ _ _ H1 H2).
Qed.

Lemma scan_to_end_unsafe : forall ds s s' p l,
  scanr s ds = Fin s' p -> safe_end s' = false ->
  exists n, iter_opt TM80.f n (TM80.run (hd s) l (dsyms ds *> 0inf)) = None.
Proof.
  intros ds s s' p l H Hs.
  destruct (scanr_fin_steps ds s s' p l 0inf H) as [n1 H1].
  destruct (end_unsafe_halts s' (p ++ l) Hs) as [n2 H2].
  exists (n1 + n2). unfold steps in H1.
  rewrite (iter_opt_add TM80.f n1 n2 _ _ H1). exact H2.
Qed.

(** *** Decode (ret) steps *)

Lemma ret_b_dec : forall l r,
  steps (TM80.ret (TM80.W10 :: l) r) 1 (TM80.ret l ([1; 1] *> r)).
Proof. exact ret_W10_step. Qed.

Lemma ret_aa_dec : forall l r,
  steps (TM80.ret (TM80.W1 :: TM80.W1 :: l) r) 1 (TM80.ret l ([1; 0] *> r)).
Proof. exact ret_W1_W1_step. Qed.

Lemma ret_ab_dec : forall l r,
  steps (TM80.ret (TM80.W1 :: TM80.W10 :: l) r) 3 (TM80.ret (TM80.W1 :: l) ([1; 1] *> r)).
Proof. intros l r. reflexivity. Qed.

Lemma ret_a_root : forall r,
  steps (TM80.ret [TM80.W1] r) 1 (TM80.run TM80.H0 [] ([1; 1; 1; 0] *> r)).
Proof. exact ret_single_W1_root. Qed.

Lemma ret_nil_start : forall r,
  steps (TM80.ret [] r) 1 (TM80.run (hd Q4) [TM80.W10] r).
Proof. intro r. reflexivity. Qed.

(** *** mod-3 lemmas *)

Lemma scanr_ones3 : forall t,
  scanr Q0 (repeat true (3 * t)) = Fin Q0 (repeat TM80.W1 (6 * t)).
Proof.
  induction t as [| t IH].
  - reflexivity.
  - replace (3 * S t) with (S (S (S (3 * t)))) by lia.
    cbn [repeat scanr step1]. rewrite IH.
    replace (6 * S t) with (6 * t + 6) by lia.
    rewrite repeat_app_local, <- !app_assoc. reflexivity.
Qed.

Definition endstate (s : St) (ds : list bool) : option St :=
  match scanr s ds with Fin s' _ => Some s' | Stop _ _ => None end.

Definition cycQ (k : nat) : St :=
  match k with O => Q0 | S O => Q5 | _ => Q2 end.

Lemma endstate_ones : forall j,
  endstate Q0 (repeat true j) = Some (cycQ (j mod 3)).
Proof.
  intro j. induction j as [j IH] using (well_founded_induction Nat.lt_wf_0).
  destruct j as [| [| [| j']]]; try reflexivity.
  unfold endstate in *. cbn [repeat scanr step1].
  specialize (IH j' ltac:(lia)).
  destruct (scanr Q0 (repeat true j')) as [s2 p2 |]; [| discriminate].
  injection IH as ->.
  replace (S (S (S j'))) with (j' + 1 * 3) by lia. rewrite Nat.Div0.mod_add by lia.
  reflexivity.
Qed.

Lemma mod3_S : forall j,
  (S j) mod 3 = match j mod 3 with O => 1%nat | S O => 2%nat | _ => O end.
Proof.
  intro j.
  assert (Hb : j mod 3 < 3) by (apply Nat.mod_upper_bound; lia).
  pose proof (Nat.div_mod_eq j 3) as Hd.
  replace (S j) with (S (j mod 3) + (j / 3) * 3) by lia.
  rewrite Nat.Div0.mod_add by lia.
  destruct (j mod 3) as [| [| [| k]]]; cbn; try reflexivity; lia.
Qed.

Definition hstate (o : option St) : bool :=
  match o with Some s => negb (safe_end s) | None => false end.

(** A tail [0 1^j] read from Q0 ends in a halting state iff j = 0 mod 3. *)
Lemma tail_Q0 : forall j,
  hstate (endstate Q0 (false :: repeat true j)) = (j mod 3 =? 0).
Proof.
  intros [| j]; [reflexivity |].
  pose proof (endstate_ones j) as E. rewrite mod3_S.
  assert (Hb : j mod 3 < 3) by (apply Nat.mod_upper_bound; lia).
  destruct (j mod 3) as [| [| [| k]]]; [| | | lia];
    unfold endstate in *; cbn [repeat scanr step1];
    (destruct (scanr Q0 (repeat true j)) as [s2 p2 |]; [| discriminate]);
    injection E as ->; reflexivity.
Qed.

(** From Q5: halting iff j >= 1 and j = 0 mod 3. *)
Lemma tail_Q5 : forall j,
  hstate (endstate Q5 (false :: repeat true j)) = andb (negb (j =? 0)) (j mod 3 =? 0).
Proof.
  intros [| j]; [reflexivity |].
  pose proof (endstate_ones j) as E. rewrite mod3_S.
  assert (Hb : j mod 3 < 3) by (apply Nat.mod_upper_bound; lia).
  destruct (j mod 3) as [| [| [| k]]]; [| | | lia];
    unfold endstate in *; cbn [repeat scanr step1];
    (destruct (scanr Q0 (repeat true j)) as [s2 p2 |]; [| discriminate]);
    injection E as ->; reflexivity.
Qed.

(** From Q1: halting iff j = 2 mod 3. *)
Lemma tail_Q1 : forall j,
  hstate (endstate Q1 (false :: repeat true j)) = (j mod 3 =? 2).
Proof.
  intro j.
  pose proof (endstate_ones j) as E.
  assert (Hb : j mod 3 < 3) by (apply Nat.mod_upper_bound; lia).
  destruct (j mod 3) as [| [| [| k]]]; [| | | lia];
    unfold endstate in *; cbn [scanr step1];
    (destruct (scanr Q0 (repeat true j)) as [s2 p2 |]; [| discriminate]);
    injection E as ->; reflexivity.
Qed.

(** *** Decode: the ret phase, as a pure function on the stack (top first) *)

(** [dec2 pend l]: decode stack [l], with an extra W1 on top when [pend] is true.
    Returns the digits written to the right of the head (left to right) and
    whether the decode ends at [ret [W1] _] (a root) instead of [ret [] _]. *)
Fixpoint dec2 (pend : bool) (l : list TM80.Word) : list bool * bool :=
  match l with
  | [] => ([], pend)
  | TM80.W10 :: l' => let (o, rt) := dec2 pend l' in (o ++ [true], rt)
  | TM80.W1 :: l' =>
    if pend then let (o, rt) := dec2 false l' in (o ++ [false], rt)
    else dec2 true l'
  end.

Definition dtarget (rt : bool) (o : list bool) (r : side) : TM80.Config :=
  if rt then TM80.ret [TM80.W1] (dsyms o *> r) else TM80.ret [] (dsyms o *> r).

Lemma dtarget_snoc : forall rt o d r,
  dtarget rt (o ++ [d]) r = dtarget rt o (dsym d *> r).
Proof.
  intros [] o d r; unfold dtarget; rewrite dsyms_app; cbn [dsyms]; rewrite app_nil_r; reflexivity.
Qed.

Lemma dec2_spec : forall l pend r o rt,
  dec2 pend l = (o, rt) ->
  exists n, steps (TM80.ret (if pend then TM80.W1 :: l else l) r) n (dtarget rt o r).
Proof.
  induction l as [| w l IH]; intros pend r o rt H.
  - cbn in H. injection H as <- <-. exists O. destruct pend; reflexivity.
  - destruct w, pend; cbn [dec2] in H.
    + (* pend, W1 :: l : ret (W1::W1::l) *)
      destruct (dec2 false l) as [o1 rt1] eqn:E. injection H as <- <-.
      destruct (IH false ([1; 0] *> r) o1 rt1 E) as [n Hn].
      exists (1 + n). rewrite dtarget_snoc.
      eapply steps_trans; [exact (ret_aa_dec l r) | exact Hn].
    + (* no pend, W1 :: l *)
      exact (IH true r o rt H).
    + (* pend, W10 :: l : ret (W1::W10::l) *)
      destruct (dec2 true l) as [o1 rt1] eqn:E. injection H as <- <-.
      destruct (IH true ([1; 1] *> r) o1 rt1 E) as [n Hn].
      exists (3 + n). rewrite dtarget_snoc.
      eapply steps_trans; [exact (ret_ab_dec l r) | exact Hn].
    + (* no pend, W10 :: l *)
      destruct (dec2 false l) as [o1 rt1] eqn:E. injection H as <- <-.
      destruct (IH false ([1; 1] *> r) o1 rt1 E) as [n Hn].
      exists (1 + n). rewrite dtarget_snoc.
      eapply steps_trans; [exact (ret_b_dec l r) | exact Hn].
Qed.

Definition dec (l : list TM80.Word) : list bool * bool := dec2 false l.

Lemma dec_spec_nil : forall l r o,
  dec l = (o, false) ->
  exists n, steps (TM80.ret l r) n (TM80.ret [] (dsyms o *> r)).
Proof. intros l r o H. exact (dec2_spec l false r o false H). Qed.

Lemma dec_spec_root : forall l r o,
  dec l = (o, true) ->
  exists n, steps (TM80.ret l r) n (TM80.run TM80.H0 [] (dsyms (true :: false :: o) *> r)).
Proof.
  intros l r o H.
  destruct (dec2_spec l false r o true H) as [n Hn].
  exists (n + 1). eapply steps_trans; [exact Hn |].
  exact (ret_a_root (dsyms o *> r)).
Qed.

(** *** One pass: scan, then decode *)

Inductive PassRes := PHalt | PNil (ds : list bool) | PRoot (T : list bool).

Definition pres_cfg (x : PassRes) : option TM80.Config :=
  match x with
  | PHalt => None
  | PNil ds => Some (TM80.ret [] (dsyms ds *> 0inf))
  | PRoot T => Some (TM80.run TM80.H0 [] (dsyms T *> 0inf))
  end.

Definition finish (stk : list TM80.Word) (tail : list bool) : PassRes :=
  match dec stk with
  | (o, false) => PNil (o ++ tail)
  | (o, true) => PRoot (true :: false :: o ++ tail)
  end.

Definition dpass (s : St) (l0 : list TM80.Word) (ds : list bool) : PassRes :=
  match scanr s ds with
  | Stop p rest => finish (p ++ l0) (true :: rest)
  | Fin s' p => if safe_end s' then finish (p ++ l0) [true] else PHalt
  end.

Lemma finish_spec : forall stk tail c,
  pres_cfg (finish stk tail) = Some c ->
  exists n, steps (TM80.ret stk (dsyms tail *> 0inf)) n c.
Proof.
  intros stk tail c H. unfold finish in H.
  destruct (dec stk) as [o []] eqn:E; unfold pres_cfg in H; injection H as <-.
  - destruct (dec_spec_root stk (dsyms tail *> 0inf) o E) as [n Hn].
    exists n. rewrite dsyms_app. exact Hn.
  - destruct (dec_spec_nil stk (dsyms tail *> 0inf) o E) as [n Hn].
    exists n. rewrite dsyms_app. exact Hn.
Qed.

Lemma pass_spec : forall s l0 ds c,
  pres_cfg (dpass s l0 ds) = Some c ->
  exists n, steps (TM80.run (hd s) l0 (dsyms ds *> 0inf)) n c.
Proof.
  intros s l0 ds c H. unfold dpass in H.
  destruct (scanr s ds) as [s' p | p rest] eqn:E.
  - destruct (safe_end s') eqn:Es; [| discriminate].
    destruct (scan_to_end_safe ds s s' p l0 E Es) as [n1 H1].
    destruct (finish_spec (p ++ l0) [true] c H) as [n2 H2].
    exists (n1 + n2). exact (steps_trans _ _ _ _ _ H1 H2).
  - destruct (scanr_stop_steps ds s p rest l0 0inf E) as [n1 H1].
    destruct (finish_spec (p ++ l0) (true :: rest) c H) as [n2 H2].
    rewrite (dsyms_cons true) in H2.
    exists (n1 + n2). exact (steps_trans _ _ _ _ _ H1 H2).
Qed.

(** *** One tick: NIL to NIL, with up to [fuel] root rescans *)

Fixpoint rootloop (fuel : nat) (T : list bool) : option (list bool) :=
  match fuel with
  | O => None
  | S f =>
    match dpass Q0 [] T with
    | PHalt => None
    | PNil ds' => Some ds'
    | PRoot T' => rootloop f T'
    end
  end.

Definition tickF (fuel : nat) (ds : list bool) : option (list bool) :=
  match dpass Q4 [TM80.W10] ds with
  | PHalt => None
  | PNil ds' => Some ds'
  | PRoot T => rootloop fuel T
  end.

Lemma rootloop_spec : forall k T ds',
  rootloop k T = Some ds' ->
  exists n, steps (TM80.run TM80.H0 [] (dsyms T *> 0inf)) n (TM80.ret [] (dsyms ds' *> 0inf)).
Proof.
  induction k as [| k IH]; intros T ds' H; [discriminate |].
  cbn [rootloop] in H.
  destruct (dpass Q0 [] T) as [| ds1 | T1] eqn:E; [discriminate | |].
  - injection H as <-.
    apply (pass_spec Q0 [] T). rewrite E. reflexivity.
  - destruct (pass_spec Q0 [] T (TM80.run TM80.H0 [] (dsyms T1 *> 0inf))) as [n1 H1].
    { rewrite E. reflexivity. }
    destruct (IH T1 ds' H) as [n2 H2].
    exists (n1 + n2). exact (steps_trans _ _ _ _ _ H1 H2).
Qed.

Lemma tick_spec : forall k ds ds',
  tickF k ds = Some ds' ->
  exists n, steps (TM80.ret [] (dsyms ds *> 0inf)) (S n) (TM80.ret [] (dsyms ds' *> 0inf)).
Proof.
  intros k ds ds' H. unfold tickF in H.
  pose proof (ret_nil_start (dsyms ds *> 0inf)) as H0.
  destruct (dpass Q4 [TM80.W10] ds) as [| ds1 | T1] eqn:E; [discriminate | |].
  - injection H as <-.
    destruct (pass_spec Q4 [TM80.W10] ds (TM80.ret [] (dsyms ds1 *> 0inf))) as [n Hn].
    { rewrite E. reflexivity. }
    exists n. exact (steps_trans 1 n _ _ _ H0 Hn).
  - destruct (pass_spec Q4 [TM80.W10] ds (TM80.run TM80.H0 [] (dsyms T1 *> 0inf))) as [n1 H1].
    { rewrite E. reflexivity. }
    destruct (rootloop_spec k T1 ds' H) as [n2 H2].
    exists (n1 + n2).
    exact (steps_trans 1 (n1 + n2) _ _ _ H0 (steps_trans _ _ _ _ _ H1 H2)).
Qed.

(** *** The reduction: nonhalting follows from any tick-closed predicate on digit strings *)

(** The NIL configuration [root3] (21 steps from cfg0) has digit string 11011. *)
Definition D0 : list bool := [true; true; false; true; true].

Lemma cfg0_to_D0 :
  steps TM80.cfg0 21 (TM80.ret [] (dsyms D0 *> 0inf)).
Proof.
  rewrite <- root0_eq_cfg0.
  change 21 with (4 + (13 + 4)).
  eapply steps_trans; [exact root0_to_root1 |].
  eapply steps_trans; [exact root1_to_root2 |].
  exact root2_to_root3.
Qed.

Theorem nonhalt_from_digit_inv (P : list bool -> Prop) (k : nat) :
  P D0 ->
  (forall ds, P ds -> exists ds', tickF k ds = Some ds' /\ P ds') ->
  ~ halts tm c0.
Proof.
  intros HP0 Hstep.
  rewrite halts_tm_iff_iter.
  apply (nonhalt_from_multi_step
           (fun c => exists ds, c = TM80.ret [] (dsyms ds *> 0inf) /\ P ds)).
  - intros x [ds [-> Hds]].
    destruct (Hstep ds Hds) as [ds' [Ht Hds']].
    destruct (tick_spec k ds ds' Ht) as [n Hn].
    exists (S n), (TM80.ret [] (dsyms ds' *> 0inf)).
    split; [lia |]. split; [exact Hn |]. exists ds'. split; [reflexivity | exact Hds'].
  - exists 21, (TM80.ret [] (dsyms D0 *> 0inf)).
    split; [exact cfg0_to_D0 |]. exists D0. split; [reflexivity | exact HP0].
Qed.

(** *** Sanity: the first 12 ticks agree with the reference digit simulator *)

Fixpoint orbit (k n : nat) (ds : list bool) : list (list bool) :=
  match n with
  | O => []
  | S n' => match tickF k ds with Some ds' => ds' :: orbit k n' ds' | None => [] end
  end.

Lemma tick_sanity :
  orbit 3 12 D0 =
  [[false; false; true; true; true; true; false; true];
   [true; true; false; true; true; true; true; false; true];
   [true; false; false; false; true; false; false; false; true; false; true];
   [true; false; true; true; false; true; false; false; false; true; false; true];
   [true; false; true; false; false; false; true; true; true; false; true; false; true];
   [true; false; true; false; true; true; false; true; true; true; false; true; false; true];
   [true; false; true; false; true; false; false; false; true; false; false; true; true; false; true];
   [true; false; true; false; true; false; true; true; false; true; false; false; true; true; false; true];
   [true; false; true; false; true; false; true; false; false; false; true; true; true; true; true; false; true];
   [true; false; true; false; true; false; true; false; true; true; false; true; true; true; true; true; false; true];
   [true; false; true; false; true; false; true; false; true; false; false; false; true; false; false; false; false; false; true; true];
   [true; false; true; false; true; false; true; false; true; false; true; true; false; true; false; false; false; false; false; true; true]].
Proof. vm_compute. reflexivity. Qed.

(** *** Prefix inertness: a (10)^k prefix rides along through a NIL pass *)

Definition rep10 (k : nat) : list bool := concat (repeat [true; false] k).
Definition rep01 (k : nat) : list bool := concat (repeat [false; true] k).
Definition blocks (k : nat) : list TM80.Word := concat (repeat [TM80.W10; TM80.W1; TM80.W1] k).

Lemma concat_repeat_snoc {A : Type} (x : list A) : forall k,
  concat (repeat x (S k)) = concat (repeat x k) ++ x.
Proof.
  induction k as [| k IH]; cbn [repeat concat] in *.
  - rewrite !app_nil_r. reflexivity.
  - rewrite IH at 1. rewrite app_assoc. reflexivity.
Qed.

Lemma true_rep01 : forall k, true :: rep01 k = rep10 k ++ [true].
Proof.
  unfold rep01, rep10. induction k as [| k IH]; [reflexivity |].
  cbn [repeat concat app]. rewrite IH. reflexivity.
Qed.

Lemma scanr_rep10 : forall k, scanr Q4 (rep10 k) = Fin Q4 (blocks k).
Proof.
  unfold rep10, blocks. induction k as [| k IH]; [reflexivity |].
  cbn [repeat concat app scanr step1]. rewrite IH. rewrite <- app_assoc.
  exact (f_equal (Fin Q4) (eq_sym (concat_repeat_snoc [TM80.W10; TM80.W1; TM80.W1] k))).
Qed.

Lemma scanr_rep10_app : forall k ds,
  scanr Q4 (rep10 k ++ ds) =
  match scanr Q4 ds with
  | Fin s p => Fin s (p ++ blocks k)
  | Stop p rest => Stop (p ++ blocks k) rest
  end.
Proof.
  intros k ds. rewrite scanr_app, scanr_rep10. reflexivity.
Qed.

Lemma dec2_app : forall p pend, exists pend' q, forall l,
  dec2 pend (p ++ l) = (fst (dec2 pend' l) ++ q, snd (dec2 pend' l)).
Proof.
  induction p as [| w p IH]; intros pend.
  - exists pend, (@nil bool). intro l. cbn [app]. destruct (dec2 pend l); cbn. rewrite app_nil_r. reflexivity.
  - destruct w; [destruct pend |].
    + destruct (IH false) as [pd [q Hq]]. exists pd, (q ++ [false]). intro l.
      cbn [app dec2]. rewrite Hq. cbn. rewrite app_assoc. reflexivity.
    + destruct (IH true) as [pd [q Hq]]. exists pd, q. intro l.
      cbn [app dec2]. exact (Hq l).
    + destruct (IH pend) as [pd [q Hq]]. exists pd, (q ++ [true]). intro l.
      cbn [app dec2]. rewrite Hq. cbn. rewrite app_assoc. reflexivity.
Qed.

Lemma dec2_blocks : forall k pend l,
  dec2 pend (blocks k ++ l) = (fst (dec2 pend l) ++ rep01 k, snd (dec2 pend l)).
Proof.
  intros k pend l. revert pend l. induction k as [| k IH]; intros pend l.
  - unfold rep01. cbn [blocks repeat concat app]. destruct (dec2 pend l); cbn.
    rewrite app_nil_r. reflexivity.
  - unfold blocks. cbn [repeat concat app]. fold (blocks k).
    unfold rep01. rewrite (concat_repeat_snoc _ k). fold (rep01 k).
    destruct pend; cbn [dec2]; rewrite IH; cbn; rewrite <- !app_assoc; reflexivity.
Qed.

Definition shiftR (k : nat) (x : PassRes) : PassRes :=
  match x with
  | PHalt => PHalt
  | PNil d => PNil (rep10 k ++ d)
  | PRoot (true :: false :: d) => PRoot (true :: false :: rep10 k ++ d)
  | PRoot T => PRoot T
  end.

Lemma finish_shift : forall p k tail,
  finish ((p ++ blocks k) ++ [TM80.W10]) tail = shiftR k (finish (p ++ [TM80.W10]) tail).
Proof.
  intros p k tail. unfold finish, dec. rewrite <- app_assoc.
  destruct (dec2_app p false) as [pd [q Hq]]. rewrite !Hq. rewrite dec2_blocks.
  destruct pd; cbn [dec2 fst snd app shiftR];
    rewrite <- !app_assoc, (app_comm_cons (rep01 k) (q ++ tail) true), true_rep01,
      <- app_assoc; reflexivity.
Qed.

Theorem dpass_shift : forall k ds,
  dpass Q4 [TM80.W10] (rep10 k ++ ds) = shiftR k (dpass Q4 [TM80.W10] ds).
Proof.
  intros k ds. unfold dpass. rewrite scanr_rep10_app.
  destruct (scanr Q4 ds) as [s' p | p rest].
  - destruct (safe_end s'); [apply finish_shift | reflexivity].
  - apply finish_shift.
Qed.

Corollary dpass_shift_nil : forall k ds d,
  dpass Q4 [TM80.W10] ds = PNil d ->
  dpass Q4 [TM80.W10] (rep10 k ++ ds) = PNil (rep10 k ++ d).
Proof. intros k ds d H. rewrite dpass_shift, H. reflexivity. Qed.

Corollary dpass_shift_halt : forall k ds,
  dpass Q4 [TM80.W10] ds = PHalt ->
  dpass Q4 [TM80.W10] (rep10 k ++ ds) = PHalt.
Proof. intros k ds H. rewrite dpass_shift, H. reflexivity. Qed.

Corollary dpass_shift_root : forall k ds d,
  dpass Q4 [TM80.W10] ds = PRoot (true :: false :: d) ->
  dpass Q4 [TM80.W10] (rep10 k ++ ds) = PRoot (true :: false :: rep10 k ++ d).
Proof. intros k ds d H. rewrite dpass_shift, H. reflexivity. Qed.

Corollary tickF_shift_nil : forall fuel k ds d,
  dpass Q4 [TM80.W10] ds = PNil d ->
  tickF fuel (rep10 k ++ ds) = Some (rep10 k ++ d).
Proof.
  intros fuel k ds d H. unfold tickF. rewrite (dpass_shift_nil k ds d H). reflexivity.
Qed.

(** *** Iterated ticks and the concrete start of level 1 *)

Fixpoint tickN (fuel n : nat) (ds : list bool) : option (list bool) :=
  match n with
  | O => Some ds
  | S n' => match tickF fuel ds with Some d' => tickN fuel n' d' | None => None end
  end.

Lemma tickN_spec : forall fuel n ds ds',
  tickN fuel n ds = Some ds' ->
  exists m, steps (TM80.ret [] (dsyms ds *> 0inf)) m (TM80.ret [] (dsyms ds' *> 0inf)).
Proof.
  intros fuel n. induction n as [| n IH]; intros ds ds' H.
  - cbn in H. injection H as <-. exists O. reflexivity.
  - cbn [tickN] in H. destruct (tickF fuel ds) as [d1 |] eqn:E1; [| discriminate].
    destruct (tick_spec fuel ds d1 E1) as [m1 H1].
    destruct (IH d1 ds' H) as [m2 H2].
    exists (S m1 + m2). exact (steps_trans _ _ _ _ _ H1 H2).
Qed.

(** NIL tape right after the first ROOT event: 001 (10)^12 111 0^7 1. *)
Definition S12_7 : list bool :=
  [false; false; true] ++ rep10 12 ++ [true; true; true] ++ repeat false 7 ++ [true].

Lemma D0_to_S12_7 : tickN 3 27 D0 = Some S12_7.
Proof. vm_compute. reflexivity. Qed.

Corollary cfg0_to_S12_7 :
  exists m, steps TM80.cfg0 m (TM80.ret [] (dsyms S12_7 *> 0inf)).
Proof.
  destruct (tickN_spec 3 27 D0 S12_7 D0_to_S12_7) as [m Hm].
  exists (21 + m). exact (steps_trans _ _ _ _ _ cfg0_to_D0 Hm).
Qed.

(** *** Binary counter: LSB-first bits, width 2 at even positions, width 1 at odd ones *)

Fixpoint encb (odd : bool) (b : list bool) : list bool :=
  match b with
  | [] => []
  | x :: b' => (if odd then [x] else [x; x]) ++ encb (negb odd) b'
  end.

Lemma encb_even2 : forall u x l,
  encb false (repeat x (2 * u) ++ l) = repeat x (3 * u) ++ encb false l.
Proof.
  induction u as [| u IH]; intros x l; [reflexivity |].
  replace (2 * S u) with (S (S (2 * u))) by lia.
  replace (3 * S u) with (S (S (S (3 * u)))) by lia.
  cbn [repeat app encb negb]. rewrite IH. reflexivity.
Qed.

Lemma repeat_snoc1 {A : Type} (x : A) : forall m, repeat x m ++ [x] = x :: repeat x m.
Proof. induction m as [| m IH]; [reflexivity | cbn; rewrite IH; reflexivity]. Qed.

Lemma dec2_W1s : forall m pend l,
  dec2 pend (repeat TM80.W1 (2 * m) ++ l) =
  (fst (dec2 pend l) ++ repeat false m, snd (dec2 pend l)).
Proof.
  induction m as [| m IH]; intros pend l.
  - change (repeat TM80.W1 (2 * 0) ++ l) with l.
    destruct (dec2 pend l); cbn. rewrite app_nil_r. reflexivity.
  - replace (2 * S m) with (S (S (2 * m))) by lia.
    destruct pend; cbn [repeat app dec2]; rewrite IH; cbn;
      rewrite <- app_assoc, repeat_snoc1; reflexivity.
Qed.

Lemma scan_1101 :
  scanr Q4 [true; true; false; true] =
  Fin Q0 [TM80.W1; TM80.W10; TM80.W1; TM80.W1; TM80.W1; TM80.W1; TM80.W1].
Proof. reflexivity. Qed.

(** One NIL pass increments the counter: 1101 C(v) R  -->  10 001 C(v+1) R,
    where C(v) = ones t ++ false :: rest and C(v+1) = zeros t ++ true :: rest. *)
Theorem counter_inc_pass : forall t rest R,
  dpass Q4 [TM80.W10]
    ([true; true; false; true] ++ encb false (repeat true t ++ false :: rest) ++ R) =
  PNil ([true; false; false; false; true] ++ encb false (repeat false t ++ true :: rest) ++ R).
Proof.
  intros t rest R.
  destruct (Nat.Even_or_Odd t) as [[u ->] | [u ->]].
  - rewrite !encb_even2. unfold dpass. rewrite <- !app_assoc.
    rewrite scanr_app, scan_1101.
    rewrite scanr_app, scanr_ones3.
    cbn [scanr step1 stopstk app encb negb].
    unfold finish, dec.
    replace (6 * u) with (2 * (3 * u)) by lia.
    cbn [dec2]. rewrite <- app_assoc, dec2_W1s. cbn.
    rewrite <- !app_assoc. reflexivity.
  - rewrite !repeat_app_local, <- !app_assoc, !encb_even2.
    unfold dpass. rewrite <- !app_assoc.
    rewrite scanr_app, scan_1101.
    rewrite scanr_app, scanr_ones3.
    cbn [scanr step1 stopstk app encb negb repeat].
    unfold finish, dec.
    replace (6 * u) with (2 * (3 * u)) by lia.
    cbn [dec2 app].
    rewrite <- app_assoc, dec2_W1s. cbn.
    rewrite <- !app_assoc. reflexivity.
Qed.

(** A pass on a tape starting with digit 0 stops at once: 0 X --> 1 1 X. *)
Lemma pass_0 : forall X,
  dpass Q4 [TM80.W10] (false :: X) = PNil (true :: true :: X).
Proof. reflexivity. Qed.

Lemma rep10_S : forall k, rep10 (S k) = rep10 k ++ [true; false].
Proof. intro k. unfold rep10. apply concat_repeat_snoc. Qed.

Lemma tickN_add : forall f a b x,
  tickN f (a + b) x = match tickN f a x with Some y => tickN f b y | None => None end.
Proof.
  intros f a. induction a as [| a IH]; intros b x; [reflexivity |].
  cbn [tickN Nat.add]. destruct (tickF f x); [apply IH | reflexivity].
Qed.

(** Two ticks: (10)^k 1101 C R --> (10)^(k+1) 001 C' R --> (10)^(k+1) 1101 C' R. *)
Theorem counter_inc_tick2 : forall f k t rest R,
  tickN f 2 (rep10 k ++ [true; true; false; true] ++ encb false (repeat true t ++ false :: rest) ++ R) =
  Some (rep10 (S k) ++ [true; true; false; true] ++ encb false (repeat false t ++ true :: rest) ++ R).
Proof.
  intros f k t rest R. cbn [tickN].
  rewrite (tickF_shift_nil f k _ _ (counter_inc_pass t rest R)).
  replace (rep10 k ++ [true; false; false; false; true] ++ encb false (repeat false t ++ true :: rest) ++ R)
    with (rep10 (S k) ++ false :: ([false; true] ++ encb false (repeat false t ++ true :: rest) ++ R))
    by (rewrite rep10_S, <- app_assoc; reflexivity).
  rewrite (tickF_shift_nil f (S k) _ _ (pass_0 _)). reflexivity.
Qed.

(** LSB-first binary increment (no overflow case needed). *)
Fixpoint incb (b : list bool) : list bool :=
  match b with
  | [] => []
  | true :: b' => false :: incb b'
  | false :: b' => true :: b'
  end.

Lemma split_first_false : forall b, In false b ->
  exists t rest, b = repeat true t ++ false :: rest.
Proof.
  induction b as [| x b IH]; intros H; [destruct H |].
  destruct x.
  - destruct H as [H | H]; [discriminate |].
    destruct (IH H) as [t [rest ->]]. exists (S t), rest. reflexivity.
  - exists O, b. reflexivity.
Qed.

Lemma incb_split : forall t rest,
  incb (repeat true t ++ false :: rest) = repeat false t ++ true :: rest.
Proof. induction t as [| t IH]; intros rest; [reflexivity | cbn; rewrite IH; reflexivity]. Qed.

Theorem counter_inc : forall f k b R, In false b ->
  tickN f 2 (rep10 k ++ [true; true; false; true] ++ encb false b ++ R) =
  Some (rep10 (S k) ++ [true; true; false; true] ++ encb false (incb b) ++ R).
Proof.
  intros f k b R Hb. destruct (split_first_false b Hb) as [t [rest ->]].
  rewrite incb_split. apply counter_inc_tick2.
Qed.

(** m increments in 2m ticks, as long as no overflow happens on the way. *)
Theorem counter_run : forall f m k b R,
  (forall i, i < m -> In false (Nat.iter i incb b)) ->
  tickN f (2 * m) (rep10 k ++ [true; true; false; true] ++ encb false b ++ R) =
  Some (rep10 (k + m) ++ [true; true; false; true] ++ encb false (Nat.iter m incb b) ++ R).
Proof.
  intros f m. induction m as [| m IH]; intros k b R H.
  - rewrite Nat.add_0_r. reflexivity.
  - replace (2 * S m) with (2 + 2 * m) by lia.
    rewrite tickN_add, (counter_inc f k b R (H O ltac:(lia))).
    rewrite (IH (S k) (incb b) R).
    + rewrite <- Nat.iter_succ_r. replace (S k + m) with (k + S m) by lia. reflexivity.
    + intros i Hi. rewrite <- Nat.iter_succ_r. apply H. lia.
Qed.

(** *** Overflow of the low counter into the middle region *)

Lemma encb_even2_nil : forall u x, encb false (repeat x (2 * u)) = repeat x (3 * u).
Proof. intros u x. rewrite <- (app_nil_r (repeat x (2 * u))), encb_even2. apply app_nil_r. Qed.

Lemma rep10_SS : forall j, rep10 (S (S j)) = [true; false; true; false] ++ rep10 j.
Proof. reflexivity. Qed.

Lemma scan_Q0_1010 :
  scanr Q0 [true; false; true; false] = Fin Q4 [TM80.W10; TM80.W1; TM80.W10; TM80.W1; TM80.W1; TM80.W1].
Proof. reflexivity. Qed.

Lemma scan_Q0_101101 :
  scanr Q0 [true; false; true; true; false; true] =
  Fin Q0 [TM80.W1; TM80.W10; TM80.W1; TM80.W1; TM80.W1; TM80.W1; TM80.W10; TM80.W1; TM80.W1; TM80.W1].
Proof. reflexivity. Qed.

Lemma rep01_false : forall j Y, rep01 j ++ false :: Y = false :: rep10 j ++ Y.
Proof.
  unfold rep01, rep10. induction j as [| j IH]; intros Y; [reflexivity |].
  cbn [repeat concat app]. rewrite IH. reflexivity.
Qed.

Ltac ovf_dec :=
  unfold finish, dec;
  repeat match goal with |- context [repeat ?w (6 * ?x)] => replace (6 * x) with (2 * (3 * x)) by lia end;
  rewrite <- !app_assoc; cbn [app dec2];
  repeat (first [rewrite dec2_W1s | rewrite dec2_blocks]; cbn [app dec2 fst snd]);
  cbn; rewrite <- !app_assoc; cbn.

Theorem counter_overflow_pass : forall h j t rest T,
  dpass Q4 [TM80.W10]
    ([true; true; false; true] ++ encb false (repeat true (2 * h)) ++ rep10 (S j) ++
     [true; true; false; true] ++ encb false (repeat true t ++ false :: rest) ++ T) =
  PNil ([true; false; false; false; true] ++ encb false (repeat false (2 * h + 1) ++ [true]) ++
        rep10 j ++ [false; false; true] ++ encb false (repeat false t ++ true :: rest) ++ T).
Proof.
  intros h j t rest T.
  rewrite encb_even2_nil, repeat_app_local, <- app_assoc, encb_even2. cbn [encb negb app repeat].
  destruct (Nat.Even_or_Odd t) as [[u ->] | [u ->]].
  - rewrite !encb_even2. cbn [encb negb app].
    destruct j as [| j].
    + unfold dpass. cbn [rep10 repeat concat app]. rewrite <- !app_assoc. cbn [app].
      cbn [scanr step1]. rewrite scanr_app, scanr_ones3.
      cbn [scanr step1]. rewrite scanr_app, scanr_ones3.
      cbn [scanr step1 stopstk app].
      ovf_dec. reflexivity.
    + unfold dpass. rewrite rep10_SS. rewrite <- !app_assoc. cbn [app].
      cbn [scanr step1]. rewrite scanr_app, scanr_ones3.
      cbn [scanr step1]. rewrite scanr_app, scanr_rep10.
      cbn [scanr step1]. rewrite scanr_app, scanr_ones3.
      cbn [scanr step1 stopstk app].
      ovf_dec. rewrite rep01_false. reflexivity.
  - rewrite !repeat_app_local, <- !app_assoc, !encb_even2. cbn [encb negb app repeat].
    destruct j as [| j].
    + unfold dpass. cbn [rep10 repeat concat app]. rewrite <- !app_assoc. cbn [app].
      cbn [scanr step1]. rewrite scanr_app, scanr_ones3.
      cbn [scanr step1]. rewrite scanr_app, scanr_ones3.
      cbn [scanr step1 stopstk app].
      ovf_dec. reflexivity.
    + unfold dpass. rewrite rep10_SS. rewrite <- !app_assoc. cbn [app].
      cbn [scanr step1]. rewrite scanr_app, scanr_ones3.
      cbn [scanr step1]. rewrite scanr_app, scanr_rep10.
      cbn [scanr step1]. rewrite scanr_app, scanr_ones3.
      cbn [scanr step1 stopstk app].
      ovf_dec. rewrite rep01_false. reflexivity.
Qed.

(** Two ticks at a low-counter overflow (low counter of even width 2h, all ones):
    (10)^k 1101 C(1^2h) (10)^(j+1) 1101 C(b) T
    --> (10)^(k+1) 1101 C(0^(2h+1) 1) (10)^j 001 C(b+1) T. *)
Theorem counter_overflow_tick2 : forall f k h j b T, In false b ->
  tickN f 2 (rep10 k ++ [true; true; false; true] ++ encb false (repeat true (2 * h)) ++
             rep10 (S j) ++ [true; true; false; true] ++ encb false b ++ T) =
  Some (rep10 (S k) ++ [true; true; false; true] ++ encb false (repeat false (2 * h + 1) ++ [true]) ++
        rep10 j ++ [false; false; true] ++ encb false (incb b) ++ T).
Proof.
  intros f k h j b T Hb. destruct (split_first_false b Hb) as [t [rest ->]].
  rewrite incb_split. cbn [tickN].
  rewrite (tickF_shift_nil f k _ _ (counter_overflow_pass h j t rest T)).
  match goal with |- context [tickF f (rep10 k ++ [true; false; false; false; true] ++ ?Y)] =>
    replace (rep10 k ++ [true; false; false; false; true] ++ Y)
      with (rep10 (S k) ++ false :: ([false; true] ++ Y))
      by (rewrite rep10_S, <- app_assoc; reflexivity)
  end.
  rewrite (tickF_shift_nil f (S k) _ _ (pass_0 _)). reflexivity.
Qed.

(** *** Overflow against an upper gadget in its 001 phase *)

(** The scan stops on the first 0 of the 001 gadget, so whatever follows is untouched. *)
Theorem overflow2_pass : forall h J X,
  dpass Q4 [TM80.W10]
    ([true; true; false; true] ++ encb false (repeat true (2 * h)) ++ rep10 (S (S J)) ++ false :: X) =
  PNil ([true; false; false; false; true] ++ encb false (repeat false (2 * h + 1) ++ [true]) ++
        rep10 J ++ true :: true :: X).
Proof.
  intros h J X.
  rewrite encb_even2_nil, repeat_app_local, <- app_assoc, encb_even2. cbn [encb negb app repeat].
  unfold dpass. rewrite rep10_SS. rewrite <- !app_assoc. cbn [app].
  cbn [scanr step1]. rewrite scanr_app, scanr_ones3.
  cbn [scanr step1]. rewrite scanr_app, scanr_rep10.
  cbn [scanr step1 stopstk app].
  ovf_dec. rewrite (app_comm_cons (rep01 J) _ true), true_rep01, <- app_assoc. reflexivity.
Qed.

Theorem overflow2_tick2 : forall f k h J Y,
  tickN f 2 (rep10 k ++ [true; true; false; true] ++ encb false (repeat true (2 * h)) ++
             rep10 (S (S J)) ++ [false; false; true] ++ Y) =
  Some (rep10 (S k) ++ [true; true; false; true] ++ encb false (repeat false (2 * h + 1) ++ [true]) ++
        rep10 J ++ [true; true; false; true] ++ Y).
Proof.
  intros f k h J Y. cbn [tickN].
  change ([false; false; true] ++ Y) with (false :: ([false; true] ++ Y)).
  rewrite (tickF_shift_nil f k _ _ (overflow2_pass h J ([false; true] ++ Y))).
  match goal with |- context [tickF f (rep10 k ++ [true; false; false; false; true] ++ ?Z)] =>
    replace (rep10 k ++ [true; false; false; false; true] ++ Z)
      with (rep10 (S k) ++ false :: ([false; true] ++ Z))
      by (rewrite rep10_S, <- app_assoc; reflexivity)
  end.
  rewrite (tickF_shift_nil f (S k) _ _ (pass_0 _)). reflexivity.
Qed.

(** *** Bit values *)

Fixpoint bval (b : list bool) : nat :=
  match b with [] => O | x :: b' => (if x then 1 else 0) + 2 * bval b' end.

Lemma incb_length : forall b, length (incb b) = length b.
Proof. induction b as [| [] b IH]; cbn; congruence. Qed.

Lemma incb_val : forall b, In false b -> bval (incb b) = S (bval b).
Proof.
  induction b as [| [] b IH]; intros H; [destruct H | |].
  - destruct H as [H | H]; [discriminate |]. cbn [incb bval]. rewrite (IH H). lia.
  - cbn. lia.
Qed.

Lemma bval_lt : forall b, bval b < 2 ^ length b.
Proof. induction b as [| [] b IH]; cbn [bval length]; rewrite ?Nat.pow_succ_r'; cbn; lia. Qed.

Lemma bval_full_in_false : forall b, S (bval b) < 2 ^ length b -> In false b.
Proof.
  induction b as [| x b IH]; intros H; [cbn in H; lia |].
  destruct x; [right | left; reflexivity].
  apply IH. cbn [bval length] in H. rewrite Nat.pow_succ_r' in H. lia.
Qed.

Lemma bval_all_ones : forall b, S (bval b) = 2 ^ length b -> b = repeat true (length b).
Proof.
  induction b as [| x b IH]; intros H; [reflexivity |].
  cbn [bval length] in H. rewrite Nat.pow_succ_r' in H.
  pose proof (bval_lt b).
  destruct x; cbn [repeat length]; [rewrite <- IH by lia; reflexivity | lia].
Qed.

Lemma iter_incb : forall m b, bval b + m < 2 ^ length b ->
  bval (Nat.iter m incb b) = bval b + m /\ length (Nat.iter m incb b) = length b /\
  (forall i, i < m -> In false (Nat.iter i incb b)).
Proof.
  induction m as [| m IH]; intros b H.
  - split; [cbn; lia | split; [reflexivity | intros i Hi; lia]].
  - destruct (IH b ltac:(lia)) as [Hv [Hl Hin]].
    assert (Hm : In false (Nat.iter m incb b)) by (apply bval_full_in_false; rewrite Hv, Hl; lia).
    rewrite Nat.iter_succ, incb_val, incb_length by exact Hm.
    repeat split; [lia | exact Hl |].
    intros i Hi. destruct (Nat.eq_dec i m) as [-> | Hne]; [exact Hm | apply Hin; lia].
Qed.

(** From 1 0^... (value 2^(n-1)) to all ones in 2^(n-1)-1 increments. *)
Lemma fill_low : forall h,
  let L := repeat false (2 * h + 1) ++ [true] in
  let m := 2 ^ (2 * h + 1) - 1 in
  Nat.iter m incb L = repeat true (2 * h + 2) /\ (forall i, i < m -> In false (Nat.iter i incb L)).
Proof.
  intros h L m.
  assert (HvL : bval L = 2 ^ (2 * h + 1)).
  { unfold L. generalize (2 * h + 1) as q. induction q as [| q IH]; [reflexivity |].
    cbn [repeat app bval]. rewrite IH, Nat.pow_succ_r'. lia. }
  assert (HlL : length L = 2 * h + 2) by (unfold L; rewrite length_app, repeat_length; cbn; lia).
  assert (Hp : 2 ^ (2 * h + 2) = 2 * 2 ^ (2 * h + 1)) by (rewrite <- Nat.pow_succ_r'; f_equal; lia).
  assert (Hpos : 2 ^ (2 * h + 1) >= 1) by (apply Nat.le_succ_l, Nat.neq_0_lt_0, Nat.pow_nonzero; lia).
  destruct (iter_incb m L) as [Hv [Hl Hin]]; [unfold m; rewrite HvL, HlL, Hp; lia |].
  split; [| exact Hin].
  rewrite (bval_all_ones _); rewrite Hl, HlL; [reflexivity |].
  rewrite Hv, HvL, Hp. unfold m. lia.
Qed.

(** *** The tier-2 double cycle *)

Definition Ptape (k n j : nat) (b R : list bool) : list bool :=
  rep10 k ++ [true; true; false; true] ++ encb false (repeat true n) ++ rep10 j ++
  [true; true; false; true] ++ encb false b ++ R.

Theorem double_cycle : forall f k h J b R, In false b ->
  tickN f (2 ^ (2 * h + 2) + 2 ^ (2 * h + 4)) (Ptape k (2 * h) (J + 3) b R) =
  Some (Ptape (k + 2 ^ (2 * h + 1) + 2 ^ (2 * h + 3)) (2 * h + 4) J (incb b) R).
Proof.
  intros f k h J b R Hb.
  set (N := 2 ^ (2 * h + 1)).
  assert (HN : N >= 1) by (apply Nat.le_succ_l, Nat.neq_0_lt_0, Nat.pow_nonzero; lia).
  assert (H2 : 2 ^ (2 * h + 2) = 2 * N) by (unfold N; rewrite <- Nat.pow_succ_r'; f_equal; lia).
  assert (H3 : 2 ^ (2 * h + 3) = 4 * N)
    by (unfold N; replace (2 * h + 3) with (S (S (2 * h + 1))) by lia; rewrite !Nat.pow_succ_r'; lia).
  assert (H4 : 2 ^ (2 * h + 4) = 8 * N)
    by (unfold N; replace (2 * h + 4) with (S (S (S (2 * h + 1)))) by lia; rewrite !Nat.pow_succ_r'; lia).
  destruct (fill_low h) as [Hf1 Hi1]. fold N in Hf1, Hi1.
  destruct (fill_low (S h)) as [Hf2 Hi2].
  replace (2 * S h + 1) with (2 * h + 3) in Hf2, Hi2 by lia.
  replace (2 * S h + 2) with (2 * h + 4) in Hf2 by lia.
  rewrite H3 in Hf2, Hi2.
  replace (2 ^ (2 * h + 2) + 2 ^ (2 * h + 4))
    with (2 + (2 * (N - 1) + (2 + 2 * (4 * N - 1)))) by lia.
  unfold Ptape.
  (* overflow #1 *)
  rewrite tickN_add. replace (J + 3) with (S (J + 2)) by lia.
  rewrite (counter_overflow_tick2 f k h (J + 2) b R Hb).
  (* fill the low counter *)
  rewrite tickN_add.
  rewrite (counter_run f (N - 1) (S k) (repeat false (2 * h + 1) ++ [true])
             (rep10 (J + 2) ++ [false; false; true] ++ encb false (incb b) ++ R) Hi1).
  rewrite Hf1.
  (* overflow #2 against the 001 gadget *)
  rewrite tickN_add. replace (J + 2) with (S (S J)) by lia.
  replace (2 * h + 2) with (2 * S h) by lia.
  rewrite (overflow2_tick2 f (S k + (N - 1)) (S h) J (encb false (incb b) ++ R)).
  replace (2 * S h + 1) with (2 * h + 3) by lia.
  rewrite (counter_run f (4 * N - 1) (S (S k + (N - 1))) (repeat false (2 * h + 3) ++ [true])
             (rep10 J ++ [true; true; false; true] ++ encb false (incb b) ++ R) Hi2).
  rewrite Hf2. rewrite H3.
  replace (S (S k + (N - 1)) + (4 * N - 1)) with (k + N + 4 * N) by lia.
  reflexivity.
Qed.

(** *** Bulk: T double cycles *)

Theorem double_cycles : forall f T k h J b R, bval b + T < 2 ^ length b ->
  exists cnt k',
    tickN f cnt (Ptape k (2 * h) (J + 3 * T) b R) =
    Some (Ptape k' (2 * h + 4 * T) J (Nat.iter T incb b) R).
Proof.
  intros f T. induction T as [| T IH]; intros k h J b R H.
  - exists O, k. rewrite Nat.add_0_r, Nat.add_0_r. reflexivity.
  - assert (Hb : In false b) by (apply bval_full_in_false; lia).
    replace (J + 3 * S T) with ((J + 3 * T) + 3) by lia.
    destruct (IH (k + 2 ^ (2 * h + 1) + 2 ^ (2 * h + 3)) (h + 2) J (incb b) R) as [c2 [k2 Hc]].
    { rewrite incb_val, incb_length by exact Hb. lia. }
    exists (2 ^ (2 * h + 2) + 2 ^ (2 * h + 4) + c2), k2.
    rewrite tickN_add, (double_cycle f k h (J + 3 * T) b R Hb).
    replace (2 * h + 4) with (2 * (h + 2)) by lia.
    rewrite Hc. rewrite <- Nat.iter_succ_r.
    replace (2 * (h + 2) + 4 * T) with (2 * h + 4 * S T) by lia. reflexivity.
Qed.

(** Sanity: one double cycle by computation (n = 2, j = 3, upper counter 3 bits = 0). *)
Lemma double_cycle_sanity :
  tickN 3 (2 ^ 4 + 2 ^ 6) (Ptape 1 2 3 [false; false; false] [true]) =
  Some (Ptape (1 + 2 ^ 3 + 2 ^ 5) 6 0 [true; false; false] [true]).
Proof. vm_compute. reflexivity. Qed.

Ltac ent_dec :=
  unfold finish, dec;
  try rewrite <- !app_assoc; cbn [app dec2];
  repeat (first [rewrite dec2_W1s | rewrite dec2_blocks]; cbn [app dec2 fst snd]);
  cbn; try rewrite <- !app_assoc; cbn.

(** *** Level entry: S(M,a,w) = 001 (10)^M 111 0^a w reaches P0 in 21 ticks *)

Definition Slev (M a : nat) (w : list bool) : list bool :=
  [false; false; true] ++ rep10 M ++ [true; true; true] ++ repeat false a ++ w.

(** Tick 1 -> 2: the scan crosses (10)^M and 111 and stops on the first 0 of 0^a. *)
Lemma entry_pass1 : forall J Z,
  dpass Q4 [TM80.W10] ([true; true; false; true] ++ rep10 (S (S J)) ++ [true; true; true] ++ false :: Z) =
  PNil ([true; false; false; false; true; false; false; true] ++ rep10 (S J) ++ [false; false; true] ++ Z).
Proof.
  intros J Z. unfold dpass. rewrite rep10_SS. rewrite <- !app_assoc. cbn [app].
  cbn [scanr step1]. rewrite scanr_app, scanr_rep10.
  cbn [scanr step1 stopstk app].
  ovf_dec. rewrite rep01_false. reflexivity.
Qed.

(** Tick 5 -> 6: the scan crosses (10)^(M-1) and stops on the first 0 of 001. *)
Lemma entry_pass5 : forall J Z,
  dpass Q4 [TM80.W10]
    ([true; false; true; false; true; true; false; true; true; true; true] ++ rep10 (S (S J)) ++
     [false; false; true] ++ Z) =
  PNil (rep10 3 ++ [false; false; true; false; false; false; false; false; true] ++ rep10 J ++
        [true; true; false; true] ++ Z).
Proof.
  intros J Z. unfold dpass. rewrite rep10_SS. rewrite <- !app_assoc. cbn [app].
  cbn [scanr step1]. rewrite scanr_app, scanr_rep10.
  cbn [scanr step1 stopstk app].
  ent_dec. rewrite (app_comm_cons (rep01 J) _ true), true_rep01, <- app_assoc. reflexivity.
Qed.

(** The 7 ticks from S(J+3, a+1, w) to the first P-like tape. Ticks 0, 2, 3, 4, 6 stop in a
    fixed prefix, so they hold by computation with the rest of the tape opaque. *)
Definition et0 J Z := [false; false; true] ++ rep10 (S (S (S J))) ++ [true; true; true] ++ false :: Z.
Definition et1 J Z := [true; true; false; true] ++ rep10 (S (S (S J))) ++ [true; true; true] ++ false :: Z.
Definition et2 J Z := [true; false; false; false; true; false; false; true] ++ rep10 (S (S J)) ++ [false; false; true] ++ Z.
Definition et3 J Z := [true; false; true; true; false; true; false; false; true] ++ rep10 (S (S J)) ++ [false; false; true] ++ Z.
Definition et4 J Z := [true; false; true; false; false; false; true; true; true; true] ++ rep10 (S (S J)) ++ [false; false; true] ++ Z.
Definition et5 J Z := [true; false; true; false; true; true; false; true; true; true; true] ++ rep10 (S (S J)) ++ [false; false; true] ++ Z.
Definition et6 J Z := rep10 3 ++ [false; false; true; false; false; false; false; false; true] ++ rep10 J ++ [true; true; false; true] ++ Z.
Definition et7 J Z := rep10 3 ++ [true; true; false; true] ++ encb false (repeat false 3 ++ [true]) ++ rep10 J ++ [true; true; false; true] ++ Z.

Lemma et_01 : forall f J Z, tickF f (et0 J Z) = Some (et1 J Z).
Proof. intros. reflexivity. Qed.
Lemma et_12 : forall f J Z, tickF f (et1 J Z) = Some (et2 J Z).
Proof. intros. unfold tickF, et1. rewrite entry_pass1. reflexivity. Qed.
Lemma et_23 : forall f J Z, tickF f (et2 J Z) = Some (et3 J Z).
Proof. intros. reflexivity. Qed.
Lemma et_34 : forall f J Z, tickF f (et3 J Z) = Some (et4 J Z).
Proof. intros. reflexivity. Qed.
Lemma et_45 : forall f J Z, tickF f (et4 J Z) = Some (et5 J Z).
Proof. intros. reflexivity. Qed.
Lemma et_56 : forall f J Z, tickF f (et5 J Z) = Some (et6 J Z).
Proof. intros. unfold tickF, et5. rewrite entry_pass5. reflexivity. Qed.
Lemma et_67 : forall f J Z, tickF f (et6 J Z) = Some (et7 J Z).
Proof.
  intros. unfold et6.
  change ([false; false; true; false; false; false; false; false; true] ++ rep10 J ++ [true; true; false; true] ++ Z)
    with (false :: ([false; true; false; false; false; false; false; true] ++ rep10 J ++ [true; true; false; true] ++ Z)).
  rewrite (tickF_shift_nil f 3 _ _ (pass_0 _)). reflexivity.
Qed.

(** The 7 ticks from S(J+3, a+1, w) to the first P-like tape. *)
Lemma entry_tick7 : forall f J Z, tickN f 7 (et0 J Z) = Some (et7 J Z).
Proof.
  intros f J Z. cbn [tickN].
  rewrite et_01; cbn [tickN]. rewrite et_12; cbn [tickN]. rewrite et_23; cbn [tickN].
  rewrite et_34; cbn [tickN]. rewrite et_45; cbn [tickN]. rewrite et_56; cbn [tickN].
  rewrite et_67. reflexivity.
Qed.

Lemma bval_repeat_false : forall n, bval (repeat false n) = O.
Proof. induction n as [| n IH]; cbn; [reflexivity | rewrite IH; reflexivity]. Qed.

(** Level entry: from S(J+3, 3u+1, w) to P0 = Ptape 10 4 J 0^(2u) w in 21 ticks. *)
Theorem level_entry : forall f J u w,
  tickN f 21 (Slev (S (S (S J))) (3 * u + 1) w) = Some (Ptape 10 4 J (repeat false (2 * u)) w).
Proof.
  intros f J u w.
  replace (Slev (S (S (S J))) (3 * u + 1) w) with (et0 J (repeat false (3 * u) ++ w))
    by (unfold Slev, et0; replace (3 * u + 1) with (S (3 * u)) by lia; reflexivity).
  change 21 with (7 + 2 * 7). rewrite tickN_add, entry_tick7. unfold et7, Ptape.
  destruct (fill_low 1) as [Hf Hi]. cbn [Nat.mul Nat.add Nat.pow Nat.sub] in Hf, Hi.
  rewrite (counter_run f 7 3 (repeat false 3 ++ [true])
             (rep10 J ++ [true; true; false; true] ++ repeat false (3 * u) ++ w) Hi).
  rewrite Hf. rewrite encb_even2_nil. reflexivity.
Qed.

(** Level bulk: S(je + 3T + 3, 3u+1, w) reaches Ptape k' (4 + 4T) je b' w with bval b' = T,
    as long as the upper counter (2u bits) does not overflow. *)
Theorem level_bulk : forall f je T u w, T < 2 ^ (2 * u) ->
  exists cnt k' b',
    tickN f cnt (Slev (je + 3 * T + 3) (3 * u + 1) w) = Some (Ptape k' (4 + 4 * T) je b' w) /\
    bval b' = T /\ length b' = 2 * u.
Proof.
  intros f je T u w HT.
  destruct (double_cycles f T 10 2 je (repeat false (2 * u)) w) as [c [k' Hc]].
  { rewrite bval_repeat_false, repeat_length. lia. }
  destruct (iter_incb T (repeat false (2 * u))) as [Hv [Hl _]].
  { rewrite bval_repeat_false, repeat_length. lia. }
  exists (21 + c), k', (Nat.iter T incb (repeat false (2 * u))).
  split; [| rewrite Hv, Hl, bval_repeat_false, repeat_length; lia].
  replace (je + 3 * T + 3) with (S (S (S (je + 3 * T)))) by lia.
  rewrite tickN_add, level_entry. exact Hc.
Qed.

(** The exact prefix length after T double cycles. *)
Fixpoint kcyc (h T k : nat) : nat :=
  match T with
  | O => k
  | S T' => kcyc (h + 2) T' (k + 2 ^ (2 * h + 1) + 2 ^ (2 * h + 3))
  end.

Theorem double_cycles_exact : forall f T k h J b R, bval b + T < 2 ^ length b ->
  exists cnt,
    tickN f cnt (Ptape k (2 * h) (J + 3 * T) b R) =
    Some (Ptape (kcyc h T k) (2 * h + 4 * T) J (Nat.iter T incb b) R).
Proof.
  intros f T. induction T as [| T IH]; intros k h J b R H.
  - exists O. rewrite Nat.add_0_r, Nat.add_0_r. reflexivity.
  - assert (Hb : In false b) by (apply bval_full_in_false; lia).
    replace (J + 3 * S T) with ((J + 3 * T) + 3) by lia.
    destruct (IH (k + 2 ^ (2 * h + 1) + 2 ^ (2 * h + 3)) (h + 2) J (incb b) R) as [c2 Hc].
    { rewrite incb_val, incb_length by exact Hb. lia. }
    exists (2 ^ (2 * h + 2) + 2 ^ (2 * h + 4) + c2).
    rewrite tickN_add, (double_cycle f k h (J + 3 * T) b R Hb).
    replace (2 * h + 4) with (2 * (h + 2)) by lia.
    rewrite Hc. rewrite <- Nat.iter_succ_r.
    replace (2 * (h + 2) + 4 * T) with (2 * h + 4 * S T) by lia. reflexivity.
Qed.

(** Closed form: 3 kcyc h T k + 2^(2h+1) = 3k + 2^(2h+1) 16^T. *)
Lemma kcyc_closed : forall T h k,
  3 * kcyc h T k + 2 ^ (2 * h + 1) = 3 * k + 2 ^ (2 * h + 1) * 16 ^ T.
Proof.
  induction T as [| T IH]; intros h k; [cbn; lia |].
  cbn [kcyc]. specialize (IH (h + 2) (k + 2 ^ (2 * h + 1) + 2 ^ (2 * h + 3))).
  set (P := 2 ^ (2 * h + 1)) in *.
  assert (E3 : 2 ^ (2 * h + 3) = 4 * P)
    by (unfold P; replace (2 * h + 3) with (S (S (2 * h + 1))) by lia; rewrite !Nat.pow_succ_r'; lia).
  assert (E5 : 2 ^ (2 * (h + 2) + 1) = 16 * P)
    by (unfold P; replace (2 * (h + 2) + 1) with (S (S (S (S (2 * h + 1))))) by lia;
        rewrite !Nat.pow_succ_r'; lia).
  rewrite E3, E5 in IH. rewrite E3. rewrite Nat.pow_succ_r'.
  set (Q := 16 ^ T) in *.
  replace (16 * P * Q) with (16 * (P * Q)) in IH by lia.
  replace (P * (16 * Q)) with (16 * (P * Q)) by lia.
  lia.
Qed.

(** Level bulk with the exact prefix: k' = 10 + 32 (16^T - 1) / 3, i.e. 3 k' + 32 = 30 + 32 * 16^T. *)
Theorem level_bulk_exact : forall f je T u w, T < 2 ^ (2 * u) ->
  exists cnt b',
    tickN f cnt (Slev (je + 3 * T + 3) (3 * u + 1) w) =
      Some (Ptape (kcyc 2 T 10) (4 + 4 * T) je b' w) /\
    bval b' = T /\ length b' = 2 * u /\ 3 * kcyc 2 T 10 + 32 = 30 + 32 * 16 ^ T.
Proof.
  intros f je T u w HT.
  destruct (double_cycles_exact f T 10 2 je (repeat false (2 * u)) w) as [c Hc].
  { rewrite bval_repeat_false, repeat_length. lia. }
  destruct (iter_incb T (repeat false (2 * u))) as [Hv [Hl _]].
  { rewrite bval_repeat_false, repeat_length. lia. }
  exists (21 + c), (Nat.iter T incb (repeat false (2 * u))).
  split; [| split; [rewrite Hv, bval_repeat_false; lia |
                    split; [rewrite Hl, repeat_length; reflexivity | exact (kcyc_closed T 2 10)]]].
  replace (je + 3 * T + 3) with (S (S (S (je + 3 * T)))) by lia.
  rewrite tickN_add, level_entry. exact Hc.
Qed.

(** Sanity: S12_7 is S(12, 7, 1); level_entry by computation there. *)
Lemma S12_7_Slev : S12_7 = Slev 12 7 [true].
Proof. reflexivity. Qed.

Lemma level_entry_sanity :
  tickN 3 21 (Slev 12 7 [true]) = Some (Ptape 10 4 9 (repeat false 4) [true]).
Proof. vm_compute. reflexivity. Qed.

End T694_levels.

Module End694.

(** * Line 694, bottom layer of the halting direction

    On top of [T694_levels] (ticks are machine steps, the prefix (10)^k is inert, counter runs):
    - [tick_halt], [halt_from_ticks]: a tick whose first pass ends in the undefined clause halts the machine;
    - [counter_fill]: the first counter runs to all ones, with the number of ticks kept symbolic;
    - [estep], [erun]: an evaluator for the end phase that works on the part of the tape after the prefix
      (10)^k, with a soundness theorem;
    - [prefix28_halts]: the end phase of class 3, tail 1, input 00 1^18 0^7 1 (half-width 1) reaches the
      undefined clause, for every prefix length k.

    Nothing here says that the machine reaches that end phase. *)

Import Individual62.
Import T694_levels.
Import Lia PeanoNat.
Import Coq.Lists.List.
Import ListNotations.

(** ** Halting direction *)

Lemma iter_opt_none_halts {A : Type} (f : A -> option A) : forall n x,
  iter_opt f n x = None -> iter_halts f x.
Proof.
  induction n as [| n IH]; intros x H; [discriminate |].
  cbn [iter_opt] in H. destruct (f x) as [y |] eqn:E.
  - exact (iter_halts_S f x y E (IH y H)).
  - exact (iter_halts_O f x E).
Qed.

Lemma finish_not_halt : forall stk tail, finish stk tail <> PHalt.
Proof. intros stk tail. unfold finish. destruct (dec stk) as [o []]; discriminate. Qed.

Lemma tick_halt : forall ds,
  dpass Q4 [TM80.W10] ds = PHalt ->
  exists n, iter_opt TM80.f n (TM80.ret [] (dsyms ds *> 0inf)) = None.
Proof.
  intros ds H. unfold dpass in H.
  destruct (scanr Q4 ds) as [s' p | p rest] eqn:E.
  - destruct (safe_end s') eqn:Es.
    + exfalso. exact (finish_not_halt _ _ H).
    + destruct (scan_to_end_unsafe ds Q4 s' p [TM80.W10] E Es) as [n Hn].
      exists (S n). change (S n) with (S O + n).
      pose proof (ret_nil_start (dsyms ds *> 0inf)) as H0. unfold steps in H0.
      rewrite (iter_opt_add TM80.f (S O) n _ _ H0). exact Hn.
  - exfalso. exact (finish_not_halt _ _ H).
Qed.

Theorem halt_from_ticks : forall fuel n ds,
  tickN fuel n D0 = Some ds ->
  dpass Q4 [TM80.W10] ds = PHalt ->
  halts tm c0.
Proof.
  intros fuel n ds Ht Hh. rewrite halts_tm_iff_iter.
  destruct (tickN_spec fuel n D0 ds Ht) as [m Hm].
  destruct (tick_halt ds Hh) as [n2 H2].
  pose proof cfg0_to_D0 as H0. unfold steps in *.
  apply (iter_opt_none_halts TM80.f (21 + (m + n2))).
  rewrite (iter_opt_add TM80.f 21 (m + n2) _ _ H0).
  rewrite (iter_opt_add TM80.f m n2 _ _ Hm). exact H2.
Qed.

(** ** The fill of the first counter *)

Definition c1101 : list bool := [true; true; false; true].

Theorem counter_fill : forall f k b R,
  tickN f (2 * (2 ^ length b - 1 - bval b)) (rep10 k ++ c1101 ++ encb false b ++ R) =
  Some (rep10 (k + (2 ^ length b - 1 - bval b)) ++ c1101 ++ encb false (repeat true (length b)) ++ R).
Proof.
  intros f k b R. pose proof (bval_lt b) as Hlt.
  remember (2 ^ length b - 1 - bval b) as m eqn:Em.
  assert (Hm : bval b + m < 2 ^ length b) by lia.
  destruct (iter_incb m b Hm) as [Hv [Hl Hin]].
  unfold c1101. rewrite (counter_run f m k b R Hin).
  assert (Nat.iter m incb b = repeat true (length b)) as ->.
  { rewrite <- Hl. apply bval_all_ones. rewrite Hv, Hl. lia. }
  reflexivity.
Qed.

(** ** Reachability modulo the prefix *)

Definition Reach (X Y : list bool) : Prop :=
  forall k, exists n k', tickN 3 n (rep10 k ++ X) = Some (rep10 k' ++ Y).

Lemma reach_refl : forall X, Reach X X.
Proof. intros X k. exists O, k. reflexivity. Qed.

Lemma reach_trans : forall X Y Z, Reach X Y -> Reach Y Z -> Reach X Z.
Proof.
  intros X Y Z H1 H2 k. destruct (H1 k) as [n1 [k1 E1]]. destruct (H2 k1) as [n2 [k2 E2]].
  exists (n1 + n2), k2. rewrite tickN_add, E1. exact E2.
Qed.

Lemma reach_tick : forall X Y, dpass Q4 [TM80.W10] X = PNil Y -> Reach X Y.
Proof.
  intros X Y H k. exists (S O), k. cbn [tickN]. rewrite (tickF_shift_nil 3 k X Y H). reflexivity.
Qed.

Lemma reach_strip : forall X, Reach (true :: false :: X) X.
Proof.
  intros X k. exists O, (S k). cbn [tickN]. rewrite rep10_S, <- app_assoc. reflexivity.
Qed.

Lemma reach_fill : forall b R,
  Reach (c1101 ++ encb false b ++ R) (c1101 ++ encb false (repeat true (length b)) ++ R).
Proof.
  intros b R k. eexists. eexists. apply counter_fill.
Qed.

(** ** The evaluator *)

(** Longest prefix of [cs] of the form [encb odd b]. *)
Fixpoint parse (odd : bool) (cs : list bool) : list bool * list bool :=
  match cs with
  | [] => ([], [])
  | x :: cs1 =>
    if odd then let (b, rs) := parse false cs1 in (x :: b, rs)
    else match cs1 with
         | [] => ([], cs)
         | y :: cs2 => if Bool.eqb x y then let (b, rs) := parse true cs2 in (x :: b, rs) else ([], cs)
         end
  end.

Lemma parse_spec : forall n cs, length cs <= n -> forall odd b rs,
  parse odd cs = (b, rs) -> cs = encb odd b ++ rs.
Proof.
  induction n as [| n IH]; intros cs Hn odd b rs H.
  - destruct cs; [| cbn in Hn; lia]. cbn in H. injection H as <- <-. reflexivity.
  - destruct cs as [| x cs1]; [cbn in H; injection H as <- <-; reflexivity |].
    cbn [length] in Hn. destruct odd.
    + cbn [parse] in H. destruct (parse false cs1) as [b1 rs1] eqn:E. injection H as <- <-.
      cbn [encb negb app]. f_equal. apply (IH cs1); [lia | exact E].
    + cbn [parse] in H. destruct cs1 as [| y cs2]; [injection H as <- <-; reflexivity |].
      destruct (Bool.eqb x y) eqn:Exy; [| injection H as <- <-; reflexivity].
      apply Bool.eqb_prop in Exy. subst y.
      destruct (parse true cs2) as [b1 rs1] eqn:E. injection H as <- <-.
      cbn [encb negb app]. do 2 f_equal.
      apply (IH cs2); [cbn [length] in Hn; lia | exact E].
Qed.

Definition tick1 (X : list bool) : option (list bool) :=
  match dpass Q4 [TM80.W10] X with PNil Y => Some Y | _ => None end.

Definition estep (X : list bool) : option (list bool) :=
  match X with
  | true :: false :: X' => Some X'
  | true :: true :: false :: true :: cs =>
    let (b, rs) := parse false cs in
    if forallb (fun x => x) b then tick1 X
    else Some (c1101 ++ encb false (repeat true (length b)) ++ rs)
  | _ => tick1 X
  end.

Lemma tick1_sound : forall X Y, tick1 X = Some Y -> Reach X Y.
Proof.
  intros X Y H. unfold tick1 in H.
  destruct (dpass Q4 [TM80.W10] X) as [| Y' |] eqn:E; try discriminate.
  injection H as <-. exact (reach_tick X Y' E).
Qed.

Lemma estep_sound : forall X Y, estep X = Some Y -> Reach X Y.
Proof.
  intros X Y H. unfold estep in H.
  destruct X as [| [] X1]; try exact (tick1_sound _ _ H).
  destruct X1 as [| [] X2]; try exact (tick1_sound _ _ H).
  - destruct X2 as [| [] X3]; try exact (tick1_sound _ _ H).
    destruct X3 as [| [] cs]; try exact (tick1_sound _ _ H).
    destruct (parse false cs) as [b rs] eqn:E.
    destruct (forallb (fun x => x) b); [exact (tick1_sound _ _ H) |].
    injection H as <-.
    rewrite (parse_spec (length cs) cs (le_n _) false b rs E).
    exact (reach_fill b rs).
  - injection H as <-. apply reach_strip.
Qed.

(** Run until the first pass of a tick ends in the undefined clause. *)
Fixpoint erun (fuel : nat) (X : list bool) : option (list bool) :=
  match fuel with
  | O => None
  | S f =>
    match dpass Q4 [TM80.W10] X with
    | PHalt => Some X
    | _ => match estep X with Some Y => erun f Y | None => None end
    end
  end.

Lemma erun_sound : forall fuel X Y, erun fuel X = Some Y ->
  Reach X Y /\ dpass Q4 [TM80.W10] Y = PHalt.
Proof.
  induction fuel as [| f IH]; intros X Y H; [discriminate |].
  cbn [erun] in H.
  destruct (dpass Q4 [TM80.W10] X) as [| d | T] eqn:E.
  - injection H as <-. split; [apply reach_refl | exact E].
  - destruct (estep X) as [X1 |] eqn:E1; [| discriminate].
    destruct (IH X1 Y H) as [HR HH]. split; [| exact HH].
    exact (reach_trans _ _ _ (estep_sound _ _ E1) HR).
  - destruct (estep X) as [X1 |] eqn:E1; [| discriminate].
    destruct (IH X1 Y H) as [HR HH]. split; [| exact HH].
    exact (reach_trans _ _ _ (estep_sound _ _ E1) HR).
Qed.

Theorem erun_halts : forall fuel X Y, erun fuel X = Some Y ->
  forall k, exists n ds, tickN 3 n (rep10 k ++ X) = Some ds /\ dpass Q4 [TM80.W10] ds = PHalt.
Proof.
  intros fuel X Y H k. destruct (erun_sound fuel X Y H) as [HR HH].
  destruct (HR k) as [n [k' E]]. exists n, (rep10 k' ++ Y).
  split; [exact E | exact (dpass_shift_halt k' Y HH)].
Qed.

(** ** The halting end phase on the 28 top bits of the level-14 input *)

(** T = 00 1^18 0^7 1 (high bit first), listed low bit first. *)
Definition bits28 : list bool := [true] ++ repeat false 7 ++ repeat true 18 ++ [false; false].

(** End-phase start of class 3 (three pairs 10 between the counters), tail 1, half-width [hr]. *)
Definition start28 (hr : nat) : list bool :=
  c1101 ++ repeat true (3 * hr) ++ rep10 3 ++ c1101 ++ encb false bits28 ++ [true].

Theorem prefix28_halts : forall k, exists n ds,
  tickN 3 n (rep10 k ++ start28 1) = Some ds /\ dpass Q4 [TM80.W10] ds = PHalt.
Proof.
  assert (H : exists Y, erun 40 (start28 1) = Some Y) by (vm_compute; eexists; reflexivity).
  destruct H as [Y H]. exact (erun_halts 40 (start28 1) Y H).
Qed.

End End694.

Module Sym694.

(** * Line 694: the end phase with a first counter of symbolic width

    A state is [pre ++ repeat x (3 * t) ++ post] with [t] arbitrary: [3 * t] hidden cells, all ones or all zeros,
    inside the first counter.  A tick turns hidden ones into hidden zeros ([tickS_sound]: the scan crosses 111 in
    the state cycle Q0 -> Q5 -> Q2 -> Q0 and the six W1 it pushes decode to 000), a fill turns them back into ones
    ([fillS_sound]), and ticks that stop before the hidden cells do not see them.
    [prefix28_halts_all]: the halting end phase of [End694.prefix28_halts], for every half-width. *)

Import Individual62.
Import T694_levels End694.
Import Lia PeanoNat Bool.
Import Coq.Lists.List.
Import ListNotations.

Lemma scanr_ones3 : forall t,
  scanr Q0 (repeat true (3 * t)) = Fin Q0 (repeat TM80.W1 (2 * (3 * t))).
Proof.
  induction t as [| t IH]; [reflexivity |].
  replace (3 * S t) with (3 + 3 * t) by lia.
  rewrite repeat_app, scanr_app. cbn [repeat scanr step1 app]. rewrite IH.
  replace (2 * (3 + 3 * t)) with (2 * (3 * t) + 6) by lia. rewrite repeat_app. reflexivity.
Qed.

(** [dec2_app] with the witnesses computed. *)
Fixpoint dec2p (pend : bool) (p : list TM80.Word) : bool * list bool :=
  match p with
  | [] => (pend, [])
  | TM80.W10 :: p' => let (pd, q) := dec2p pend p' in (pd, q ++ [true])
  | TM80.W1 :: p' =>
    if pend then let (pd, q) := dec2p false p' in (pd, q ++ [false]) else dec2p true p'
  end.

Lemma dec2p_spec : forall p pend l,
  dec2 pend (p ++ l) =
  (fst (dec2 (fst (dec2p pend p)) l) ++ snd (dec2p pend p), snd (dec2 (fst (dec2p pend p)) l)).
Proof.
  induction p as [| w p IH]; intros pend l.
  - cbn. destruct (dec2 pend l); cbn. rewrite app_nil_r. reflexivity.
  - destruct w; [destruct pend |]; cbn [app dec2 dec2p].
    + rewrite IH. destruct (dec2p false p) as [pd q]. cbn. rewrite app_assoc. reflexivity.
    + exact (IH true l).
    + rewrite IH. destruct (dec2p pend p) as [pd q]. cbn. rewrite app_assoc. reflexivity.
Qed.

(** ** The tick through hidden ones *)

Definition tickS (pre post : list bool) : option (list bool * list bool) :=
  match scanr Q4 pre with
  | Fin Q0 p0 =>
    match scanr Q0 post with
    | Stop p2 rest =>
      let (pd, q) := dec2p false p2 in
      match dec2 pd (p0 ++ [TM80.W10]) with
      | (oL, false) => Some (oL, q ++ true :: rest)
      | _ => None
      end
    | Fin s p2 =>
      if safe_end s then
        let (pd, q) := dec2p false p2 in
        match dec2 pd (p0 ++ [TM80.W10]) with
        | (oL, false) => Some (oL, q ++ [true])
        | _ => None
        end
      else None
    end
  | _ => None
  end.

Theorem tickS_sound : forall pre post oa ob, tickS pre post = Some (oa, ob) ->
  forall t, dpass Q4 [TM80.W10] (pre ++ repeat true (3 * t) ++ post) =
            PNil (oa ++ repeat false (3 * t) ++ ob).
Proof.
  intros pre post oa ob H t. unfold tickS in H.
  destruct (scanr Q4 pre) as [s p0 |] eqn:E0; [| discriminate].
  destruct s; try discriminate.
  unfold dpass. rewrite scanr_app, E0. cbv beta iota.
  rewrite scanr_app, scanr_ones3. cbv beta iota.
  destruct (scanr Q0 post) as [s p2 | p2 rest] eqn:E2.
  - destruct (safe_end s); [| discriminate].
    destruct (dec2p false p2) as [pd q] eqn:Ep.
    destruct (dec2 pd (p0 ++ [TM80.W10])) as [oL []] eqn:Ed; [discriminate |].
    injection H as <- <-. unfold finish, dec. rewrite <- !app_assoc.
    rewrite dec2p_spec, Ep. cbn [fst snd]. rewrite dec2_W1s, Ed. cbn [fst snd].
    rewrite <- !app_assoc. reflexivity.
  - destruct (dec2p false p2) as [pd q] eqn:Ep.
    destruct (dec2 pd (p0 ++ [TM80.W10])) as [oL []] eqn:Ed; [discriminate |].
    injection H as <- <-. unfold finish, dec. rewrite <- !app_assoc.
    rewrite dec2p_spec, Ep. cbn [fst snd]. rewrite dec2_W1s, Ed. cbn [fst snd].
    rewrite <- !app_assoc. reflexivity.
Qed.

Definition haltS (pre post : list bool) : bool :=
  match scanr Q4 pre with
  | Fin Q0 _ => match scanr Q0 post with Fin s _ => negb (safe_end s) | Stop _ _ => false end
  | _ => false
  end.

Theorem haltS_sound : forall pre post, haltS pre post = true ->
  forall t, dpass Q4 [TM80.W10] (pre ++ repeat true (3 * t) ++ post) = PHalt.
Proof.
  intros pre post H t. unfold haltS in H.
  destruct (scanr Q4 pre) as [s p0 |] eqn:E0; [| discriminate].
  destruct s; try discriminate.
  unfold dpass. rewrite scanr_app, E0. cbv beta iota.
  rewrite scanr_app, scanr_ones3. cbv beta iota.
  destruct (scanr Q0 post) as [s p2 | p2 rest] eqn:E2; [| discriminate].
  destruct (safe_end s); [discriminate | reflexivity].
Qed.

(** ** A tick that stops before the hidden cells *)

Lemma dpass_stop_app : forall pre p rest d Y,
  scanr Q4 pre = Stop p rest -> dpass Q4 [TM80.W10] pre = PNil d ->
  dpass Q4 [TM80.W10] (pre ++ Y) = PNil (d ++ Y).
Proof.
  intros pre p rest d Y Hs Hd. unfold dpass in *. rewrite scanr_app, Hs. rewrite Hs in Hd.
  unfold finish in *. destruct (dec (p ++ [TM80.W10])) as [o []]; [discriminate |].
  injection Hd as <-. rewrite <- app_assoc. reflexivity.
Qed.

(** ** The fill across the hidden cells *)

Fixpoint par (o : bool) (a : list bool) : bool :=
  match a with [] => o | _ :: a' => par (negb o) a' end.

Lemma par_len : forall a a' o, length a = length a' -> par o a = par o a'.
Proof.
  induction a as [| x a IH]; intros [| y a'] o H; try discriminate; [reflexivity |].
  cbn [par]. apply IH. cbn in H. lia.
Qed.

Lemma encb_app : forall a o l, encb o (a ++ l) = encb o a ++ encb (par o a) l.
Proof.
  induction a as [| x a IH]; intros o l; [reflexivity |].
  cbn [app encb par]. rewrite IH, app_assoc. reflexivity.
Qed.

Lemma encb_rep2 : forall t o x l, encb o (repeat x (2 * t) ++ l) = repeat x (3 * t) ++ encb o l.
Proof.
  induction t as [| t IH]; intros o x l; [reflexivity |].
  replace (2 * S t) with (S (S (2 * t))) by lia.
  replace (3 * S t) with (S (S (S (3 * t)))) by lia.
  destruct o; cbn [repeat app encb negb]; rewrite IH; reflexivity.
Qed.

Lemma par_rep2 : forall t o x l, par o (repeat x (2 * t) ++ l) = par o l.
Proof.
  induction t as [| t IH]; intros o x l; [reflexivity |].
  replace (2 * S t) with (S (S (2 * t))) by lia.
  cbn [repeat app par]. rewrite Bool.negb_involutive. apply IH.
Qed.

Lemma fillS_sound : forall blo bhi rs x t,
  Reach (c1101 ++ encb false blo ++ repeat x (3 * t) ++ encb (par false blo) bhi ++ rs)
        (c1101 ++ encb false (repeat true (length blo)) ++ repeat true (3 * t) ++
         encb (par false blo) (repeat true (length bhi)) ++ rs).
Proof.
  intros blo bhi rs x t.
  pose proof (reach_fill (blo ++ repeat x (2 * t) ++ bhi) rs) as H.
  assert (E1 : encb false (blo ++ repeat x (2 * t) ++ bhi) =
               encb false blo ++ repeat x (3 * t) ++ encb (par false blo) bhi)
    by (rewrite encb_app, encb_rep2; reflexivity).
  assert (E2 : repeat true (length (blo ++ repeat x (2 * t) ++ bhi)) =
               repeat true (length blo) ++ repeat true (2 * t) ++ repeat true (length bhi))
    by (rewrite !length_app, repeat_length, !repeat_app; reflexivity).
  rewrite E1, E2 in H. rewrite encb_app, encb_rep2 in H.
  rewrite (par_len (repeat true (length blo)) blo false (repeat_length _ _)) in H.
  rewrite <- !app_assoc in H. exact H.
Qed.

(** ** The symbolic evaluator *)

Definition sst : Type := (list bool * bool * list bool)%type.

Definition conc (t : nat) (st : sst) : list bool :=
  let '(pre, x, post) := st in pre ++ repeat x (3 * t) ++ post.

Definition all1 (b : list bool) : bool := forallb (fun y => y) b.

Definition fillS (pre : list bool) (x : bool) (post : list bool) : option sst :=
  match pre with
  | true :: true :: false :: true :: cs =>
    let (blo, r0) := parse false cs in
    match r0 with
    | [] =>
      let (bhi, rs) := parse (par false blo) post in
      if all1 blo && x && all1 bhi then None
      else Some (c1101 ++ encb false (repeat true (length blo)), true,
                 encb (par false blo) (repeat true (length bhi)) ++ rs)
    | _ => None
    end
  | _ => None
  end.

(** Move the last cell of [pre] behind the hidden cells when it equals them. *)
Definition normS (pre : list bool) (x : bool) (post : list bool) : option sst :=
  match pre with
  | [true; true; false; true] => None
  | _ => match rev pre with
         | y :: r' => if Bool.eqb y x then Some (rev r', x, x :: post) else None
         | [] => None
         end
  end.

Definition sstep (st : sst) : option sst :=
  let '(pre, x, post) := st in
  match pre with
  | true :: false :: pre' => Some (pre', x, post)
  | _ =>
    match normS pre x post with
    | Some st' => Some st'
    | None =>
      match fillS pre x post with
      | Some st' => Some st'
      | None =>
        match scanr Q4 pre, dpass Q4 [TM80.W10] pre with
        | Stop _ _, PNil d => Some (d, x, post)
        | _, _ =>
          if x then match tickS pre post with Some (oa, ob) => Some (oa, false, ob) | None => None end
          else None
        end
      end
    end
  end.

Lemma fillS_reach : forall pre x post st', fillS pre x post = Some st' ->
  forall t, Reach (conc t (pre, x, post)) (conc t st').
Proof.
  intros pre x post st' H t. unfold fillS in H.
  destruct pre as [| [] pre]; try discriminate.
  destruct pre as [| [] pre]; try discriminate.
  destruct pre as [| [] pre]; try discriminate.
  destruct pre as [| [] cs]; try discriminate.
  destruct (parse false cs) as [blo r0] eqn:E1.
  destruct r0; [| discriminate].
  destruct (parse (par false blo) post) as [bhi rs] eqn:E2.
  destruct (all1 blo && x && all1 bhi); [discriminate |].
  injection H as <-.
  pose proof (parse_spec (length cs) cs (le_n _) false blo [] E1) as Hc. rewrite app_nil_r in Hc.
  pose proof (parse_spec (length post) post (le_n _) _ bhi rs E2) as Hp.
  unfold conc. rewrite Hc, Hp.
  pose proof (fillS_sound blo bhi rs x t) as HR. unfold c1101 in *.
  cbn [app] in *. rewrite <- ?app_assoc. exact HR.
Qed.

Lemma normS_eq : forall pre x post st', normS pre x post = Some st' ->
  forall t, conc t (pre, x, post) = conc t st'.
Proof.
  intros pre x post st' H t. unfold normS in H.
  assert (H' : match rev pre with
               | y :: r' => if Bool.eqb y x then Some (rev r', x, x :: post) else None
               | [] => None end = Some st').
  { destruct pre as [| [] [| [] [| [] [| [] [| ? ?]]]]]; try exact H; discriminate. }
  clear H. destruct (rev pre) as [| y r'] eqn:Er; [discriminate |].
  destruct (Bool.eqb y x) eqn:Ey; [| discriminate]. apply Bool.eqb_prop in Ey. subst y.
  injection H' as <-.
  assert (Hp : pre = rev r' ++ [x]).
  { rewrite <- (rev_involutive pre), Er. reflexivity. }
  unfold conc. rewrite Hp, <- app_assoc. cbn [app].
  change (x :: repeat x (3 * t) ++ post) with ((x :: repeat x (3 * t)) ++ post).
  rewrite <- (repeat_snoc1 x (3 * t)), <- app_assoc. reflexivity.
Qed.

Lemma sstep_sound : forall st st', sstep st = Some st' ->
  forall t, Reach (conc t st) (conc t st').
Proof.
  intros [[pre x] post] st' H t. unfold sstep in H.
  assert (Hmain : match normS pre x post with
    | Some st1 => Some st1
    | None => match fillS pre x post with
      | Some st1 => Some st1
      | None => match scanr Q4 pre, dpass Q4 [TM80.W10] pre with
        | Stop _ _, PNil d => Some (d, x, post)
        | _, _ => if x then match tickS pre post with Some (oa, ob) => Some (oa, false, ob) | None => None end
                  else None
        end end end = Some st' -> Reach (conc t (pre, x, post)) (conc t st')).
  { clear H. intro H.
    destruct (normS pre x post) as [st1 |] eqn:En.
    { injection H as <-. rewrite (normS_eq _ _ _ _ En t). apply reach_refl. }
    destruct (fillS pre x post) as [st1 |] eqn:Ef.
    { injection H as <-. exact (fillS_reach _ _ _ _ Ef t). }
    assert (Htick : (if x then match tickS pre post with Some (oa, ob) => Some (oa, false, ob) | None => None end
                     else None) = Some st' -> Reach (conc t (pre, x, post)) (conc t st')).
    { intro H1. destruct x; [| discriminate].
      destruct (tickS pre post) as [[oa ob] |] eqn:Et; [| discriminate]. injection H1 as <-.
      unfold conc. apply reach_tick. exact (tickS_sound pre post oa ob Et t). }
    destruct (scanr Q4 pre) as [s p | p rest] eqn:Es; [exact (Htick H) |].
    destruct (dpass Q4 [TM80.W10] pre) as [| d | T] eqn:Ed; try exact (Htick H).
    injection H as <-. unfold conc. rewrite app_assoc. apply reach_tick.
    rewrite <- app_assoc. exact (dpass_stop_app pre p rest d _ Es Ed). }
  destruct pre as [| [] pre1]; try exact (Hmain H).
  destruct pre1 as [| [] pre2]; try exact (Hmain H).
  injection H as <-. unfold conc. cbn [app]. apply reach_strip.
Qed.

Fixpoint srun (fuel : nat) (st : sst) : option sst :=
  match fuel with
  | O => None
  | S f =>
    let '(pre, x, post) := st in
    if x && haltS pre post then Some st
    else match sstep st with Some st' => srun f st' | None => None end
  end.

Lemma srun_sound : forall fuel st st', srun fuel st = Some st' ->
  forall t, Reach (conc t st) (conc t st') /\ dpass Q4 [TM80.W10] (conc t st') = PHalt.
Proof.
  induction fuel as [| f IH]; intros [[pre x] post] st' H t; [discriminate |].
  cbn [srun] in H.
  destruct (x && haltS pre post) eqn:Eh.
  - injection H as <-. apply andb_prop in Eh. destruct Eh as [-> Eh].
    split; [apply reach_refl | exact (haltS_sound pre post Eh t)].
  - destruct (sstep (pre, x, post)) as [st1 |] eqn:E1; [| discriminate].
    destruct (IH st1 st' H t) as [HR HH]. split; [| exact HH].
    exact (reach_trans _ _ _ (sstep_sound _ _ E1 t) HR).
Qed.

(** ** The halting end phase for every half-width *)

Theorem prefix28_halts_all : forall hr k, exists n ds,
  tickN 3 n (rep10 k ++ start28 hr) = Some ds /\ dpass Q4 [TM80.W10] ds = PHalt.
Proof.
  intros hr k.
  assert (H : exists st', srun 200 (c1101, true, rep10 3 ++ c1101 ++ encb false bits28 ++ [true]) = Some st')
    by (vm_compute; eexists; reflexivity).
  destruct H as [st' H].
  destruct (srun_sound 200 _ st' H hr) as [HR HH].
  destruct (HR k) as [n [k' E]]. exists n, (rep10 k' ++ conc hr st').
  split; [exact E | exact (dpass_shift_halt k' _ HH)].
Qed.

End Sym694.

Module Lev694.

(** * 1RB1LB_1RC0RD_0LA1RE_0RF1LC_1LA0RB_---1LC: the tick that ends a level

    A tick whose decode runs into the left end of the tape (result [PRoot]) is followed by a
    second pass from the left end.  That pass crosses the prefix (10)^k: after two pairs the
    scan is in state Q4 and from there it is the ordinary pass.  The outcome is

        (10)^(j+1) X   ->   001 (10)^j e

    where 10 d is what the first pass leaves of X and e is the ordinary pass on d.
    This is the shape S(M, a, w) = 001 (10)^M 111 0^a w of a level start. *)

Import Individual62.
Import T694_levels End694.
Import Lia PeanoNat.
Import Coq.Lists.List.
Import ListNotations.

Definition rootstk : list TM80.Word :=
  [TM80.W10; TM80.W1; TM80.W10; TM80.W1; TM80.W1; TM80.W1].

Lemma finish_root_nil : forall p j tail e,
  finish (p ++ [TM80.W10]) tail = PNil e ->
  finish ((p ++ blocks j) ++ rootstk) tail = PNil ([false; false; true] ++ rep10 j ++ e).
Proof.
  intros p j tail e. unfold finish, dec, rootstk. rewrite <- app_assoc.
  destruct (dec2_app p false) as [pd [q Hq]]. rewrite !Hq. rewrite dec2_blocks.
  destruct pd; cbn [dec2 fst snd app]; intro H; [discriminate |].
  injection H as <-.
  rewrite <- !app_assoc. cbn [app].
  rewrite (app_comm_cons (rep01 j) (q ++ tail) true), true_rep01, <- app_assoc. reflexivity.
Qed.

(** The second pass, from the left end, through a prefix of at least two pairs. *)
Theorem dpass_root_prefix : forall j d e,
  dpass Q4 [TM80.W10] d = PNil e ->
  dpass Q0 [] (rep10 (S (S j)) ++ d) = PNil ([false; false; true] ++ rep10 j ++ e).
Proof.
  intros j d e. unfold dpass.
  rewrite rep10_SS, <- app_assoc, scanr_app, scan_Q0_1010, scanr_rep10_app.
  fold rootstk.
  destruct (scanr Q4 d) as [s' p | p rest]; rewrite !app_nil_r.
  - destruct (safe_end s'); [apply finish_root_nil | discriminate].
  - apply finish_root_nil.
Qed.

(** The tick that ends a level. *)
Theorem level_end_tick : forall fuel j X d e,
  dpass Q4 [TM80.W10] X = PRoot (true :: false :: d) ->
  dpass Q4 [TM80.W10] d = PNil e ->
  tickF (S fuel) (rep10 (S j) ++ X) = Some ([false; false; true] ++ rep10 j ++ e).
Proof.
  intros fuel j X d e HX Hd. unfold tickF.
  rewrite (dpass_shift_root (S j) X d HX). cbn [rootloop].
  change (true :: false :: rep10 (S j) ++ d) with (rep10 (S (S j)) ++ d).
  rewrite (dpass_root_prefix j d e Hd). reflexivity.
Qed.

(** In the shape of a level start. *)
Corollary level_end_Slev : forall fuel j X d i a w,
  dpass Q4 [TM80.W10] X = PRoot (true :: false :: d) ->
  dpass Q4 [TM80.W10] d = PNil (rep10 i ++ [true; true; true] ++ repeat false a ++ w) ->
  tickF (S fuel) (rep10 (S j) ++ X) = Some (Slev (j + i) a w).
Proof.
  intros fuel j X d i a w HX Hd. rewrite (level_end_tick fuel j X d _ HX Hd).
  unfold Slev, rep10. rewrite repeat_app, concat_app, <- !app_assoc. reflexivity.
Qed.

End Lev694.

Module Lvl1_694.

(** * 1RB1LB_1RC0RD_0LA1RE_0RF1LC_1LA0RB_---1LC: level 1 from start to end

    The end phase with the length of the prefix (10)^k tracked exactly, and the first level
    of the machine as one statement: from the start configuration to the start of level 2. *)

Import Individual62.
Import T694_levels End694 Lev694.
Import Lia PeanoNat NArith.
Import Coq.Lists.List.
Import ListNotations.

(** [ReachD dk X Y]: from (10)^k X to (10)^(k + dk) Y, for every k. *)
Definition ReachD (dk : nat) (X Y : list bool) : Prop :=
  forall k, exists n, tickN 3 n (rep10 k ++ X) = Some (rep10 (k + dk) ++ Y).

Lemma reachd_refl : forall X, ReachD O X X.
Proof. intros X k. exists O. rewrite Nat.add_0_r. reflexivity. Qed.

Lemma reachd_trans : forall a b X Y Z, ReachD a X Y -> ReachD b Y Z -> ReachD (a + b) X Z.
Proof.
  intros a b X Y Z H1 H2 k. destruct (H1 k) as [n1 E1]. destruct (H2 (k + a)) as [n2 E2].
  exists (n1 + n2). rewrite tickN_add, E1, E2, Nat.add_assoc. reflexivity.
Qed.

Lemma reachd_tick : forall X Y, dpass Q4 [TM80.W10] X = PNil Y -> ReachD O X Y.
Proof.
  intros X Y H k. exists (S O). cbn [tickN]. rewrite (tickF_shift_nil 3 k X Y H), Nat.add_0_r.
  reflexivity.
Qed.

Lemma reachd_strip : forall X, ReachD (S O) (true :: false :: X) X.
Proof.
  intros X k. exists O. cbn [tickN]. rewrite Nat.add_1_r, rep10_S, <- app_assoc. reflexivity.
Qed.

Lemma reachd_fill : forall b R,
  ReachD (2 ^ length b - 1 - bval b)
    (c1101 ++ encb false b ++ R) (c1101 ++ encb false (repeat true (length b)) ++ R).
Proof. intros b R k. eexists. apply counter_fill. Qed.

(** What one evaluator step adds to the prefix. *)
Definition dkof (X : list bool) : nat :=
  match X with
  | true :: false :: _ => S O
  | true :: true :: false :: true :: cs =>
    let (b, rs) := parse false cs in
    if forallb (fun x => x) b then O else 2 ^ length b - 1 - bval b
  | _ => O
  end.

Lemma tick1_soundD : forall X Y, tick1 X = Some Y -> ReachD O X Y.
Proof.
  intros X Y H. unfold tick1 in H.
  destruct (dpass Q4 [TM80.W10] X) as [| Y' |] eqn:E; try discriminate.
  injection H as <-. exact (reachd_tick X Y' E).
Qed.

Lemma estep_soundD : forall X Y, estep X = Some Y -> ReachD (dkof X) X Y.
Proof.
  intros X Y H. unfold estep in H. unfold dkof.
  destruct X as [| [] X1]; try exact (tick1_soundD _ _ H).
  destruct X1 as [| [] X2]; try exact (tick1_soundD _ _ H).
  - destruct X2 as [| [] X3]; try exact (tick1_soundD _ _ H).
    destruct X3 as [| [] cs]; try exact (tick1_soundD _ _ H).
    destruct (parse false cs) as [b rs] eqn:E.
    destruct (forallb (fun x => x) b); [exact (tick1_soundD _ _ H) |].
    injection H as <-.
    rewrite (parse_spec (length cs) cs (le_n _) false b rs E).
    exact (reachd_fill b rs).
  - injection H as <-. apply reachd_strip.
Qed.

(** The same count in binary, so that it can be computed. *)
Fixpoint bvalN (b : list bool) : N :=
  match b with [] => 0%N | x :: b' => ((if x then 1 else 0) + 2 * bvalN b')%N end.

Lemma bvalN_spec : forall b, N.to_nat (bvalN b) = bval b.
Proof.
  induction b as [| x b IH]; [reflexivity |].
  cbn [bvalN bval]. rewrite N2Nat.inj_add, N2Nat.inj_mul, IH. destruct x; reflexivity.
Qed.

Definition dkofN (X : list bool) : N :=
  match X with
  | true :: false :: _ => 1%N
  | true :: true :: false :: true :: cs =>
    let (b, rs) := parse false cs in
    if forallb (fun x => x) b then 0%N else (2 ^ N.of_nat (length b) - 1 - bvalN b)%N
  | _ => 0%N
  end.

Lemma dkofN_spec : forall X, N.to_nat (dkofN X) = dkof X.
Proof.
  intros X. unfold dkofN, dkof.
  destruct X as [| [] X1]; try reflexivity.
  destruct X1 as [| [] X2]; try reflexivity.
  destruct X2 as [| [] X3]; try reflexivity.
  destruct X3 as [| [] cs]; try reflexivity.
  destruct (parse false cs) as [b rs].
  destruct (forallb (fun x => x) b); [reflexivity |].
  rewrite !N2Nat.inj_sub, bvalN_spec, N2Nat.inj_pow, Nat2N.id. reflexivity.
Qed.

(** Run until a tick reaches the left end of the tape. *)
Fixpoint drun (fuel : nat) (acc : N) (X : list bool) : option (N * list bool) :=
  match fuel with
  | O => None
  | S f =>
    match dpass Q4 [TM80.W10] X with
    | PRoot _ => Some (acc, X)
    | PHalt => None
    | PNil _ => match estep X with Some Y => drun f (acc + dkofN X)%N Y | None => None end
    end
  end.

Lemma drun_sound : forall fuel acc X dk Y, drun fuel acc X = Some (dk, Y) ->
  exists d, N.to_nat dk = N.to_nat acc + d /\ ReachD d X Y.
Proof.
  induction fuel as [| f IH]; intros acc X dk Y H; [discriminate |].
  cbn [drun] in H.
  destruct (dpass Q4 [TM80.W10] X) as [| d0 | T] eqn:E; [discriminate | |].
  - destruct (estep X) as [X1 |] eqn:E1; [| discriminate].
    destruct (IH _ _ _ _ H) as [d [Hd HR]].
    exists (dkof X + d). split; [rewrite Hd, N2Nat.inj_add, dkofN_spec; lia |].
    exact (reachd_trans _ _ _ _ _ (estep_soundD _ _ E1) HR).
  - injection H as <- <-. exists O. split; [lia | apply reachd_refl].
Qed.

Definition X1 : list bool :=
  [true; true; false; true] ++ encb false (repeat true 12) ++ rep10 3 ++
  [true; true; false; true] ++ encb false [false; true; false; false] ++ [true].

(** ** Level 1 *)

(** What the end phase of level 1 adds to the prefix: 3114 * 4^6. *)
Definition dk1 : N := 12754944%N.

Definition Y1 : list bool := [true; true; false; true] ++ repeat true 37.
Definition d1 : list bool := [true; false; false; true] ++ repeat false 37 ++ [true].

Lemma run1 : drun 200 0%N X1 = Some (dk1, Y1).
Proof. vm_compute. reflexivity. Qed.

Lemma end1 : ReachD (N.to_nat dk1) X1 Y1.
Proof.
  destruct (drun_sound _ _ _ _ _ run1) as [d [Hd HR]].
  change (N.to_nat 0%N) with O in Hd. cbn [Nat.add] in Hd. rewrite Hd. exact HR.
Qed.

Lemma Y1_root : dpass Q4 [TM80.W10] Y1 = PRoot (true :: false :: d1).
Proof. vm_compute. reflexivity. Qed.

Lemma d1_pass : dpass Q4 [TM80.W10] d1 =
  PNil (rep10 (S O) ++ [true; true; true] ++ repeat false 37 ++ [true]).
Proof. vm_compute. reflexivity. Qed.

Lemma bits_T2 : forall b, length b = 4 -> bval b = 2 -> b = [false; true; false; false].
Proof.
  intros b Hl Hv.
  destruct b as [| b0 [| b1 [| b2 [| b3 [| b4 b]]]]]; try discriminate Hl.
  destruct b0, b1, b2, b3; cbn in Hv; try discriminate Hv; reflexivity.
Qed.

Lemma kcyc_2730 : kcyc 2 2 10 = 2730.
Proof. vm_compute. reflexivity. Qed.

(** The first level: from the digit form of the start to the start of level 2,
    S(12757674, 37, 1), where 12757674 = (2 * 4^6 - 2) / 3 + 3114 * 4^6. *)
Theorem level1 : exists n, tickN 3 n D0 = Some (Slev (N.to_nat 12757674%N) 37 [true]).
Proof.
  destruct (level_bulk_exact 3 3 2 2 [true]) as [cnt [b [Hb [Hv [Hl _]]]]]; [cbn; lia |].
  rewrite (bits_T2 b Hl Hv), kcyc_2730 in Hb.
  destruct (end1 2730) as [n Hn].
  exists (27 + (cnt + (n + S O))).
  rewrite tickN_add, D0_to_S12_7, S12_7_Slev.
  rewrite tickN_add. change (Slev 12 7 [true]) with (Slev (3 + 3 * 2 + 3) (3 * 2 + 1) [true]).
  rewrite Hb.
  change (Ptape 2730 (4 + 4 * 2) 3 [false; true; false; false] [true]) with (rep10 2730 ++ X1).
  rewrite tickN_add, Hn. cbn [tickN].
  replace (2730 + N.to_nat dk1) with (S (2729 + N.to_nat dk1)) by lia.
  rewrite (level_end_Slev 2 (2729 + N.to_nat dk1) Y1 d1 (S O) 37 [true] Y1_root d1_pass).
  replace (2729 + N.to_nat dk1 + 1) with (N.to_nat 12757674%N) by (unfold dk1; lia).
  reflexivity.
Qed.

End Lvl1_694.

Module Eng694.

(** * 1RB1LB_1RC0RD_0LA1RE_0RF1LC_1LA0RB_---1LC: the generic engine for one level

    Proved once, used by every level:

    - the end-phase evaluator on states [pre ++ repeat x (3 * t) ++ post ++ R], sound for every
      hidden width [t] and every untouched rest [R], with the growth of the prefix (10)^k
      as an exact value [A * 4^t + B]  ([gstep_sound], [grun_sound]);
    - the end of a level from the final state of a run ([endphase]);
    - a level as one statement: bulk, end phase, level-end tick ([level_step]);
    - division by a constant as a bit transducer, most significant bit first, with its value
      law, its behaviour on a concatenation and on a repeated block ([dm_spec], [dm_app_eq],
      [dm_rp]);
    - the next counter word as the quotient of a division by 3 ([stageB]). *)

Import Individual62.
Import T694_levels End694 Sym694 Lev694 Lvl1_694.
Import Lia Arith PeanoNat Bool NArith ZArith.
Import Coq.Lists.List.
Import ListNotations.

(** ** Bit values (least significant bit first) *)

Lemma bval_app : forall a b, bval (a ++ b) = bval a + 2 ^ length a * bval b.
Proof.
  induction a as [| x a IH]; intro b.
  - cbn [app bval length]. rewrite Nat.pow_0_r. lia.
  - cbn [app bval length]. rewrite IH, Nat.pow_succ_r'. destruct x; cbv iota; ring.
Qed.

Lemma bval_ones : forall n, S (bval (repeat true n)) = 2 ^ n.
Proof.
  induction n as [| n IH]; [reflexivity |].
  cbn [repeat bval]. rewrite Nat.pow_succ_r'. lia.
Qed.

Lemma bval_neg : forall b, bval (map negb b) + bval b + 1 = 2 ^ length b.
Proof.
  induction b as [| x b IH]; [reflexivity |].
  cbn [map bval length]. rewrite Nat.pow_succ_r'. destruct x; cbn [negb]; cbv iota; lia.
Qed.

Lemma bval_inj : forall a b, length a = length b -> bval a = bval b -> a = b.
Proof.
  induction a as [| x a IH]; intros [| y b] Hl Hv; try discriminate; [reflexivity |].
  cbn [bval] in Hv. cbn [length] in Hl.
  assert (Hxy : x = y) by (destruct x, y; cbv iota in Hv; try reflexivity; lia).
  subst y. f_equal. apply IH; [lia |]. destruct x; cbv iota in Hv; lia.
Qed.

Lemma bvalZ : forall b, Z.of_nat (bval b) = Z.of_N (bvalN b).
Proof. intro b. rewrite <- bvalN_spec, N_nat_Z. reflexivity. Qed.

Definition pw4 (t : nat) : Z := (4 ^ Z.of_nat t)%Z.

Lemma pw4_pos : forall t, (1 <= pw4 t)%Z.
Proof.
  intro t. unfold pw4.
  assert (0 < 4 ^ Z.of_nat t)%Z by (apply Z.pow_pos_nonneg; lia). lia.
Qed.

Lemma pw2_2t : forall t, (2 ^ Z.of_nat (2 * t))%Z = pw4 t.
Proof.
  intro t. unfold pw4. rewrite Nat2Z.inj_mul. change (Z.of_nat 2) with 2%Z.
  rewrite Z.pow_mul_r by lia. reflexivity.
Qed.

Lemma pow2Z : forall n, Z.of_nat (2 ^ n) = (2 ^ Z.of_nat n)%Z.
Proof. intro n. rewrite Nat2Z.inj_pow. reflexivity. Qed.

Lemma pw4_add : forall a b, pw4 (a + b) = (pw4 a * pw4 b)%Z.
Proof. intros a b. unfold pw4. rewrite Nat2Z.inj_add, Z.pow_add_r by lia. reflexivity. Qed.

Lemma pw4_16 : forall T, pw4 (2 + 2 * T) = (16 * Z.of_nat (16 ^ T))%Z.
Proof.
  intro T. rewrite pw4_add. change (pw4 2) with 16%Z. unfold pw4.
  rewrite Nat2Z.inj_mul, Nat2Z.inj_pow. change (Z.of_nat 2) with 2%Z. change (Z.of_nat 16) with 16%Z.
  rewrite Z.pow_mul_r by lia. reflexivity.
Qed.

(** What a fill adds to the prefix, for a counter in three parts. *)
Lemma fill_delta_gen : forall blo mid bhi,
  Z.of_nat (2 ^ length (blo ++ mid ++ bhi) - 1 - bval (blo ++ mid ++ bhi)) =
  (2 ^ Z.of_nat (length blo) *
     (2 ^ Z.of_nat (length mid) * (2 ^ Z.of_nat (length bhi) - Z.of_nat (bval bhi)) - Z.of_nat (bval mid))
   - 1 - Z.of_nat (bval blo))%Z.
Proof.
  intros blo mid bhi. pose proof (bval_lt (blo ++ mid ++ bhi)) as Hlt.
  rewrite Nat2Z.inj_sub by lia. rewrite Nat2Z.inj_sub by lia.
  rewrite !length_app, !bval_app, !Nat.pow_add_r.
  repeat first [rewrite Nat2Z.inj_add | rewrite Nat2Z.inj_mul | rewrite pow2Z].
  change (Z.of_nat 1) with 1%Z. ring.
Qed.

Definition fillA (x : bool) (blo bhi : list bool) : Z :=
  (2 ^ Z.of_nat (length blo) * (2 ^ Z.of_nat (length bhi) - Z.of_N (bvalN bhi) - (if x then 1 else 0)))%Z.

Definition fillB (x : bool) (blo : list bool) : Z :=
  ((if x then 2 ^ Z.of_nat (length blo) else 0) - 1 - Z.of_N (bvalN blo))%Z.

Lemma fill_delta : forall x blo bhi t,
  Z.of_nat (2 ^ length (blo ++ repeat x (2 * t) ++ bhi) - 1 - bval (blo ++ repeat x (2 * t) ++ bhi)) =
  (fillA x blo bhi * pw4 t + fillB x blo)%Z.
Proof.
  intros x blo bhi t. rewrite fill_delta_gen, repeat_length, pw2_2t, (bvalZ blo), (bvalZ bhi).
  unfold fillA, fillB. destruct x; cbv iota.
  - pose proof (bval_ones (2 * t)) as Ho.
    assert (Hz : Z.of_nat (bval (repeat true (2 * t))) = (pw4 t - 1)%Z).
    { rewrite <- pw2_2t, <- pow2Z. lia. }
    rewrite Hz. ring.
  - rewrite bval_repeat_false. change (Z.of_nat O) with 0%Z. ring.
Qed.

(** ** Reaching, with the exact growth of the prefix *)

Definition ReachA (A B : Z) (X Y : nat -> list bool) : Prop :=
  forall t k, exists n k', tickN 3 n (rep10 k ++ X t) = Some (rep10 k' ++ Y t) /\
    Z.of_nat k' = (Z.of_nat k + A * pw4 t + B)%Z.

Lemma reachA_refl : forall X, ReachA 0 0 X X.
Proof. intros X t k. exists O, k. split; [reflexivity | lia]. Qed.

Lemma reachA_trans : forall A1 B1 A2 B2 X Y Z0,
  ReachA A1 B1 X Y -> ReachA A2 B2 Y Z0 -> ReachA (A1 + A2) (B1 + B2) X Z0.
Proof.
  intros A1 B1 A2 B2 X Y Z0 H1 H2 t k.
  destruct (H1 t k) as [n1 [k1 [E1 D1]]]. destruct (H2 t k1) as [n2 [k2 [E2 D2]]].
  exists (n1 + n2), k2. split; [rewrite tickN_add, E1; exact E2 | lia].
Qed.

Lemma strip_reach : forall X : nat -> list bool, ReachA 0 1 (fun t => true :: false :: X t) X.
Proof.
  intros X t k. exists O, (S k). split; [| lia].
  cbn [tickN]. rewrite rep10_S, <- app_assoc. reflexivity.
Qed.

Lemma tick_reach : forall X Y : nat -> list bool,
  (forall t, dpass Q4 [TM80.W10] (X t) = PNil (Y t)) -> ReachA 0 0 X Y.
Proof.
  intros X Y H t k. exists (S O), k. split; [| lia].
  cbn [tickN]. rewrite (tickF_shift_nil 3 k _ _ (H t)). reflexivity.
Qed.

Lemma eq_reach : forall X Y : nat -> list bool, (forall t, X t = Y t) -> ReachA 0 0 X Y.
Proof. intros X Y H t k. exists O, k. split; [rewrite H; reflexivity | lia]. Qed.

(** ** The tick through hidden ones, with the rest of the tape and with the root case *)

Definition tickG (pre post : list bool) : option (bool * bool * list bool * list bool) :=
  match scanr Q4 pre with
  | Fin Q0 p0 =>
    match scanr Q0 post with
    | Stop p2 rest =>
      let (pd, q) := dec2p false p2 in
      let (oL, rt) := dec2 pd (p0 ++ [TM80.W10]) in
      Some (true, rt, oL, q ++ true :: rest)
    | Fin s p2 =>
      if safe_end s then
        let (pd, q) := dec2p false p2 in
        let (oL, rt) := dec2 pd (p0 ++ [TM80.W10]) in
        Some (false, rt, oL, q ++ [true])
      else None
    end
  | _ => None
  end.

Definition pres (rt : bool) (l : list bool) : PassRes :=
  if rt then PRoot (true :: false :: l) else PNil l.

Theorem tickG_sound : forall pre post fr rt oa ob, tickG pre post = Some (fr, rt, oa, ob) ->
  forall t R, (fr = false -> R = []) ->
  dpass Q4 [TM80.W10] (pre ++ repeat true (3 * t) ++ post ++ R) =
  pres rt (oa ++ repeat false (3 * t) ++ ob ++ R).
Proof.
  intros pre post fr rt oa ob H t R HR. unfold tickG in H.
  destruct (scanr Q4 pre) as [s p0 |] eqn:E0; [| discriminate].
  destruct s; try discriminate.
  unfold dpass. rewrite scanr_app, E0. cbv beta iota.
  rewrite scanr_app, scanr_ones3. cbv beta iota.
  rewrite scanr_app.
  destruct (scanr Q0 post) as [s p2 | p2 rest] eqn:E2; cbv beta iota.
  - destruct (safe_end s) eqn:Es; [| discriminate].
    destruct (dec2p false p2) as [pd q] eqn:Ep.
    destruct (dec2 pd (p0 ++ [TM80.W10])) as [oL rt'] eqn:Ed.
    injection H as Hfr Hrt Hoa Hob. subst fr rt oa ob.
    specialize (HR eq_refl). subst R.
    cbn [scanr]. rewrite Es.
    unfold finish, dec. rewrite <- ?app_assoc. cbn [app].
    rewrite dec2p_spec, Ep. cbn [fst snd]. rewrite dec2_W1s, Ed. cbn [fst snd].
    rewrite ?app_nil_r.
    destruct rt'; cbv beta iota; cbn [pres]; rewrite <- ?app_assoc; cbn [app]; reflexivity.
  - destruct (dec2p false p2) as [pd q] eqn:Ep.
    destruct (dec2 pd (p0 ++ [TM80.W10])) as [oL rt'] eqn:Ed.
    injection H as Hfr Hrt Hoa Hob. subst fr rt oa ob.
    unfold finish, dec. rewrite <- ?app_assoc. cbn [app].
    rewrite dec2p_spec, Ep. cbn [fst snd]. rewrite dec2_W1s, Ed. cbn [fst snd].
    destruct rt'; cbv beta iota; cbn [pres]; rewrite <- ?app_assoc; cbn [app]; reflexivity.
Qed.

(** ** The fill across the hidden cells, with its exact count *)

Lemma fillZ_sound : forall blo bhi rs x t k, exists n,
  tickN 3 n (rep10 k ++ c1101 ++ encb false blo ++ repeat x (3 * t) ++ encb (par false blo) bhi ++ rs) =
  Some (rep10 (k + (2 ^ length (blo ++ repeat x (2 * t) ++ bhi) - 1 - bval (blo ++ repeat x (2 * t) ++ bhi))) ++
        c1101 ++ encb false (repeat true (length blo)) ++ repeat true (3 * t) ++
        encb (par false blo) (repeat true (length bhi)) ++ rs).
Proof.
  intros blo bhi rs x t k.
  exists (2 * (2 ^ length (blo ++ repeat x (2 * t) ++ bhi) - 1 - bval (blo ++ repeat x (2 * t) ++ bhi))).
  pose proof (counter_fill 3 k (blo ++ repeat x (2 * t) ++ bhi) rs) as H.
  assert (E1 : encb false (blo ++ repeat x (2 * t) ++ bhi) =
               encb false blo ++ repeat x (3 * t) ++ encb (par false blo) bhi)
    by (rewrite encb_app, encb_rep2; reflexivity).
  assert (E2 : repeat true (length (blo ++ repeat x (2 * t) ++ bhi)) =
               repeat true (length blo) ++ repeat true (2 * t) ++ repeat true (length bhi))
    by (rewrite !length_app, repeat_length, !repeat_app; reflexivity).
  rewrite E1, E2 in H. rewrite encb_app, encb_rep2 in H.
  rewrite (par_len (repeat true (length blo)) blo false (repeat_length _ _)) in H.
  rewrite <- !app_assoc in H. exact H.
Qed.

Definition gfill (pre : list bool) (x : bool) (post : list bool) : option (sst * Z * Z) :=
  match pre with
  | true :: true :: false :: true :: cs =>
    let (blo, r0) := parse false cs in
    match r0 with
    | [] =>
      let (bhi, rs) := parse (par false blo) post in
      if all1 blo && x && all1 bhi then None
      else Some ((c1101 ++ encb false (repeat true (length blo)), true,
                  encb (par false blo) (repeat true (length bhi)) ++ rs),
                 fillA x blo bhi, fillB x blo)
    | _ => None
    end
  | _ => None
  end.

Lemma gfill_sound : forall pre x post st' A B, gfill pre x post = Some (st', A, B) ->
  forall R, ReachA A B (fun t => conc t (pre, x, post) ++ R) (fun t => conc t st' ++ R).
Proof.
  intros pre x post st' A B H R t k. unfold gfill in H.
  destruct pre as [| [] pre]; try discriminate.
  destruct pre as [| [] pre]; try discriminate.
  destruct pre as [| [] pre]; try discriminate.
  destruct pre as [| [] cs]; try discriminate.
  destruct (parse false cs) as [blo r0] eqn:E1.
  destruct r0; [| discriminate].
  destruct (parse (par false blo) post) as [bhi rs] eqn:E2.
  destruct (all1 blo && x && all1 bhi); [discriminate |].
  injection H as <- <- <-.
  pose proof (parse_spec (length cs) cs (le_n _) false blo [] E1) as Hc. rewrite app_nil_r in Hc.
  pose proof (parse_spec (length post) post (le_n _) _ bhi rs E2) as Hp.
  destruct (fillZ_sound blo bhi (rs ++ R) x t k) as [n Hn].
  exists n. eexists. split.
  - unfold conc. rewrite Hc, Hp. unfold c1101 in *.
    rewrite <- ?app_assoc. cbn [app]. rewrite <- ?app_assoc.
    rewrite <- ?app_assoc in Hn. cbn [app] in Hn. rewrite <- ?app_assoc in Hn. exact Hn.
  - rewrite Nat2Z.inj_add, fill_delta. lia.
Qed.

(** ** One step of the evaluator *)

Definition gstep (closed : bool) (st : sst) : option (sst * Z * Z) :=
  let '(pre, x, post) := st in
  match pre with
  | true :: false :: pre' => Some ((pre', x, post), 0%Z, 1%Z)
  | _ =>
    match normS pre x post with
    | Some st' => Some (st', 0%Z, 0%Z)
    | None =>
      match gfill pre x post with
      | Some r => Some r
      | None =>
        match scanr Q4 pre, dpass Q4 [TM80.W10] pre with
        | Stop _ _, PNil d => Some ((d, x, post), 0%Z, 0%Z)
        | _, _ =>
          if x then
            match tickG pre post with
            | Some (fr, false, oa, ob) =>
              if fr || closed then Some ((oa, false, ob), 0%Z, 0%Z) else None
            | _ => None
            end
          else None
        end
      end
    end
  end.

Lemma gstep_sound : forall closed st st' A B, gstep closed st = Some (st', A, B) ->
  forall R, (closed = true -> R = []) ->
  ReachA A B (fun t => conc t st ++ R) (fun t => conc t st' ++ R).
Proof.
  intros closed [[pre x] post] st' A B H R HR. unfold gstep in H.
  assert (Hmain : match normS pre x post with
    | Some st1 => Some (st1, 0%Z, 0%Z)
    | None => match gfill pre x post with
      | Some r => Some r
      | None => match scanr Q4 pre, dpass Q4 [TM80.W10] pre with
        | Stop _ _, PNil d => Some ((d, x, post), 0%Z, 0%Z)
        | _, _ => if x then
                    match tickG pre post with
                    | Some (fr, false, oa, ob) =>
                      if fr || closed then Some ((oa, false, ob), 0%Z, 0%Z) else None
                    | _ => None
                    end
                  else None
        end end end = Some (st', A, B) ->
      ReachA A B (fun t => conc t (pre, x, post) ++ R) (fun t => conc t st' ++ R)).
  { clear H. intro H.
    destruct (normS pre x post) as [st1 |] eqn:En.
    { injection H as <- <- <-. apply eq_reach. intro t. cbv beta.
      rewrite (normS_eq _ _ _ _ En t). reflexivity. }
    destruct (gfill pre x post) as [[[st1 a] b] |] eqn:Ef.
    { injection H as <- <- <-. exact (gfill_sound _ _ _ _ _ _ Ef R). }
    assert (Htick : (if x then
                    match tickG pre post with
                    | Some (fr, false, oa, ob) =>
                      if fr || closed then Some ((oa, false, ob), 0%Z, 0%Z) else None
                    | _ => None
                    end
                  else None) = Some (st', A, B) ->
                  ReachA A B (fun t => conc t (pre, x, post) ++ R) (fun t => conc t st' ++ R)).
    { intro H1. destruct x; [| discriminate].
      destruct (tickG pre post) as [[[[fr rt] oa] ob] |] eqn:Et; [| discriminate].
      destruct rt; [discriminate |].
      destruct (fr || closed) eqn:Efc; [| discriminate]. injection H1 as <- <- <-.
      apply tick_reach. intro t. cbv beta. unfold conc. rewrite <- !app_assoc.
      apply (tickG_sound pre post fr false oa ob Et t R).
      intro Hf. apply HR. rewrite Hf in Efc. exact Efc. }
    destruct (scanr Q4 pre) as [s p | p rest] eqn:Es; [exact (Htick H) |].
    destruct (dpass Q4 [TM80.W10] pre) as [| d | T] eqn:Ed; try exact (Htick H).
    injection H as <- <- <-. apply tick_reach. intro t. cbv beta. unfold conc.
    rewrite <- !app_assoc. exact (dpass_stop_app pre p rest d _ Es Ed). }
  destruct pre as [| [] pre1]; try exact (Hmain H).
  destruct pre1 as [| [] pre2]; try exact (Hmain H).
  injection H as <- <- <-. unfold conc. cbn [app].
  apply (strip_reach (fun t => (pre2 ++ repeat x (3 * t) ++ post) ++ R)).
Qed.

Fixpoint grun (closed : bool) (fuel : nat) (st : sst) (A B : Z) : sst * Z * Z :=
  match fuel with
  | O => (st, A, B)
  | S f =>
    match gstep closed st with
    | Some (st', a, b) => grun closed f st' (A + a)%Z (B + b)%Z
    | None => (st, A, B)
    end
  end.

Lemma grun_sound : forall closed fuel st A B st' A' B', grun closed fuel st A B = (st', A', B') ->
  forall R, (closed = true -> R = []) ->
  ReachA (A' - A) (B' - B) (fun t => conc t st ++ R) (fun t => conc t st' ++ R).
Proof.
  intros closed. induction fuel as [| f IH]; intros st A B st' A' B' H R HR.
  - cbn [grun] in H. injection H as <- <- <-.
    replace (A - A)%Z with 0%Z by lia. replace (B - B)%Z with 0%Z by lia. apply reachA_refl.
  - cbn [grun] in H. destruct (gstep closed st) as [[[st1 a] b] |] eqn:E.
    + pose proof (reachA_trans _ _ _ _ _ _ _ (gstep_sound _ _ _ _ _ E R HR) (IH _ _ _ _ _ _ H R HR)) as HT.
      replace (A' - A)%Z with (a + (A' - (A + a)))%Z by lia.
      replace (B' - B)%Z with (b + (B' - (B + b)))%Z by lia. exact HT.
    + injection H as <- <- <-.
      replace (A - A)%Z with 0%Z by lia. replace (B - B)%Z with 0%Z by lia. apply reachA_refl.
Qed.

(** ** The end of a level from the final state of a run *)

Theorem endphase : forall fuel st0 pre post A fr oa ob p rest z1 z2 w',
  grun true fuel st0 0 0 = ((pre, true, post), A, 0%Z) ->
  (0 <= A)%Z ->
  tickG pre post = Some (fr, true, oa, ob) ->
  scanr Q4 oa = Stop p rest ->
  dpass Q4 [TM80.W10] oa = PNil (rep10 (S O) ++ [true; true; true] ++ repeat false z1) ->
  ob = repeat false z2 ++ w' ->
  forall t k, (1 <= k)%nat -> exists n M',
    tickN 3 n (rep10 k ++ conc t st0) = Some (Slev M' (z1 + 3 * t + z2) w') /\
    Z.of_nat M' = (Z.of_nat k + A * pw4 t)%Z.
Proof.
  intros fuel st0 pre post A fr oa ob p rest z1 z2 w' Hrun HA Ht Hs Hd Hob t k Hk.
  pose proof (grun_sound true fuel st0 0 0 _ _ _ Hrun [] (fun _ => eq_refl)) as HR.
  destruct (HR t k) as [n [k' [E D]]]. cbv beta in E. rewrite !app_nil_r in E.
  replace (A - 0)%Z with A in D by lia.
  assert (Hp : (0 <= A * pw4 t)%Z) by (apply Z.mul_nonneg_nonneg; [lia | pose proof (pw4_pos t); lia]).
  destruct k' as [| j]; [lia |].
  exists (n + S O), (j + S O). split.
  - rewrite tickN_add, E. cbn [tickN].
    assert (HX : dpass Q4 [TM80.W10] (conc t (pre, true, post)) =
                 PRoot (true :: false :: oa ++ repeat false (3 * t) ++ ob)).
    { pose proof (tickG_sound pre post fr true oa ob Ht t [] (fun _ => eq_refl)) as H1.
      rewrite !app_nil_r in H1. exact H1. }
    assert (Hd2 : dpass Q4 [TM80.W10] (oa ++ repeat false (3 * t) ++ ob) =
                  PNil (rep10 (S O) ++ [true; true; true] ++ repeat false (z1 + 3 * t + z2) ++ w')).
    { rewrite (dpass_stop_app oa p rest _ _ Hs Hd), Hob.
      replace (z1 + 3 * t + z2) with (z1 + (3 * t + z2)) by lia.
      rewrite (@repeat_app _ false z1 (3 * t + z2)), (@repeat_app _ false (3 * t) z2).
      rewrite <- !app_assoc. reflexivity. }
    rewrite (level_end_Slev 2 j _ _ (S O) _ w' HX Hd2). reflexivity.
  - rewrite Nat2Z.inj_add. lia.
Qed.

(** ** A level: bulk, end phase, level-end tick *)

Theorem level_step : forall je T u w b a' w' (dk : Z),
  bval b = T -> length b = 2 * u ->
  (forall k, (1 <= k)%nat -> exists n M',
     tickN 3 n (rep10 k ++ c1101 ++ repeat true (3 * (2 + 2 * T)) ++ rep10 je ++ c1101 ++ encb false b ++ w) =
       Some (Slev M' a' w') /\ Z.of_nat M' = (Z.of_nat k + dk)%Z) ->
  exists n M', tickN 3 n (Slev (je + 3 * T + 3) (3 * u + 1) w) = Some (Slev M' a' w') /\
    (3 * Z.of_nat M' + 2 = 2 * pw4 (2 + 2 * T) + 3 * dk)%Z.
Proof.
  intros je T u w b a' w' dk Hv Hl H.
  assert (HT : T < 2 ^ (2 * u)) by (rewrite <- Hv, <- Hl; apply bval_lt).
  destruct (level_bulk_exact 3 je T u w HT) as [cnt [b' [Hb [Hv' [Hl' Hk]]]]].
  assert (Hbb : b' = b) by (apply bval_inj; lia). subst b'.
  assert (Hp16 : 1 <= 16 ^ T) by (pose proof (Nat.pow_nonzero 16 T); lia).
  assert (Hk1 : 1 <= kcyc 2 T 10) by lia.
  destruct (H _ Hk1) as [n [M' [E D]]].
  exists (cnt + n), M'. split.
  - rewrite tickN_add, Hb. unfold Ptape.
    replace (4 + 4 * T) with (2 * (2 + 2 * T)) by lia. rewrite encb_even2_nil. exact E.
  - rewrite pw4_16. lia.
Qed.

(** ** Division by a constant, most significant bit first *)

Fixpoint dm (m : N) (b : list bool) (r : N) : list bool * N :=
  match b with
  | [] => ([], r)
  | x :: b' =>
    let (o, r1) := dm m b' r in
    let v := (2 * r1 + (if x then 1 else 0))%N in
    if (m <=? v)%N then (true :: o, (v - m)%N) else (false :: o, v)
  end.

Lemma dm_cons : forall m x b r,
  dm m (x :: b) r =
  let (o, r1) := dm m b r in
  let v := (2 * r1 + (if x then 1 else 0))%N in
  if (m <=? v)%N then (true :: o, (v - m)%N) else (false :: o, v).
Proof. reflexivity. Qed.

Lemma dm_spec : forall m b r o r', (r < m)%N -> dm m b r = (o, r') ->
  (Z.of_N r * 2 ^ Z.of_nat (length b) + Z.of_nat (bval b) = Z.of_N m * Z.of_nat (bval o) + Z.of_N r')%Z /\
  length o = length b /\ (r' < m)%N.
Proof.
  intros m. induction b as [| x b IH]; intros r o r' Hr H.
  - cbn [dm] in H. injection H as <- <-. cbn [length bval].
    split; [| split; [reflexivity | exact Hr]].
    change (Z.of_nat O) with 0%Z. rewrite Z.pow_0_r. lia.
  - rewrite dm_cons in H. destruct (dm m b r) as [o1 r1] eqn:E.
    destruct (IH r o1 r1 Hr E) as [He [Hlen Hr1]].
    cbv zeta in H.
    remember (2 * r1 + (if x then 1 else 0))%N as v eqn:Ev.
    assert (Hv : Z.of_N v = (2 * Z.of_N r1 + Z.of_nat (if x then 1 else 0)%nat)%Z)
      by (subst v; destruct x; lia).
    assert (Hvm : (v < 2 * m)%N) by (subst v; destruct x; lia).
    clear Ev.
    assert (Hpw : (2 ^ Z.of_nat (length (x :: b)) = 2 * 2 ^ Z.of_nat (length b))%Z).
    { cbn [length]. rewrite Nat2Z.inj_succ, Z.pow_succ_r by lia. reflexivity. }
    assert (Hb : Z.of_nat (bval (x :: b)) =
                 (Z.of_nat (if x then 1 else 0)%nat + 2 * Z.of_nat (bval b))%Z).
    { change (bval (x :: b)) with ((if x then 1 else 0) + 2 * bval b)%nat. lia. }
    destruct (m <=? v)%N eqn:Hc; [apply N.leb_le in Hc | apply N.leb_gt in Hc];
      injection H as <- <-; rewrite Hpw, Hb.
    + change (bval (true :: o1)) with (1 + 2 * bval o1)%nat.
      split; [lia | split; [cbn [length]; lia | lia]].
    + change (bval (false :: o1)) with (0 + 2 * bval o1)%nat.
      split; [lia | split; [cbn [length]; lia | lia]].
Qed.

Lemma dm_app : forall m a b r,
  dm m (a ++ b) r = let (ob, r1) := dm m b r in let (oa, r2) := dm m a r1 in (oa ++ ob, r2).
Proof.
  intros m. induction a as [| x a IH]; intros b r.
  - cbn [app dm]. destruct (dm m b r). reflexivity.
  - cbn [app dm]. rewrite IH. destruct (dm m b r) as [ob r1]. destruct (dm m a r1) as [oa r2].
    cbv zeta. destruct (m <=? _)%N; reflexivity.
Qed.

Lemma dm_app_eq : forall m a b r ob r1 oa r2,
  dm m b r = (ob, r1) -> dm m a r1 = (oa, r2) -> dm m (a ++ b) r = (oa ++ ob, r2).
Proof.
  intros m a b r ob r1 oa r2 H1 H2. rewrite dm_app, H1. cbv beta iota. rewrite H2. reflexivity.
Qed.

(** Repeated blocks. *)
Definition rp (P : list bool) (q : nat) : list bool := concat (repeat P q).

Lemma rp_S : forall P q, rp P (S q) = P ++ rp P q.
Proof. reflexivity. Qed.

Lemma rp_add : forall P a b, rp P (a + b) = rp P a ++ rp P b.
Proof.
  intros P a b. induction a as [| a IH]; [reflexivity |].
  cbn [Nat.add]. rewrite !rp_S, IH, app_assoc. reflexivity.
Qed.

Lemma rp_mul : forall P a b, rp P (b * a) = rp (rp P a) b.
Proof.
  intros P a b. induction b as [| b IH]; [reflexivity |].
  cbn [Nat.mul]. rewrite rp_add, IH, rp_S. reflexivity.
Qed.

Lemma length_rp : forall P q, length (rp P q) = q * length P.
Proof.
  intros P q. induction q as [| q IH]; [reflexivity |].
  rewrite rp_S, length_app, IH. cbn [Nat.mul]. reflexivity.
Qed.

Lemma map_rp : forall (f : bool -> bool) P q, map f (rp P q) = rp (map f P) q.
Proof.
  intros f P q. induction q as [| q IH]; [reflexivity |].
  rewrite !rp_S, map_app, IH. reflexivity.
Qed.

Lemma dm_rp : forall m P r Po, dm m P r = (Po, r) -> forall q, dm m (rp P q) r = (rp Po q, r).
Proof.
  intros m P r Po H q. induction q as [| q IH]; [reflexivity |].
  change (rp P (S q)) with (P ++ rp P q). change (rp Po (S q)) with (Po ++ rp Po q).
  exact (dm_app_eq m P (rp P q) r (rp Po q) r Po r IH H).
Qed.

(** ** The next counter word *)

Lemma length_rep01 : forall n, length (rep01 n) = 2 * n.
Proof.
  induction n as [| n IH]; [reflexivity |].
  unfold rep01 in *. cbn [repeat concat app length]. lia.
Qed.

Lemma bval_rep01 : forall n, 3 * bval (rep01 n) + 2 = 2 * 2 ^ (2 * n).
Proof.
  induction n as [| n IH]; [reflexivity |].
  unfold rep01 in *. cbn [repeat concat app bval].
  replace (2 * S n) with (S (S (2 * n))) by lia. rewrite !Nat.pow_succ_r'. lia.
Qed.

Lemma bval_Zl : forall h Cc, 2 <= h ->
  3 * bval ([false; false; true; false] ++ rep01 (h - 2) ++ Cc) + 20 =
  2 * 2 ^ (2 * h) + 3 * (2 ^ (2 * h) * bval Cc).
Proof.
  intros h Cc Hh. rewrite !bval_app, length_rep01. cbn [length bval].
  pose proof (bval_rep01 (h - 2)) as Hr.
  replace (2 * h) with (4 + 2 * (h - 2)) by lia. rewrite Nat.pow_add_r. change (2 ^ 4) with 16.
  lia.
Qed.

(** If the end phase of a level with half-width [h] adds [4^h * bval Cc] to the prefix, the counter
    word of the next level is the quotient of [0100 (10)^(h-2) Cc] by 3 and its class is the remainder. *)
Theorem stageB : forall h Cc b' r M',
  (2 <= h)%nat ->
  dm 3 ([false; false; true; false] ++ rep01 (h - 2) ++ Cc) 0 = (b', r) ->
  (3 * Z.of_nat M' + 2 = 2 * pw4 h + 3 * (pw4 h * Z.of_nat (bval Cc)))%Z ->
  M' = (3 + N.to_nat r) + 3 * bval b' + 3 /\ length b' = 2 * h + length Cc /\ (r < 3)%N.
Proof.
  intros h Cc b' r M' Hh Hd HM.
  destruct (dm_spec 3 _ 0 b' r ltac:(reflexivity) Hd) as [He [Hlen Hr]].
  pose proof (bval_Zl h Cc Hh) as Hn.
  assert (Hp : Z.of_nat (2 ^ (2 * h)) = pw4 h) by (rewrite pow2Z, pw2_2t; reflexivity).
  remember (2 ^ (2 * h))%nat as X eqn:EX in *. clear EX.
  apply (f_equal Z.of_nat) in Hn.
  repeat first [rewrite Nat2Z.inj_add in Hn | rewrite Nat2Z.inj_mul in Hn].
  rewrite Hp in Hn.
  split; [| split; [| exact Hr]].
  - lia.
  - rewrite Hlen, !length_app, length_rep01. cbn [length]. lia.
Qed.

End Eng694.

Module Cert694.

(** * 1RB1LB_1RC0RD_0LA1RE_0RF1LC_1LA0RB_---1LC: certificates for one level

    Everything here is proved once.  A level then needs only computations:

    - [endcert]: the whole end phase of a level whose counter word is a literal
      ([endcert_sound]);
    - [c4cert]: the end phase of a level of class 4, for a counter word [lo ++ rest] with a
      literal low part and an arbitrary rest ([c4cert_sound]);
    - [dmB]: division by a constant of a word given as a list of blocks, literal or
      repeated ([dmB_sound]);
    - [level_next]: from the level statement [Lvl] and an end phase to the next [Lvl]. *)

Import Individual62.
Import T694_levels End694 Sym694 Lev694 Lvl1_694 Eng694.
Import Lia Arith PeanoNat Bool NArith ZArith.
Import Coq.Lists.List.
Import ListNotations.

(** ** Small tools *)

Fixpoint leqb (a b : list bool) : bool :=
  match a, b with
  | [], [] => true
  | x :: a', y :: b' => Bool.eqb x y && leqb a' b'
  | _, _ => false
  end.

Lemma leqb_eq : forall a b, leqb a b = true -> a = b.
Proof.
  induction a as [| x a IH]; intros [| y b] H; try discriminate; [reflexivity |].
  cbn [leqb] in H. apply andb_prop in H. destruct H as [H1 H2].
  apply Bool.eqb_prop in H1. subst y. f_equal. exact (IH _ H2).
Qed.

Fixpoint lead0 (l : list bool) : nat * list bool :=
  match l with
  | false :: l' => let (z, r) := lead0 l' in (S z, r)
  | _ => (O, l)
  end.

Lemma lead0_spec : forall l z r, lead0 l = (z, r) -> l = repeat false z ++ r.
Proof.
  induction l as [| x l IH]; intros z r H.
  - cbn [lead0] in H. injection H as <- <-. reflexivity.
  - destruct x.
    + cbn [lead0] in H. injection H as <- <-. reflexivity.
    + cbn [lead0] in H. destruct (lead0 l) as [z1 r1] eqn:E. injection H as <- <-.
      cbn [repeat app]. f_equal. exact (IH _ _ eq_refl).
Qed.

Fixpoint zbits (z : Z) (n : nat) : list bool :=
  match n with O => [] | S n' => Z.odd z :: zbits (Z.div2 z) n' end.

Lemma tickN_comp : forall f a b x y z,
  tickN f a x = Some y -> tickN f b y = Some z -> tickN f (a + b) x = Some z.
Proof. intros f a b x y z H1 H2. rewrite tickN_add, H1. exact H2. Qed.

Lemma pw4_ge4 : forall h, (1 <= h)%nat -> (4 <= pw4 h)%Z.
Proof.
  intros [| h'] Hh; [lia |]. change (S h') with (1 + h')%nat. rewrite pw4_add.
  change (pw4 1) with 4%Z. pose proof (pw4_pos h'). lia.
Qed.

(** ** The end phase of a level with a literal counter word *)

Definition endcert (fuel : nat) (st0 : sst) : option (Z * nat * nat * list bool) :=
  let '(st, aa, bb) := grun true fuel st0 0 0 in
  let '(pre, x, post) := st in
  if x && (bb =? 0)%Z && (0 <=? aa)%Z then
    match tickG pre post with
    | Some (fr, rt, oa, ob) =>
      if rt then
        match scanr Q4 oa with
        | Stop _ _ =>
          match dpass Q4 [TM80.W10] oa with
          | PNil d =>
            if leqb d (rep10 (S O) ++ [true; true; true] ++ repeat false (length d - 5)) then
              let (z2, w') := lead0 ob in Some (aa, length d - 5, z2, w')
            else None
          | _ => None
          end
        | Fin _ _ => None
        end
      else None
    | None => None
    end
  else None.

Theorem endcert_sound : forall fuel st0 aa z1 z2 w',
  endcert fuel st0 = Some (aa, z1, z2, w') ->
  forall t k, (1 <= k)%nat -> exists n M',
    tickN 3 n (rep10 k ++ conc t st0) = Some (Slev M' (z1 + 3 * t + z2) w') /\
    Z.of_nat M' = (Z.of_nat k + aa * pw4 t)%Z.
Proof.
  intros fuel st0 aa z1 z2 w' H. unfold endcert in H.
  destruct (grun true fuel st0 0 0) as [[[[pre x] post] a] b] eqn:Eg.
  destruct (x && (b =? 0)%Z && (0 <=? a)%Z) eqn:Ec; [| discriminate].
  apply andb_prop in Ec. destruct Ec as [Ec Ea]. apply andb_prop in Ec. destruct Ec as [Ex Eb].
  subst x. apply Z.eqb_eq in Eb. subst b. apply Z.leb_le in Ea.
  destruct (tickG pre post) as [[[[fr rt] oa] ob] |] eqn:Et; [| discriminate].
  destruct rt; [| discriminate].
  destruct (scanr Q4 oa) as [s p | p rest] eqn:Es; [discriminate |].
  destruct (dpass Q4 [TM80.W10] oa) as [| d | T] eqn:Ed; try discriminate.
  destruct (leqb d (rep10 (S O) ++ [true; true; true] ++ repeat false (length d - 5))) eqn:El;
    [| discriminate].
  destruct (lead0 ob) as [z2' w''] eqn:E0.
  injection H as <- <- <- <-.
  apply leqb_eq in El. apply lead0_spec in E0.
  assert (Ed' : dpass Q4 [TM80.W10] oa =
                PNil (rep10 (S O) ++ [true; true; true] ++ repeat false (length d - 5)))
    by (rewrite Ed; f_equal; exact El).
  exact (endphase fuel st0 pre post a fr oa ob p rest (length d - 5) z2' w'' Eg Ea Et Es Ed' E0).
Qed.

(** ** The open run: stops where the next fill would reach into the untouched rest *)

Definition stopq (st : sst) : bool :=
  let '(pre, x, post) := st in
  match pre with
  | true :: true :: false :: true :: cs =>
    let (blo, r0) := parse false cs in
    match r0 with
    | [] => let (bhi, rs) := parse (par false blo) post in
            match rs with [] => true | _ => false end
    | _ => false
    end
  | _ => false
  end.

Fixpoint grunO (fuel : nat) (st : sst) (A B : Z) : sst * Z * Z :=
  match fuel with
  | O => (st, A, B)
  | S f =>
    if stopq st then (st, A, B) else
    match gstep false st with
    | Some (st', a, b) => grunO f st' (A + a)%Z (B + b)%Z
    | None => (st, A, B)
    end
  end.

Lemma grunO_sound : forall fuel st A B st' A' B', grunO fuel st A B = (st', A', B') ->
  forall R, ReachA (A' - A) (B' - B) (fun t => conc t st ++ R) (fun t => conc t st' ++ R).
Proof.
  assert (Hrefl : forall (st : sst) (A B : Z) (R : list bool),
    ReachA (A - A) (B - B) (fun t => conc t st ++ R) (fun t => conc t st ++ R)).
  { intros st A B R. replace (A - A)%Z with 0%Z by lia. replace (B - B)%Z with 0%Z by lia.
    apply reachA_refl. }
  induction fuel as [| f IH]; intros st A B st' A' B' H R.
  - cbn [grunO] in H. injection H as <- <- <-. apply Hrefl.
  - cbn [grunO] in H. destruct (stopq st).
    + injection H as <- <- <-. apply Hrefl.
    + destruct (gstep false st) as [[[st1 a] b] |] eqn:E.
      * assert (HR : false = true -> R = []) by discriminate.
        pose proof (reachA_trans _ _ _ _ _ _ _ (gstep_sound _ _ _ _ _ E R HR) (IH _ _ _ _ _ _ H R)) as HT.
        replace (A' - A)%Z with (a + (A' - (A + a)))%Z by lia.
        replace (B' - B)%Z with (b + (B' - (B + b)))%Z by lia. exact HT.
      * injection H as <- <- <-. apply Hrefl.
Qed.

(** ** Class 4: one fill covers the whole counter word *)

Lemma class4_arith : forall k k1 dd M' A1 B1 A3 P Qm V H4 bm br bl nr c0 : Z,
  (k1 = k + A1 * H4 + B1 ->
   dd = P * (H4 * (Qm * V - (bm + Qm * br))) - 1 - bl ->
   M' = k1 + dd + A3 * (H4 * (P * Qm) * V) ->
   B1 - 1 - bl = 0 ->
   c0 = A1 + P * Qm - P * bm ->
   nr + br + 1 = V ->
   M' = k + (c0 + P * Qm * (nr + V * A3)) * H4)%Z.
Proof.
  intros k k1 dd M' A1 B1 A3 P Qm V H4 bm br bl nr c0 E1 E2 E3 E4 E5 E6.
  subst k1 dd M' c0.
  assert (E7 : B1 = (1 + bl)%Z) by lia. assert (E8 : nr = (V - br - 1)%Z) by lia.
  subst B1 nr. ring.
Qed.

Theorem class4 : forall f1 f3 je lo w blo mid A1 B1 A3 z1 z2 w' cb ab s la,
  grunO f1 (c1101, true, rep10 je ++ c1101 ++ encb false lo) 0 0 =
    ((c1101 ++ encb false blo, false, encb (par false blo) mid), A1, B1) ->
  par (par false blo) mid = par false lo ->
  length blo + length mid = 2 * s ->
  endcert f3 (c1101, true, w) = Some (A3, z1, z2, w') ->
  (B1 - 1 - Z.of_N (bvalN blo) = 0)%Z ->
  (Z.of_N (bvalN cb) = A1 + 2 ^ Z.of_nat (2 * s) - 2 ^ Z.of_nat (length blo) * Z.of_N (bvalN mid))%Z ->
  length cb = 2 * s ->
  Z.of_N (bvalN ab) = A3 -> length ab = 2 * la -> z1 + z2 = 3 * la + 1 ->
  forall rest v h, length rest = 2 * v -> (1 <= h)%nat ->
  forall k, (1 <= k)%nat -> exists n M',
    tickN 3 n (rep10 k ++ c1101 ++ repeat true (3 * h) ++ rep10 je ++ c1101 ++ encb false (lo ++ rest) ++ w) =
      Some (Slev M' (3 * (h + (s + v + la)) + 1) w') /\
    Z.of_nat M' = (Z.of_nat k + Z.of_nat (bval (cb ++ map negb rest ++ ab)) * pw4 h)%Z.
Proof.
  intros f1 f3 je lo w blo mid A1 B1 A3 z1 z2 w' cb ab s la Hg Hpar Hs Hend HB Hcb Hlcb Hab Hlab Hz
         rest v h Hv Hh k Hk.
  pose proof (grunO_sound _ _ _ _ _ _ _ Hg (encb (par false lo) rest ++ w)) as HR1.
  destruct (HR1 h k) as [n1 [k1 [E1 D1]]]. cbv beta in E1.
  assert (Hstart : c1101 ++ repeat true (3 * h) ++ rep10 je ++ c1101 ++ encb false (lo ++ rest) ++ w =
                   conc h (c1101, true, rep10 je ++ c1101 ++ encb false lo) ++
                   encb (par false lo) rest ++ w).
  { unfold conc. rewrite (encb_app lo), <- ?app_assoc. reflexivity. }
  assert (Hmid : conc h (c1101 ++ encb false blo, false, encb (par false blo) mid) ++
                 encb (par false lo) rest ++ w =
                 c1101 ++ encb false (blo ++ repeat false (2 * h) ++ mid ++ rest) ++ w).
  { unfold conc. rewrite (encb_app blo), encb_rep2, (encb_app mid), Hpar, <- ?app_assoc. reflexivity. }
  rewrite Hmid in E1.
  assert (Hlen : length (blo ++ repeat false (2 * h) ++ mid ++ rest) = 2 * (h + s + v)).
  { rewrite !length_app, repeat_length. lia. }
  assert (HD0 : Z.of_nat (2 ^ length (blo ++ repeat false (2 * h) ++ mid ++ rest) - 1 -
                          bval (blo ++ repeat false (2 * h) ++ mid ++ rest)) =
     (2 ^ Z.of_nat (length blo) *
        (pw4 h * (2 ^ Z.of_nat (length (mid ++ rest)) - Z.of_nat (bval (mid ++ rest))) - 0)
      - 1 - Z.of_nat (bval blo))%Z).
  { rewrite fill_delta_gen, repeat_length, pw2_2t, bval_repeat_false. reflexivity. }
  pose proof (counter_fill 3 k1 (blo ++ repeat false (2 * h) ++ mid ++ rest) w) as Hf.
  remember (2 ^ length (blo ++ repeat false (2 * h) ++ mid ++ rest) - 1 -
            bval (blo ++ repeat false (2 * h) ++ mid ++ rest)) as dd eqn:Edd.
  clear Edd. rewrite Hlen, encb_even2_nil in Hf.
  assert (Hdd : (1 <= k1 + dd)%nat).
  { pose proof (bval_lt blo) as L1. pose proof (bval_lt (mid ++ rest)) as L2.
    apply Nat2Z.inj_lt in L1. apply Nat2Z.inj_lt in L2. rewrite pow2Z in L1, L2.
    pose proof (pw4_ge4 h Hh) as H4.
    assert (X1 : (4 * 1 <= pw4 h * (2 ^ Z.of_nat (length (mid ++ rest)) - Z.of_nat (bval (mid ++ rest))))%Z)
      by (apply Z.mul_le_mono_nonneg; lia).
    assert (X2 : (2 ^ Z.of_nat (length blo) * (4 * 1) <=
                  2 ^ Z.of_nat (length blo) *
                  (pw4 h * (2 ^ Z.of_nat (length (mid ++ rest)) - Z.of_nat (bval (mid ++ rest)))))%Z)
      by (apply Z.mul_le_mono_nonneg_l; lia).
    lia. }
  destruct (endcert_sound _ _ _ _ _ _ Hend (h + s + v) (k1 + dd) Hdd) as [n3 [M' [E3 D3]]].
  unfold conc in E3.
  exists (n1 + (2 * dd + n3)), M'. split.
  - rewrite Hstart.
    apply (tickN_comp 3 n1 (2 * dd + n3) _ _ _ E1).
    apply (tickN_comp 3 (2 * dd) n3 _ _ _ Hf).
    replace (3 * (h + (s + v + la)) + 1) with (z1 + 3 * (h + s + v) + z2) by lia. exact E3.
  - assert (Hl2 : length cb = length blo + length mid) by lia.
    assert (Hbv : Z.of_nat (bval (cb ++ map negb rest ++ ab)) =
       (Z.of_N (bvalN cb) + 2 ^ Z.of_nat (length blo) * 2 ^ Z.of_nat (length mid) *
          (Z.of_nat (bval (map negb rest)) + 2 ^ Z.of_nat (length rest) * A3))%Z).
    { rewrite !bval_app, Hl2, length_map.
      repeat first [rewrite Nat2Z.inj_add | rewrite Nat2Z.inj_mul | rewrite pow2Z].
      rewrite Z.pow_add_r by lia. rewrite (bvalZ cb), (bvalZ ab), Hab. ring. }
    pose proof (bval_neg rest) as Hn. apply (f_equal Z.of_nat) in Hn.
    repeat first [rewrite Nat2Z.inj_add in Hn | rewrite pow2Z in Hn].
    change (Z.of_nat 1) with 1%Z in Hn.
    rewrite <- (bvalZ blo) in HB. rewrite <- (bvalZ mid) in Hcb.
    rewrite <- Hs, Nat2Z.inj_add, Z.pow_add_r in Hcb by lia.
    rewrite length_app, bval_app in HD0.
    repeat first [rewrite Nat2Z.inj_add in HD0 | rewrite Nat2Z.inj_mul in HD0 | rewrite pow2Z in HD0].
    rewrite Z.pow_add_r in HD0 by lia.
    rewrite Nat2Z.inj_add in D3.
    rewrite !pw4_add, <- (pw2_2t s), <- (pw2_2t v), <- Hs, <- Hv, Nat2Z.inj_add, Z.pow_add_r in D3 by lia.
    rewrite Hbv.
    apply (class4_arith (Z.of_nat k) (Z.of_nat k1) (Z.of_nat dd) (Z.of_nat M') A1 B1 A3
             (2 ^ Z.of_nat (length blo)) (2 ^ Z.of_nat (length mid)) (2 ^ Z.of_nat (length rest))
             (pw4 h) (Z.of_nat (bval mid)) (Z.of_nat (bval rest)) (Z.of_nat (bval blo))
             (Z.of_nat (bval (map negb rest))) (Z.of_N (bvalN cb))); lia.
Qed.

Definition c4cert (f1 f3 je : nat) (lo w : list bool) :
  option (nat * nat * list bool * list bool * list bool) :=
  let '(st, a1, b1) := grunO f1 (c1101, true, rep10 je ++ c1101 ++ encb false lo) 0 0 in
  let '(pre, x, post) := st in
  match pre with
  | true :: true :: false :: true :: cs =>
    let (blo, r0) := parse false cs in
    let (mid, rs) := parse (par false blo) post in
    match endcert f3 (c1101, true, w) with
    | Some (a3, z1, z2, w') =>
      if negb x && leqb r0 [] && leqb rs [] && Bool.eqb (par (par false blo) mid) (par false lo)
         && (length blo + length mid =? 2 * Nat.div2 (length blo + length mid))%nat
         && (b1 - 1 - Z.of_N (bvalN blo) =? 0)%Z
         && (Z.of_N (bvalN (zbits (a1 + 2 ^ Z.of_nat (2 * Nat.div2 (length blo + length mid))
                                    - 2 ^ Z.of_nat (length blo) * Z.of_N (bvalN mid))
                                  (2 * Nat.div2 (length blo + length mid)))) =?
             a1 + 2 ^ Z.of_nat (2 * Nat.div2 (length blo + length mid))
                - 2 ^ Z.of_nat (length blo) * Z.of_N (bvalN mid))%Z
         && (length (zbits (a1 + 2 ^ Z.of_nat (2 * Nat.div2 (length blo + length mid))
                                    - 2 ^ Z.of_nat (length blo) * Z.of_N (bvalN mid))
                           (2 * Nat.div2 (length blo + length mid))) =?
             2 * Nat.div2 (length blo + length mid))%nat
         && (Z.of_N (bvalN (zbits a3 (2 * ((z1 + z2 - 1) / 3)))) =? a3)%Z
         && (length (zbits a3 (2 * ((z1 + z2 - 1) / 3))) =? 2 * ((z1 + z2 - 1) / 3))%nat
         && (z1 + z2 =? 3 * ((z1 + z2 - 1) / 3) + 1)%nat
      then Some (Nat.div2 (length blo + length mid), (z1 + z2 - 1) / 3,
                 zbits (a1 + 2 ^ Z.of_nat (2 * Nat.div2 (length blo + length mid))
                           - 2 ^ Z.of_nat (length blo) * Z.of_N (bvalN mid))
                       (2 * Nat.div2 (length blo + length mid)),
                 zbits a3 (2 * ((z1 + z2 - 1) / 3)), w')
      else None
    | None => None
    end
  | _ => None
  end.

Theorem c4cert_sound : forall f1 f3 je lo w s la cb ab w',
  c4cert f1 f3 je lo w = Some (s, la, cb, ab, w') ->
  forall rest v h, length rest = 2 * v -> (1 <= h)%nat ->
  forall k, (1 <= k)%nat -> exists n M',
    tickN 3 n (rep10 k ++ c1101 ++ repeat true (3 * h) ++ rep10 je ++ c1101 ++ encb false (lo ++ rest) ++ w) =
      Some (Slev M' (3 * (h + (s + v + la)) + 1) w') /\
    Z.of_nat M' = (Z.of_nat k + Z.of_nat (bval (cb ++ map negb rest ++ ab)) * pw4 h)%Z.
Proof.
  intros f1 f3 je lo w s la cb ab w' H. unfold c4cert in H.
  destruct (grunO f1 (c1101, true, rep10 je ++ c1101 ++ encb false lo) 0 0)
    as [[[[pre x] post] a1] b1] eqn:Eg.
  destruct pre as [| [] pre]; try discriminate.
  destruct pre as [| [] pre]; try discriminate.
  destruct pre as [| [] pre]; try discriminate.
  destruct pre as [| [] cs]; try discriminate.
  destruct (parse false cs) as [blo r0] eqn:E1.
  destruct (parse (par false blo) post) as [mid rs] eqn:E2.
  destruct (endcert f3 (c1101, true, w)) as [[[[a3 z1] z2] w''] |] eqn:Ee; [| discriminate].
  match type of H with (if ?c then _ else _) = _ => destruct c eqn:Hc; [| discriminate] end.
  injection H as <- <- <- <- <-.
  apply andb_prop in Hc. destruct Hc as [Hc C11].
  apply andb_prop in Hc. destruct Hc as [Hc C10].
  apply andb_prop in Hc. destruct Hc as [Hc C9].
  apply andb_prop in Hc. destruct Hc as [Hc C8].
  apply andb_prop in Hc. destruct Hc as [Hc C7].
  apply andb_prop in Hc. destruct Hc as [Hc C6].
  apply andb_prop in Hc. destruct Hc as [Hc C5].
  apply andb_prop in Hc. destruct Hc as [Hc C4].
  apply andb_prop in Hc. destruct Hc as [Hc C3].
  apply andb_prop in Hc. destruct Hc as [C1 C2].
  apply negb_true_iff in C1. subst x.
  apply leqb_eq in C2. apply leqb_eq in C3. subst r0 rs.
  apply Bool.eqb_prop in C4.
  apply Nat.eqb_eq in C5. apply Z.eqb_eq in C6. apply Z.eqb_eq in C7. apply Nat.eqb_eq in C8.
  apply Z.eqb_eq in C9. apply Nat.eqb_eq in C10. apply Nat.eqb_eq in C11.
  pose proof (parse_spec (length cs) cs (le_n _) false blo [] E1) as Hcs. rewrite app_nil_r in Hcs.
  pose proof (parse_spec (length post) post (le_n _) _ mid [] E2) as Hpost. rewrite app_nil_r in Hpost.
  subst cs post.
  exact (class4 f1 f3 je lo w blo mid a1 b1 a3 z1 z2 w'' _ _ _ _ Eg C4 C5 Ee C6 C7 C8 C9 C10 C11).
Qed.

(** ** Words as lists of blocks, and their division *)

Inductive blk := Lit (l : list bool) | Rep (P : list bool) (q : nat).

Definition bden (x : blk) : list bool := match x with Lit l => l | Rep P q => rp P q end.

Fixpoint den (bs : list blk) : list bool :=
  match bs with [] => [] | x :: bs' => bden x ++ den bs' end.

Fixpoint dmB (m : N) (bs : list blk) (r : N) : option (list blk * N) :=
  match bs with
  | [] => Some ([], r)
  | x :: bs' =>
    match dmB m bs' r with
    | None => None
    | Some (os, r1) =>
      match x with
      | Lit l => let (o, r2) := dm m l r1 in Some (Lit o :: os, r2)
      | Rep P q => let (o, r2) := dm m P r1 in
                   if (r2 =? r1)%N then Some (Rep o q :: os, r1) else None
      end
    end
  end.

Lemma dmB_sound : forall m bs r os r', dmB m bs r = Some (os, r') -> dm m (den bs) r = (den os, r').
Proof.
  intros m. induction bs as [| x bs IH]; intros r os r' H.
  - cbn [dmB] in H. injection H as <- <-. reflexivity.
  - cbn [dmB] in H. destruct (dmB m bs r) as [[os1 r1] |] eqn:E; [| discriminate].
    specialize (IH _ _ _ E).
    destruct x as [l | P q].
    + destruct (dm m l r1) as [o r2] eqn:El. injection H as <- <-.
      cbn [den bden]. exact (dm_app_eq m l (den bs) r (den os1) r1 o r2 IH El).
    + destruct (dm m P r1) as [o r2] eqn:EP. destruct (r2 =? r1)%N eqn:Er; [| discriminate].
      apply N.eqb_eq in Er. subst r2. injection H as <- <-.
      cbn [den bden].
      exact (dm_app_eq m (rp P q) (den bs) r (den os1) r1 (rp o q) r1 IH (dm_rp m P r1 o EP q)).
Qed.

(** ** The level statement and the step to the next level *)

Definition Lvl (je : nat) (b : list bool) (u : nat) (w : list bool) : Prop :=
  length b = 2 * u /\
  exists n, tickN 3 n D0 = Some (Slev (je + 3 * bval b + 3) (3 * u + 1) w).

Theorem level_next : forall je b u w Cc lc b' r w',
  Lvl je b u w -> length Cc = 2 * lc ->
  (forall k, (1 <= k)%nat -> exists n M',
     tickN 3 n (rep10 k ++ c1101 ++ repeat true (3 * (2 + 2 * bval b)) ++ rep10 je ++ c1101 ++
                encb false b ++ w) =
       Some (Slev M' (3 * (2 + 2 * bval b + lc) + 1) w') /\
     Z.of_nat M' = (Z.of_nat k + Z.of_nat (bval Cc) * pw4 (2 + 2 * bval b))%Z) ->
  dm 3 ([false; false; true; false] ++ rep01 (2 * bval b) ++ Cc) 0 = (b', r) ->
  Lvl (3 + N.to_nat r) b' (2 + 2 * bval b + lc) w'.
Proof.
  intros je b u w Cc lc b' r w' [Hl [n0 H0]] HC Hend Hd.
  destruct (level_step je (bval b) u w b _ w' _ eq_refl Hl Hend) as [n [M' [E D]]].
  assert (Hd' : dm 3 ([false; false; true; false] ++ rep01 (2 + 2 * bval b - 2) ++ Cc) 0 = (b', r)).
  { replace (2 + 2 * bval b - 2) with (2 * bval b) by lia. exact Hd. }
  assert (HMz : (3 * Z.of_nat M' + 2 = 2 * pw4 (2 + 2 * bval b) +
                 3 * (pw4 (2 + 2 * bval b) * Z.of_nat (bval Cc)))%Z) by (rewrite D; ring).
  assert (H2 : (2 <= 2 + 2 * bval b)%nat) by lia.
  destruct (stageB (2 + 2 * bval b) Cc b' r M' H2 Hd' HMz) as [HM [Hlen Hr]].
  split; [rewrite Hlen, HC; lia |].
  exists (n0 + n). apply (tickN_comp 3 n0 n _ _ _ H0). rewrite <- HM. exact E.
Qed.

End Cert694.

Module Run694.

(** * 1RB1LB_1RC0RD_0LA1RE_0RF1LC_1LA0RB_---1LC: runs, cycles and the carry chain

    Proved once, for the levels of class 3 and 5, where the end phase eats the counter word a
    few bits per round:

    - [Run st F st' sh a]: from the state [st] followed by the cells [F], for every hidden
      width [t] and every rest of the tape, the machine reaches [st'] with the hidden width
      grown by [sh], and the prefix (10)^k grows by exactly [a * 4^t];
    - [run_cert]: a run is checked by one computation of the evaluator;
    - [run_comp], [run_iter]: runs compose, and a run that returns to its own state can be
      repeated any number of times (the pass over a repeated block);
    - [asm], [asm_sound]: the sum of the contributions of a list of runs and cycles is the
      value of a list of blocks (the carry chain);
    - [crun], [crun_run], [pasm]: runs checked round by round, at linear cost;
    - [stageA]: the end phase of a level from its runs, its closing computation and [asm]. *)

Import Individual62.
Import T694_levels End694 Sym694 Lev694 Lvl1_694 Eng694 Cert694.
Import Lia Arith PeanoNat Bool NArith ZArith.
Import Coq.Lists.List.
Import ListNotations.

(** ** Runs *)

Definition addpost (st : sst) (F : list bool) : sst :=
  let '(pre, x, post) := st in (pre, x, post ++ F).

Lemma conc_addpost : forall t st F, conc t (addpost st F) = conc t st ++ F.
Proof. intros t [[pre x] post] F. unfold addpost, conc. rewrite <- ?app_assoc. reflexivity. Qed.

Lemma conc_shift : forall t sh pre x post,
  conc t (pre, x, repeat x (3 * sh) ++ post) = conc (t + sh) (pre, x, post).
Proof.
  intros t sh pre x post. unfold conc. replace (3 * (t + sh)) with (3 * t + 3 * sh) by lia.
  rewrite repeat_app, <- ?app_assoc. reflexivity.
Qed.

Definition Run (st : sst) (F : list bool) (st' : sst) (sh : nat) (a : Z) : Prop :=
  forall t R k, exists n k',
    tickN 3 n (rep10 k ++ conc t st ++ F ++ R) = Some (rep10 k' ++ conc (t + sh) st' ++ R) /\
    Z.of_nat k' = (Z.of_nat k + a * pw4 t)%Z.

Lemma run_cert : forall n st F pre' x' post' sh a,
  grun false n (addpost st F) 0 0 = ((pre', x', repeat x' (3 * sh) ++ post'), a, 0%Z) ->
  Run st F (pre', x', post') sh a.
Proof.
  intros n st F pre' x' post' sh a H t R k.
  assert (HR : false = true -> R = []) by discriminate.
  destruct (grun_sound false n _ 0 0 _ _ _ H R HR t k) as [m [k' [E D]]]. cbv beta in E.
  rewrite conc_addpost, conc_shift, <- app_assoc in E.
  exists m, k'. split; [exact E | lia].
Qed.

Lemma run_nil : forall st, Run st [] st 0 0.
Proof.
  intros st t R k. exists O, k. split; [rewrite Nat.add_0_r; reflexivity | lia].
Qed.

Lemma run_comp : forall st F1 st1 sh1 a1 F2 st2 sh2 a2,
  Run st F1 st1 sh1 a1 -> Run st1 F2 st2 sh2 a2 ->
  Run st (F1 ++ F2) st2 (sh1 + sh2) (a1 + pw4 sh1 * a2).
Proof.
  intros st F1 st1 sh1 a1 F2 st2 sh2 a2 H1 H2 t R k.
  destruct (H1 t (F2 ++ R) k) as [n1 [k1 [E1 D1]]].
  destruct (H2 (t + sh1) R k1) as [n2 [k2 [E2 D2]]].
  exists (n1 + n2), k2. split.
  - rewrite <- app_assoc. apply (tickN_comp 3 n1 n2 _ _ _ E1). rewrite Nat.add_assoc. exact E2.
  - rewrite pw4_add in D2. lia.
Qed.

Lemma run_eq : forall st F st' sh a sh' a',
  Run st F st' sh a -> sh = sh' -> a = a' -> Run st F st' sh' a'.
Proof. intros st F st' sh a sh' a' H E1 E2. subst. exact H. Qed.

Fixpoint geo (X : Z) (q : nat) : Z :=
  match q with O => 0%Z | S q' => (1 + X * geo X q')%Z end.

Lemma run_iter : forall st F sh a, Run st F st sh a ->
  forall q, Run st (rp F q) st (q * sh) (a * geo (pw4 sh) q).
Proof.
  intros st F sh a H. induction q as [| q IH].
  - apply (run_eq st [] st O 0%Z); [apply run_nil | reflexivity | cbn [geo]; ring].
  - rewrite rp_S.
    apply (run_eq st (F ++ rp F q) st (sh + q * sh) (a + pw4 sh * (a * geo (pw4 sh) q))%Z);
      [exact (run_comp _ _ _ _ _ _ _ _ _ H IH) | reflexivity | cbn [geo]; ring].
Qed.

(** ** The contributions of a list of runs and cycles *)

(** Lists of rounds [(a, sh)]: the value, the width, and the carry chain with small numbers. *)
Fixpoint pV (l : list (Z * nat)) : Z :=
  match l with [] => 0%Z | (a, sh) :: r => (a + pw4 sh * pV r)%Z end.

Fixpoint pSh (l : list (Z * nat)) : nat :=
  match l with [] => O | (_, sh) :: r => sh + pSh r end.

Fixpoint pasm (c : Z) (l : list (Z * nat)) : option (list bool * Z) :=
  match l with
  | [] => Some ([], c)
  | (a, sh) :: r =>
    if (Z.of_N (bvalN (zbits (c + a) (2 * sh))) + pw4 sh * ((c + a) / pw4 sh) =? c + a)%Z
       && (length (zbits (c + a) (2 * sh)) =? 2 * sh)%nat then
      match pasm ((c + a) / pw4 sh)%Z r with
      | Some (ws, c') => Some (zbits (c + a) (2 * sh) ++ ws, c')
      | None => None
      end
    else None
  end.

Lemma pasm_cons : forall c a sh r, pasm c ((a, sh) :: r) =
  if (Z.of_N (bvalN (zbits (c + a) (2 * sh))) + pw4 sh * ((c + a) / pw4 sh) =? c + a)%Z
     && (length (zbits (c + a) (2 * sh)) =? 2 * sh)%nat then
    match pasm ((c + a) / pw4 sh)%Z r with
    | Some (ws, c') => Some (zbits (c + a) (2 * sh) ++ ws, c')
    | None => None
    end
  else None.
Proof. reflexivity. Qed.

Lemma pasm_sound : forall l c w c', pasm c l = Some (w, c') ->
  (c + pV l = Z.of_nat (bval w) + pw4 (pSh l) * c')%Z /\ length w = 2 * pSh l.
Proof.
  induction l as [| [a sh] l IH]; intros c w c' H.
  - injection H as <- <-. split; [| reflexivity].
    change (pV []) with 0%Z. change (pw4 (pSh [])) with 1%Z.
    change (Z.of_nat (bval [])) with 0%Z. ring.
  - rewrite pasm_cons in H. remember (zbits (c + a) (2 * sh)) as X eqn:EX.
    match type of H with (if ?cnd then _ else _) = _ => destruct cnd eqn:Hc; [| discriminate] end.
    destruct (pasm ((c + a) / pw4 sh)%Z l) as [[ws c1'] |] eqn:E; [| discriminate].
    injection H as <- <-. apply andb_prop in Hc. destruct Hc as [Hv Hl].
    apply Z.eqb_eq in Hv. apply Nat.eqb_eq in Hl.
    destruct (IH _ _ _ E) as [IHv IHl].
    cbn [pV pSh].
    split; [| rewrite length_app, Hl, IHl; lia].
    rewrite bval_app, Hl, Nat2Z.inj_add, Nat2Z.inj_mul, pow2Z, pw2_2t, pw4_add, bvalZ.
    assert (E2 : (pw4 sh * ((c + a) / pw4 sh + pV l) =
                  pw4 sh * (Z.of_nat (bval ws) + pw4 (pSh l) * c1'))%Z)
      by (rewrite IHv; reflexivity).
    lia.
Qed.

(** Segments: [SL], [SC] are a literal run and a cycle given by one number each; [SP], [SK]
    are the same given round by round. *)
Inductive seg :=
| SL (a : Z) (sh : nat)
| SC (a : Z) (d : nat) (q : nat)
| SP (l : list (Z * nat))
| SK (l : list (Z * nat)) (q : nat).

Fixpoint segV (l : list seg) : Z :=
  match l with
  | [] => 0%Z
  | SL a sh :: r => (a + pw4 sh * segV r)%Z
  | SC a d q :: r => (a * geo (pw4 d) q + pw4 (q * d) * segV r)%Z
  | SP l0 :: r => (pV l0 + pw4 (pSh l0) * segV r)%Z
  | SK l0 q :: r => (pV l0 * geo (pw4 (pSh l0)) q + pw4 (q * pSh l0) * segV r)%Z
  end.

Fixpoint segSh (l : list seg) : nat :=
  match l with
  | [] => O
  | SL _ sh :: r => sh + segSh r
  | SC _ d q :: r => q * d + segSh r
  | SP l0 :: r => pSh l0 + segSh r
  | SK l0 q :: r => q * pSh l0 + segSh r
  end.

(** The carry chain over a repeated block. *)
Lemma carry_rp : forall wl (a c : Z) d, length wl = 2 * d ->
  (Z.of_nat (bval wl) = c + a - pw4 d * c)%Z ->
  forall q, (c + a * geo (pw4 d) q = Z.of_nat (bval (rp wl q)) + pw4 (q * d) * c)%Z.
Proof.
  intros wl a c d Hl Hw. induction q as [| q IH].
  - cbn [geo]. change (rp wl O) with (@nil bool). change (pw4 (O * d)) with 1%Z.
    change (Z.of_nat (bval [])) with 0%Z. ring.
  - rewrite rp_S, bval_app, Hl. cbn [geo].
    change (S q * d)%nat with (d + q * d)%nat. rewrite pw4_add.
    rewrite Nat2Z.inj_add, Nat2Z.inj_mul, pow2Z, pw2_2t.
    assert (E : (pw4 d * (c + a * geo (pw4 d) q) =
                 pw4 d * (Z.of_nat (bval (rp wl q)) + pw4 (q * d) * c))%Z) by (rewrite IH; reflexivity).
    lia.
Qed.

Fixpoint asm (c : Z) (l : list seg) : option (list blk * Z) :=
  match l with
  | [] => Some ([], c)
  | SL a sh :: r =>
    if (Z.of_N (bvalN (zbits (c + a) (2 * sh))) + pw4 sh * ((c + a) / pw4 sh) =? c + a)%Z
       && (length (zbits (c + a) (2 * sh)) =? 2 * sh)%nat then
      match asm ((c + a) / pw4 sh)%Z r with
      | Some (bs, c') => Some (Lit (zbits (c + a) (2 * sh)) :: bs, c')
      | None => None
      end
    else None
  | SC a d q :: r =>
    if (Z.of_N (bvalN (zbits (c + a - pw4 d * c) (2 * d))) =? c + a - pw4 d * c)%Z
       && (length (zbits (c + a - pw4 d * c) (2 * d)) =? 2 * d)%nat then
      match asm c r with
      | Some (bs, c') => Some (Rep (zbits (c + a - pw4 d * c) (2 * d)) q :: bs, c')
      | None => None
      end
    else None
  | SP l0 :: r =>
    match pasm c l0 with
    | Some (w, c1) =>
      match asm c1 r with
      | Some (bs, c') => Some (Lit w :: bs, c')
      | None => None
      end
    | None => None
    end
  | SK l0 q :: r =>
    match pasm c l0 with
    | Some (w, c1) =>
      if (c1 =? c)%Z then
        match asm c r with
        | Some (bs, c') => Some (Rep w q :: bs, c')
        | None => None
        end
      else None
    | None => None
    end
  end.

Lemma asm_SP : forall c l0 r,
  asm c (SP l0 :: r) =
  match pasm c l0 with
  | Some (w, c1) =>
    match asm c1 r with
    | Some (bs, c') => Some (Lit w :: bs, c')
    | None => None
    end
  | None => None
  end.
Proof. reflexivity. Qed.

Lemma asm_SK : forall c l0 q r,
  asm c (SK l0 q :: r) =
  match pasm c l0 with
  | Some (w, c1) =>
    if (c1 =? c)%Z then
      match asm c r with
      | Some (bs, c') => Some (Rep w q :: bs, c')
      | None => None
      end
    else None
  | None => None
  end.
Proof. reflexivity. Qed.

Lemma asm_SL : forall c a sh r,
  asm c (SL a sh :: r) =
  if (Z.of_N (bvalN (zbits (c + a) (2 * sh))) + pw4 sh * ((c + a) / pw4 sh) =? c + a)%Z
     && (length (zbits (c + a) (2 * sh)) =? 2 * sh)%nat then
    match asm ((c + a) / pw4 sh)%Z r with
    | Some (bs, c') => Some (Lit (zbits (c + a) (2 * sh)) :: bs, c')
    | None => None
    end
  else None.
Proof. reflexivity. Qed.

Lemma asm_SC : forall c a d q r,
  asm c (SC a d q :: r) =
  if (Z.of_N (bvalN (zbits (c + a - pw4 d * c) (2 * d))) =? c + a - pw4 d * c)%Z
     && (length (zbits (c + a - pw4 d * c) (2 * d)) =? 2 * d)%nat then
    match asm c r with
    | Some (bs, c') => Some (Rep (zbits (c + a - pw4 d * c) (2 * d)) q :: bs, c')
    | None => None
    end
  else None.
Proof. reflexivity. Qed.

Lemma asm_sound : forall l c bs c', asm c l = Some (bs, c') ->
  (c + segV l = Z.of_nat (bval (den bs)) + pw4 (segSh l) * c')%Z /\
  length (den bs) = 2 * segSh l.
Proof.
  induction l as [| s l IH]; intros c bs c' H.
  - injection H as <- <-. split; [| reflexivity].
    change (segV []) with 0%Z. change (pw4 (segSh [])) with 1%Z.
    change (Z.of_nat (bval (den []))) with 0%Z. ring.
  - destruct s as [a sh | a d q | l0 | l0 q].
    + rewrite asm_SL in H. remember (zbits (c + a) (2 * sh)) as X eqn:EX.
      match type of H with (if ?cnd then _ else _) = _ => destruct cnd eqn:Hc; [| discriminate] end.
      destruct (asm ((c + a) / pw4 sh)%Z l) as [[bs1 c1'] |] eqn:E; [| discriminate].
      injection H as <- <-. apply andb_prop in Hc. destruct Hc as [Hv Hl].
      apply Z.eqb_eq in Hv. apply Nat.eqb_eq in Hl.
      destruct (IH _ _ _ E) as [IHv IHl].
      cbn [den bden segV segSh].
      split; [| rewrite length_app, Hl, IHl; lia].
      rewrite bval_app, Hl, Nat2Z.inj_add, Nat2Z.inj_mul, pow2Z, pw2_2t, pw4_add, bvalZ.
      assert (E2 : (pw4 sh * ((c + a) / pw4 sh + segV l) =
                    pw4 sh * (Z.of_nat (bval (den bs1)) + pw4 (segSh l) * c1'))%Z)
        by (rewrite IHv; reflexivity).
      lia.
    + rewrite asm_SC in H. remember (zbits (c + a - pw4 d * c) (2 * d)) as X eqn:EX.
      match type of H with (if ?cnd then _ else _) = _ => destruct cnd eqn:Hc; [| discriminate] end.
      destruct (asm c l) as [[bs1 c1'] |] eqn:E; [| discriminate].
      injection H as <- <-. apply andb_prop in Hc. destruct Hc as [Hv Hl].
      apply Z.eqb_eq in Hv. apply Nat.eqb_eq in Hl.
      destruct (IH _ _ _ E) as [IHv IHl].
      cbn [den bden segV segSh].
      rewrite <- bvalZ in Hv.
      pose proof (carry_rp _ a c d Hl Hv q) as Hq.
      split; [| rewrite length_app, length_rp, Hl, IHl; lia].
      rewrite bval_app, length_rp, Hl.
      replace (q * (2 * d))%nat with (2 * (q * d))%nat by lia.
      rewrite Nat2Z.inj_add, Nat2Z.inj_mul, pow2Z, pw2_2t, pw4_add.
      assert (E2 : (pw4 (q * d) * (c + segV l) =
                    pw4 (q * d) * (Z.of_nat (bval (den bs1)) + pw4 (segSh l) * c1'))%Z)
        by (rewrite IHv; reflexivity).
      lia.
    + rewrite asm_SP in H.
      destruct (pasm c l0) as [[w c1] |] eqn:Ep; [| discriminate].
      destruct (asm c1 l) as [[bs1 c1'] |] eqn:E; [| discriminate].
      injection H as <- <-.
      destruct (pasm_sound _ _ _ _ Ep) as [Pv Pl]. destruct (IH _ _ _ E) as [IHv IHl].
      cbn [den bden segV segSh].
      split; [| rewrite length_app, Pl, IHl; lia].
      rewrite bval_app, Pl, Nat2Z.inj_add, Nat2Z.inj_mul, pow2Z, pw2_2t, pw4_add.
      assert (E2 : (pw4 (pSh l0) * (c1 + segV l) =
                    pw4 (pSh l0) * (Z.of_nat (bval (den bs1)) + pw4 (segSh l) * c1'))%Z)
        by (rewrite IHv; reflexivity).
      lia.
    + rewrite asm_SK in H.
      destruct (pasm c l0) as [[w c1] |] eqn:Ep; [| discriminate].
      destruct (c1 =? c)%Z eqn:Hc; [| discriminate]. apply Z.eqb_eq in Hc. subst c1.
      destruct (asm c l) as [[bs1 c1'] |] eqn:E; [| discriminate].
      injection H as <- <-.
      destruct (pasm_sound _ _ _ _ Ep) as [Pv Pl]. destruct (IH _ _ _ E) as [IHv IHl].
      assert (Hw : (Z.of_nat (bval w) = c + pV l0 - pw4 (pSh l0) * c)%Z) by lia.
      pose proof (carry_rp _ (pV l0) c (pSh l0) Pl Hw q) as Hq.
      cbn [den bden segV segSh].
      split; [| rewrite length_app, length_rp, Pl, IHl; lia].
      rewrite bval_app, length_rp, Pl.
      replace (q * (2 * pSh l0))%nat with (2 * (q * pSh l0))%nat by lia.
      rewrite Nat2Z.inj_add, Nat2Z.inj_mul, pow2Z, pw2_2t, pw4_add.
      assert (E2 : (pw4 (q * pSh l0) * (c + segV l) =
                    pw4 (q * pSh l0) * (Z.of_nat (bval (den bs1)) + pw4 (segSh l) * c1'))%Z)
        by (rewrite IHv; reflexivity).
      lia.
Qed.

(** Runs composed along a list of segments. *)
Lemma run_end : forall st, Run st [] st (segSh []) (segV []).
Proof. exact run_nil. Qed.

Lemma run_SL : forall st F st1 a sh F' st2 segs,
  Run st F st1 sh a -> Run st1 F' st2 (segSh segs) (segV segs) ->
  Run st (F ++ F') st2 (segSh (SL a sh :: segs)) (segV (SL a sh :: segs)).
Proof. intros st F st1 a sh F' st2 segs H1 H2. exact (run_comp _ _ _ _ _ _ _ _ _ H1 H2). Qed.

Lemma run_SC : forall st F a d q F' st2 segs,
  Run st F st d a -> Run st F' st2 (segSh segs) (segV segs) ->
  Run st (rp F q ++ F') st2 (segSh (SC a d q :: segs)) (segV (SC a d q :: segs)).
Proof.
  intros st F a d q F' st2 segs H1 H2.
  exact (run_comp _ _ _ _ _ _ _ _ _ (run_iter _ _ _ _ H1 q) H2).
Qed.

Lemma run_SP : forall st F st1 l0 F' st2 segs,
  Run st F st1 (pSh l0) (pV l0) -> Run st1 F' st2 (segSh segs) (segV segs) ->
  Run st (F ++ F') st2 (segSh (SP l0 :: segs)) (segV (SP l0 :: segs)).
Proof. intros st F st1 l0 F' st2 segs H1 H2. exact (run_comp _ _ _ _ _ _ _ _ _ H1 H2). Qed.

Lemma run_SK : forall st F l0 q F' st2 segs,
  Run st F st (pSh l0) (pV l0) -> Run st F' st2 (segSh segs) (segV segs) ->
  Run st (rp F q ++ F') st2 (segSh (SK l0 q :: segs)) (segV (SK l0 q :: segs)).
Proof.
  intros st F l0 q F' st2 segs H1 H2.
  exact (run_comp _ _ _ _ _ _ _ _ _ (run_iter _ _ _ _ H1 q) H2).
Qed.

(** ** Runs in rounds

    The evaluator is run [per] steps at a time; after each round the ones in front of the
    state go into the hidden width, and the round contributes one pair [(a, sh)].  The state
    stays short and the numbers stay small, so the cost is linear in the cells read. *)

Fixpoint leadx (x : bool) (l : list bool) : nat :=
  match l with y :: l' => if Bool.eqb x y then S (leadx x l') else O | [] => O end.

Lemma leadx_split : forall x n l, n <= leadx x l -> l = repeat x n ++ skipn n l.
Proof.
  intros x. induction n as [| n IH]; intros l H; [reflexivity |].
  destruct l as [| y l]; [cbn [leadx] in H; lia |].
  cbn [leadx] in H. destruct (Bool.eqb x y) eqn:E; [| lia].
  apply Bool.eqb_prop in E. subst y. cbn [repeat skipn app]. f_equal. apply IH. lia.
Qed.

Definition stripn (x : bool) (post : list bool) : nat := leadx x post / 3.

Definition strip (st : sst) : sst :=
  match st with (pre, x, post) => (pre, x, skipn (3 * stripn x post) post) end.

Definition stripsh (st : sst) : nat :=
  match st with (pre, x, post) => stripn x post end.

Lemma strip_spec : forall st t, conc t st = conc (t + stripsh st) (strip st).
Proof.
  intros [[pre x] post] t. cbv [strip stripsh].
  assert (Hl : 3 * stripn x post <= leadx x post) by (unfold stripn; apply Nat.mul_div_le; lia).
  rewrite <- conc_shift, <- (leadx_split x (3 * stripn x post) post Hl). reflexivity.
Qed.

Fixpoint crun (chunks per : nat) (st : sst) : option (sst * list (Z * nat)) :=
  match chunks with
  | O => Some (st, [])
  | S c =>
    match grun false per st 0 0 with
    | (s1, a, b) =>
      if (b =? 0)%Z then
        match crun c per (strip s1) with
        | Some (s3, l) => Some (s3, (a, stripsh s1) :: l)
        | None => None
        end
      else None
    end
  end.

Lemma crun_sound : forall chunks per st st' l,
  crun chunks per st = Some (st', l) -> Run st [] st' (pSh l) (pV l).
Proof.
  induction chunks as [| c IH]; intros per st st' l H.
  - injection H as <- <-. exact (run_nil st).
  - cbn [crun] in H. destruct (grun false per st 0 0) as [[s1 a] b] eqn:E.
    destruct (b =? 0)%Z eqn:Hb; [| discriminate]. apply Z.eqb_eq in Hb. subst b.
    destruct (crun c per (strip s1)) as [[s3 l1] |] eqn:E1; [| discriminate].
    injection H as <- <-.
    assert (R1 : Run st [] (strip s1) (stripsh s1) a).
    { intros t R k. assert (HR : false = true -> R = []) by discriminate.
      destruct (grun_sound false per st 0 0 _ _ _ E R HR t k) as [m [k' [Em D]]]. cbv beta in Em.
      exists m, k'. split; [| lia]. rewrite <- (strip_spec s1 t). exact Em. }
    exact (run_comp _ _ _ _ _ _ _ _ _ R1 (IH _ _ _ _ E1)).
Qed.

Lemma run_addpost : forall st F st' sh a, Run (addpost st F) [] st' sh a -> Run st F st' sh a.
Proof.
  intros st F st' sh a H t R k. destruct (H t R k) as [n [k' [E D]]].
  exists n, k'. split; [| exact D]. rewrite conc_addpost, <- app_assoc in E. exact E.
Qed.

Lemma crun_run : forall chunks per st F st' l,
  crun chunks per (addpost st F) = Some (st', l) -> Run st F st' (pSh l) (pV l).
Proof. intros chunks per st F st' l H. exact (run_addpost _ _ _ _ _ (crun_sound _ _ _ _ _ H)). Qed.

(** A run checked by a boolean computation. *)
Definition sst_eqb (s1 s2 : sst) : bool :=
  let '(p1, x1, q1) := s1 in let '(p2, x2, q2) := s2 in leqb p1 p2 && Bool.eqb x1 x2 && leqb q1 q2.

Lemma sst_eqb_eq : forall s1 s2, sst_eqb s1 s2 = true -> s1 = s2.
Proof.
  intros [[p1 x1] q1] [[p2 x2] q2] H. unfold sst_eqb in H.
  apply andb_prop in H. destruct H as [H H3]. apply andb_prop in H. destruct H as [H1 H2].
  apply leqb_eq in H1. apply leqb_eq in H3. apply Bool.eqb_prop in H2. subst. reflexivity.
Qed.

Definition runck (n : nat) (st : sst) (F : list bool) (st' : sst) (sh : nat) (a : Z) : bool :=
  let '(pre', x', post') := st' in
  let '(s, a', b') := grun false n (addpost st F) 0 0 in
  sst_eqb s (pre', x', repeat x' (3 * sh) ++ post') && (a' =? a)%Z && (b' =? 0)%Z.

Lemma runck_sound : forall n st F st' sh a, runck n st F st' sh a = true -> Run st F st' sh a.
Proof.
  intros n st F [[pre' x'] post'] sh a H. unfold runck in H.
  destruct (grun false n (addpost st F) 0 0) as [[s a'] b'] eqn:E.
  apply andb_prop in H. destruct H as [H H3]. apply andb_prop in H. destruct H as [H1 H2].
  apply sst_eqb_eq in H1. apply Z.eqb_eq in H2. apply Z.eqb_eq in H3. subst.
  exact (run_cert n st F pre' x' post' sh a E).
Qed.

(** ** The end phase from runs *)

Theorem stageA : forall st0 F st1 segs fuel Fw ae z1 z2 w' bs c' ab la (top : Z),
  Run st0 F st1 (segSh segs) (segV segs) ->
  endcert fuel (addpost st1 Fw) = Some (ae, z1, z2, w') ->
  asm 0 segs = Some (bs, c') -> (0 <= c')%Z ->
  (Z.of_N (bvalN ab) + top * pw4 la = c' + ae)%Z -> length ab = 2 * la -> z1 + z2 = 3 * la + 1 ->
  length (den bs ++ ab) = 2 * (segSh segs + la) /\
  forall t k, (1 <= k)%nat -> exists n M',
    tickN 3 n (rep10 k ++ conc t st0 ++ F ++ Fw) =
      Some (Slev M' (3 * (t + (segSh segs + la)) + 1) w') /\
    Z.of_nat M' = (Z.of_nat k +
                   (Z.of_nat (bval (den bs ++ ab)) + top * pw4 (segSh segs + la)) * pw4 t)%Z.
Proof.
  intros st0 F st1 segs fuel Fw ae z1 z2 w' bs c' ab la top HR He Ha Hc Hab Hlab Hz.
  destruct (asm_sound _ _ _ _ Ha) as [HV HL].
  split; [rewrite length_app, HL, Hlab; lia |].
  intros t k Hk.
  destruct (HR t Fw k) as [n1 [k1 [E1 D1]]].
  pose proof (pw4_pos (segSh segs)) as Hp1. pose proof (pw4_pos t) as Hp2.
  assert (HV0 : (0 <= segV segs)%Z).
  { assert (0 <= pw4 (segSh segs) * c')%Z by (apply Z.mul_nonneg_nonneg; lia). lia. }
  assert (HV1 : (0 <= segV segs * pw4 t)%Z) by (apply Z.mul_nonneg_nonneg; lia).
  assert (Hk1 : (1 <= k1)%nat) by lia.
  destruct (endcert_sound _ _ _ _ _ _ He (t + segSh segs) k1 Hk1) as [n2 [M' [E2 D2]]].
  rewrite conc_addpost in E2.
  exists (n1 + n2), M'. split.
  - apply (tickN_comp 3 n1 n2 _ _ _ E1).
    replace (3 * (t + (segSh segs + la)) + 1) with (z1 + 3 * (t + segSh segs) + z2) by lia.
    rewrite <- ?app_assoc in E2. exact E2.
  - rewrite bval_app, HL, Nat2Z.inj_add, Nat2Z.inj_mul, pow2Z, pw2_2t, (bvalZ ab), pw4_add.
    rewrite pw4_add in D2.
    assert (E3 : (pw4 t * (0 + segV segs) =
                  pw4 t * (Z.of_nat (bval (den bs)) + pw4 (segSh segs) * c'))%Z)
      by (rewrite HV; reflexivity).
    assert (E4 : (pw4 t * pw4 (segSh segs) * (Z.of_N (bvalN ab) + top * pw4 la) =
                  pw4 t * pw4 (segSh segs) * (c' + ae))%Z) by (rewrite Hab; reflexivity).
    lia.
Qed.

(** ** The division with a top digit

    The total of an end phase can exceed its [2 * lc] bits by a digit [top < 3]; the division
    by 3 then starts from the remainder [top]. *)

Theorem stageB_top : forall h Cc (top : N) b' r M',
  (2 <= h)%nat -> (top < 3)%N ->
  dm 3 ([false; false; true; false] ++ rep01 (h - 2) ++ Cc) top = (b', r) ->
  (3 * Z.of_nat M' + 2 = 2 * pw4 h +
     3 * (pw4 h * (Z.of_nat (bval Cc) + Z.of_N top * 2 ^ Z.of_nat (length Cc))))%Z ->
  M' = (3 + N.to_nat r) + 3 * bval b' + 3 /\ length b' = 2 * h + length Cc /\ (r < 3)%N.
Proof.
  intros h Cc top b' r M' Hh Ht Hd HM.
  destruct (dm_spec 3 _ top b' r Ht Hd) as [He [Hlen Hr]].
  pose proof (bval_Zl h Cc Hh) as Hn.
  assert (HL : length ([false; false; true; false] ++ rep01 (h - 2) ++ Cc) = 2 * h + length Cc)
    by (rewrite !length_app, length_rep01; cbn [length]; lia).
  rewrite HL in He. rewrite Nat2Z.inj_add, Z.pow_add_r, pw2_2t in He by lia.
  assert (Hp : Z.of_nat (2 ^ (2 * h)) = pw4 h) by (rewrite pow2Z, pw2_2t; reflexivity).
  remember (2 ^ (2 * h))%nat as X eqn:EX in *. clear EX.
  apply (f_equal Z.of_nat) in Hn.
  repeat first [rewrite Nat2Z.inj_add in Hn | rewrite Nat2Z.inj_mul in Hn].
  rewrite Hp in Hn.
  remember (2 ^ Z.of_nat (length Cc))%Z as Y eqn:EY. clear EY.
  split; [| split; [| exact Hr]].
  - lia.
  - rewrite Hlen, HL. reflexivity.
Qed.

Theorem level_next_top : forall je b u w Cc lc (top : N) b' r w',
  Lvl je b u w -> length Cc = 2 * lc -> (top < 3)%N ->
  (forall k, (1 <= k)%nat -> exists n M',
     tickN 3 n (rep10 k ++ c1101 ++ repeat true (3 * (2 + 2 * bval b)) ++ rep10 je ++ c1101 ++
                encb false b ++ w) =
       Some (Slev M' (3 * (2 + 2 * bval b + lc) + 1) w') /\
     Z.of_nat M' = (Z.of_nat k +
                    (Z.of_nat (bval Cc) + Z.of_N top * pw4 lc) * pw4 (2 + 2 * bval b))%Z) ->
  dm 3 ([false; false; true; false] ++ rep01 (2 * bval b) ++ Cc) top = (b', r) ->
  Lvl (3 + N.to_nat r) b' (2 + 2 * bval b + lc) w'.
Proof.
  intros je b u w Cc lc top b' r w' [Hl [n0 H0]] HC Ht Hend Hd.
  destruct (level_step je (bval b) u w b _ w' _ eq_refl Hl Hend) as [n [M' [E D]]].
  assert (Hd' : dm 3 ([false; false; true; false] ++ rep01 (2 + 2 * bval b - 2) ++ Cc) top = (b', r)).
  { replace (2 + 2 * bval b - 2) with (2 * bval b) by lia. exact Hd. }
  assert (HMz : (3 * Z.of_nat M' + 2 = 2 * pw4 (2 + 2 * bval b) +
                 3 * (pw4 (2 + 2 * bval b) *
                      (Z.of_nat (bval Cc) + Z.of_N top * 2 ^ Z.of_nat (length Cc))))%Z)
    by (rewrite D, HC, pw2_2t; ring).
  assert (H2 : (2 <= 2 + 2 * bval b)%nat) by lia.
  destruct (stageB_top (2 + 2 * bval b) Cc top b' r M' H2 Ht Hd' HMz) as [HM [Hlen Hr]].
  split; [rewrite Hlen, HC; lia |].
  exists (n0 + n). apply (tickN_comp 3 n0 n _ _ _ H0). rewrite <- HM. exact E.
Qed.

(** ** Words with repeated blocks, as cells and re-cut *)

Lemma encb_rp : forall P o, par o P = o ->
  forall q l, encb o (rp P q ++ l) = rp (encb o P) q ++ encb o l.
Proof.
  intros P o Hp. induction q as [| q IH]; intro l; [reflexivity |].
  rewrite !rp_S, <- !app_assoc, (encb_app P), Hp, IH. reflexivity.
Qed.

Lemma rp_rot : forall (u v : list bool) n, rp (u ++ v) n ++ u = u ++ rp (v ++ u) n.
Proof.
  intros u v. induction n as [| n IH]; [cbn [rp repeat concat app]; rewrite app_nil_r; reflexivity |].
  rewrite !rp_S, <- !app_assoc, IH. reflexivity.
Qed.

(** A repeated block re-cut at another phase: [c0] copies and [u0] go to the left, the rest of
    [a'] copies to the right. *)
Lemma rp_recut : forall P u0 v0 n c0 a' V',
  P = u0 ++ v0 -> rp P a' = u0 ++ V' ->
  rp P (c0 + n + a') = (rp P c0 ++ u0) ++ rp (v0 ++ u0) n ++ V'.
Proof.
  intros P u0 v0 n c0 a' V' HP Ha. rewrite !rp_add, Ha. subst P.
  rewrite <- !app_assoc. f_equal. rewrite (app_assoc (rp (u0 ++ v0) n)), rp_rot, <- app_assoc.
  reflexivity.
Qed.

End Run694.

Module Res694.

(** * 1RB1LB_1RC0RD_0LA1RE_0RF1LC_1LA0RB_---1LC: residues of block words

    Proved once, used by every level that needs a count modulo a power of 3:

    - [bval_rp]: the value of [rp P q] as a geometric sum, [bval_rp_closed] in closed form;
    - [pow_order], [pow_mod_order]: [X^o = 1 (mod m)] makes [X^e (mod m)] depend on [e mod o] only;
      [pow4_ord]: [4^(3^j) = 1 (mod 3^(j+1))], hence [pow4_mod3], [pow2_mod3], [pw4_mod3];
    - [resW]: an evaluator of [bval (den bs) mod m] in [Z], linear in the literal and period
      bits, that takes every count only through its residue modulo a period [o] of that block,
      and [resW_sound]: its result is the value of the word modulo [m].

    A level file states a residue of a word as [resW m rbs = Some v] (by [vm_compute]) and the
    congruences of the counts (by [lia]), and gets [Z.of_nat (bval (den bs)) mod m = v]. *)

Import Individual62.
Import T694_levels End694 Sym694 Lev694 Lvl1_694 Eng694 Cert694.
Import Lia Arith PeanoNat Bool NArith ZArith.
Import Coq.Lists.List.
Import ListNotations.

Local Open Scope Z_scope.

(** ** Congruences *)

Lemma cg_add : forall m a a' b b', m <> 0 -> a mod m = a' mod m -> b mod m = b' mod m ->
  (a + b) mod m = (a' + b') mod m.
Proof. intros m a a' b b' Hm Ha Hb. rewrite Z.add_mod, Ha, Hb, <- Z.add_mod by exact Hm. reflexivity. Qed.

Lemma cg_mul : forall m a a' b b', m <> 0 -> a mod m = a' mod m -> b mod m = b' mod m ->
  (a * b) mod m = (a' * b') mod m.
Proof. intros m a a' b b' Hm Ha Hb. rewrite Z.mul_mod, Ha, Hb, <- Z.mul_mod by exact Hm. reflexivity. Qed.

Lemma cg_mod : forall m a, m <> 0 -> (a mod m) mod m = a mod m.
Proof. intros m a Hm. apply Z.mod_mod. exact Hm. Qed.

Lemma cg_pow : forall m x x' (n : nat), m <> 0 -> x mod m = x' mod m ->
  (x ^ Z.of_nat n) mod m = (x' ^ Z.of_nat n) mod m.
Proof.
  intros m x x' n Hm Hx. induction n as [| n IH]; [reflexivity |].
  rewrite Nat2Z.inj_succ, !Z.pow_succ_r by lia. exact (cg_mul m _ _ _ _ Hm Hx IH).
Qed.

(** ** The value of a repeated block *)

Fixpoint geoZ (x : Z) (q : nat) : Z :=
  match q with O => 0 | S q' => 1 + x * geoZ x q' end.

Lemma geoZ_add : forall x a b, geoZ x (a + b) = geoZ x a + x ^ Z.of_nat a * geoZ x b.
Proof.
  intros x a b. induction a as [| a IH].
  - cbn [geoZ Nat.add]. change (Z.of_nat 0) with 0. rewrite Z.pow_0_r. ring.
  - cbn [geoZ Nat.add]. rewrite IH, Nat2Z.inj_succ, Z.pow_succ_r by lia. ring.
Qed.

Lemma geoZ_closed : forall x q, (x - 1) * geoZ x q = x ^ Z.of_nat q - 1.
Proof.
  intros x q. induction q as [| q IH].
  - cbn [geoZ]. change (Z.of_nat 0) with 0. rewrite Z.pow_0_r. ring.
  - cbn [geoZ]. rewrite Nat2Z.inj_succ, Z.pow_succ_r by lia.
    replace ((x - 1) * (1 + x * geoZ x q)) with ((x - 1) + x * ((x - 1) * geoZ x q)) by ring.
    rewrite IH. ring.
Qed.

Lemma geoZ_mul : forall x o a, geoZ x (o * a) = geoZ x o * geoZ (x ^ Z.of_nat o) a.
Proof.
  intros x o a. induction a as [| a IH].
  - rewrite Nat.mul_0_r. cbn [geoZ]. ring.
  - replace (o * S a)%nat with (o + o * a)%nat by lia.
    rewrite geoZ_add, IH. cbn [geoZ]. ring.
Qed.

Lemma geoZ_cong : forall m x x' q, m <> 0 -> x mod m = x' mod m -> geoZ x q mod m = geoZ x' q mod m.
Proof.
  intros m x x' q Hm Hx. induction q as [| q IH]; [reflexivity |].
  cbn [geoZ]. apply cg_add; [exact Hm | reflexivity |]. exact (cg_mul m _ _ _ _ Hm Hx IH).
Qed.

Theorem bval_rp : forall P q,
  Z.of_nat (bval (rp P q)) = Z.of_nat (bval P) * geoZ (2 ^ Z.of_nat (length P)) q.
Proof.
  intros P q. induction q as [| q IH].
  - cbn [geoZ]. change (rp P 0) with (@nil bool). cbn [bval]. ring.
  - rewrite rp_S, bval_app, Nat2Z.inj_add, Nat2Z.inj_mul, pow2Z, IH. cbn [geoZ]. ring.
Qed.

Lemma pow_nat_mul : forall x (a b : nat), x ^ Z.of_nat (a * b) = (x ^ Z.of_nat a) ^ Z.of_nat b.
Proof. intros x a b. rewrite Nat2Z.inj_mul, Z.pow_mul_r by lia. reflexivity. Qed.

Theorem bval_rp_closed : forall P q,
  (2 ^ Z.of_nat (length P) - 1) * Z.of_nat (bval (rp P q)) =
  Z.of_nat (bval P) * (2 ^ Z.of_nat (length P * q) - 1).
Proof.
  intros P q. rewrite bval_rp, pow_nat_mul.
  rewrite <- (geoZ_closed (2 ^ Z.of_nat (length P)) q). ring.
Qed.

Lemma length_rp_pow : forall P q,
  2 ^ Z.of_nat (length (rp P q)) = (2 ^ Z.of_nat (length P)) ^ Z.of_nat q.
Proof. intros P q. rewrite length_rp, Nat.mul_comm, pow_nat_mul. reflexivity. Qed.

(** ** Orders *)

Theorem pow_order : forall X o m (a : nat) b, m <> 0 -> 0 <= o -> 0 <= b ->
  X ^ o mod m = 1 mod m -> X ^ (o * Z.of_nat a + b) mod m = X ^ b mod m.
Proof.
  intros X o m a b Hm Ho Hb H. induction a as [| a IH].
  - rewrite Z.mul_0_r, Z.add_0_l. reflexivity.
  - replace (o * Z.of_nat (S a) + b) with (o + (o * Z.of_nat a + b)) by lia.
    rewrite Z.pow_add_r by lia.
    rewrite (cg_mul m _ 1 _ (X ^ (o * Z.of_nat a + b)) Hm H eq_refl), Z.mul_1_l. exact IH.
Qed.

Theorem pow_mod_order : forall X o m e, m <> 0 -> 0 < o -> 0 <= e ->
  X ^ o mod m = 1 mod m -> X ^ e mod m = X ^ (e mod o) mod m.
Proof.
  intros X o m e Hm Ho He H.
  assert (Hq : 0 <= e / o) by (apply Z.div_pos; lia).
  pose proof (Z.mod_pos_bound e o Ho) as Hr.
  rewrite (Z.div_mod e o) at 1 by lia.
  rewrite <- (Z2Nat.id (e / o)) by exact Hq.
  apply pow_order; lia.
Qed.

(** [a = 1 (mod 3^(j+1))] gives [a^3 = 1 (mod 3^(j+2))]. *)
Lemma cube_lift : forall n a, 1 < n -> a mod n = 1 -> (3 * n) mod 3 = 0 ->
  (n mod 3 = 0) -> (a ^ 3) mod (3 * n) = 1.
Proof.
  intros n a Hn Ha _ H3.
  assert (En : n = 3 * (n / 3)) by (pose proof (Z.div_mod n 3 ltac:(lia)); lia).
  assert (Ea : a = n * (a / n) + 1) by (pose proof (Z.div_mod a n ltac:(lia)); lia).
  set (t := a / n) in *. set (M := n / 3) in *.
  assert (E : a ^ 3 = 1 + (t + n * t ^ 2 + 3 * M * M * t ^ 3) * (3 * n)).
  { rewrite Ea. clearbody t M. subst n. ring. }
  rewrite E, Z_mod_plus_full. apply Z.mod_small. lia.
Qed.

Theorem pow4_ord : forall j : nat, 4 ^ (3 ^ Z.of_nat j) mod 3 ^ (Z.of_nat j + 1) = 1.
Proof.
  induction j as [| j IH]; [reflexivity |].
  rewrite Nat2Z.inj_succ.
  assert (H3j : 0 < 3 ^ Z.of_nat j) by (apply Z.pow_pos_nonneg; lia).
  assert (Hn : 3 <= 3 ^ (Z.of_nat j + 1)).
  { rewrite Z.pow_add_r, Z.pow_1_r by lia. lia. }
  replace (3 ^ Z.succ (Z.of_nat j)) with (3 ^ Z.of_nat j * 3) by (rewrite Z.pow_succ_r by lia; ring).
  rewrite Z.pow_mul_r by lia.
  replace (Z.succ (Z.of_nat j) + 1) with (1 + (Z.of_nat j + 1)) by lia.
  rewrite (Z.pow_add_r 3 1) by lia. rewrite Z.pow_1_r.
  apply cube_lift; [lia | exact IH | | ].
  - rewrite Z.mul_comm, Z_mod_mult. reflexivity.
  - rewrite Z.pow_add_r, Z.pow_1_r by lia. apply Z_mod_mult.
Qed.

Theorem pow4_mod3 : forall (j : nat) h, 0 <= h ->
  4 ^ h mod 3 ^ (Z.of_nat j + 1) = 4 ^ (h mod 3 ^ Z.of_nat j) mod 3 ^ (Z.of_nat j + 1).
Proof.
  intros j h Hh.
  assert (Hm : 0 < 3 ^ (Z.of_nat j + 1)) by (apply Z.pow_pos_nonneg; lia).
  assert (Ho : 0 < 3 ^ Z.of_nat j) by (apply Z.pow_pos_nonneg; lia).
  apply pow_mod_order; [lia | exact Ho | exact Hh |].
  rewrite pow4_ord. symmetry. apply Z.mod_small.
  assert (3 ^ (Z.of_nat j + 1) = 3 * 3 ^ Z.of_nat j) by (rewrite Z.pow_add_r, Z.pow_1_r by lia; ring).
  lia.
Qed.

Theorem pow2_mod3 : forall (j : nat) h, 0 <= h ->
  2 ^ h mod 3 ^ (Z.of_nat j + 1) = 2 ^ (h mod (2 * 3 ^ Z.of_nat j)) mod 3 ^ (Z.of_nat j + 1).
Proof.
  intros j h Hh.
  assert (Hm : 0 < 3 ^ (Z.of_nat j + 1)) by (apply Z.pow_pos_nonneg; lia).
  assert (Ho : 0 < 3 ^ Z.of_nat j) by (apply Z.pow_pos_nonneg; lia).
  apply pow_mod_order; [lia | lia | exact Hh |].
  rewrite Z.pow_mul_r by lia. change (2 ^ 2) with 4. rewrite pow4_ord. symmetry. apply Z.mod_small.
  assert (3 ^ (Z.of_nat j + 1) = 3 * 3 ^ Z.of_nat j) by (rewrite Z.pow_add_r, Z.pow_1_r by lia; ring).
  lia.
Qed.

(** The same for [pw4] (exponent a [nat]). *)
Theorem pw4_mod3 : forall (j h : nat),
  pw4 h mod 3 ^ (Z.of_nat j + 1) = 4 ^ (Z.of_nat h mod 3 ^ Z.of_nat j) mod 3 ^ (Z.of_nat j + 1).
Proof. intros j h. unfold pw4. apply pow4_mod3. lia. Qed.

(** ** The evaluator *)

(** Reduction of [0 <= s < 2m] by one comparison (no division: [Z.modulo] in the VM costs a
    bitwise division per call). *)
Definition csub (m s : Z) : Z := if (m <=? s) then s - m else s.

Lemma csub_spec : forall m s, 0 <= s < 2 * m -> csub m s = s mod m.
Proof.
  intros m s Hs. unfold csub. destruct (m <=? s) eqn:E.
  - apply Z.leb_le in E. replace s with ((s - m) + 1 * m) at 2 by ring.
    rewrite Z_mod_plus_full. symmetry. apply Z.mod_small. lia.
  - apply Z.leb_gt in E. symmetry. apply Z.mod_small. lia.
Qed.

(** Scan of a literal, low bit first: [acc + pw * bval l] and [pw * 2^|l|], modulo [m], for
    [acc] and [pw] already reduced.  Tail recursive, numbers below [2m]. *)
Fixpoint lsc (m : Z) (l : list bool) (acc pw : Z) : Z * Z :=
  match l with
  | [] => (acc, pw)
  | x :: l' => lsc m l' (if x then csub m (acc + pw) else acc) (csub m (2 * pw))
  end.

Lemma lsc_spec : forall m l acc pw, 0 <= acc < m -> 0 <= pw < m ->
  fst (lsc m l acc pw) = (acc + pw * Z.of_nat (bval l)) mod m /\
  snd (lsc m l acc pw) = (pw * 2 ^ Z.of_nat (length l)) mod m.
Proof.
  intros m l. induction l as [| x l IH]; intros acc pw Ha Hp.
  - cbn [lsc fst snd bval length]. change (Z.of_nat 0) with 0. rewrite Z.pow_0_r.
    rewrite Z.mul_0_r, Z.add_0_r, Z.mul_1_r. split; symmetry; apply Z.mod_small; lia.
  - assert (Hm : m <> 0) by lia.
    set (acc1 := if x then csub m (acc + pw) else acc).
    assert (E1 : acc1 = (acc + (if x then pw else 0)) mod m).
    { unfold acc1. destruct x; [apply csub_spec; lia | rewrite Z.add_0_r; symmetry; apply Z.mod_small; lia]. }
    assert (E2 : csub m (2 * pw) = (2 * pw) mod m) by (apply csub_spec; lia).
    assert (B1 : 0 <= acc1 < m) by (rewrite E1; apply Z.mod_pos_bound; lia).
    assert (B2 : 0 <= csub m (2 * pw) < m) by (rewrite E2; apply Z.mod_pos_bound; lia).
    cbn [lsc]. fold acc1. destruct (IH acc1 _ B1 B2) as [H1 H2]. rewrite H1, H2. split.
    + change (bval (x :: l)) with ((if x then 1 else 0) + 2 * bval l)%nat.
      rewrite Nat2Z.inj_add, Nat2Z.inj_mul.
      replace (acc + pw * (Z.of_nat (if x then 1%nat else 0%nat) + Z.of_nat 2 * Z.of_nat (bval l)))
        with ((acc + (if x then pw else 0)) + (2 * pw) * Z.of_nat (bval l))
        by (change (Z.of_nat 2) with 2; destruct x;
            [change (Z.of_nat 1) with 1 | change (Z.of_nat 0) with 0]; ring).
      apply cg_add; [exact Hm | rewrite E1; apply cg_mod; exact Hm |].
      apply cg_mul; [exact Hm | rewrite E2; apply cg_mod; exact Hm | reflexivity].
    + cbn [length]. rewrite Nat2Z.inj_succ, Z.pow_succ_r by lia.
      replace (pw * (2 * 2 ^ Z.of_nat (length l))) with ((2 * pw) * 2 ^ Z.of_nat (length l)) by ring.
      apply cg_mul; [exact Hm | rewrite E2; apply cg_mod; exact Hm | reflexivity].
Qed.

Definition lscan (m : Z) (l : list bool) (acc pw : Z) : Z * Z := lsc m l (acc mod m) (pw mod m).

Lemma lscan_spec : forall m l acc pw, 0 < m ->
  fst (lscan m l acc pw) mod m = (acc + pw * Z.of_nat (bval l)) mod m /\
  snd (lscan m l acc pw) mod m = (pw * 2 ^ Z.of_nat (length l)) mod m.
Proof.
  intros m l acc pw Hm0. assert (Hm : m <> 0) by lia. unfold lscan.
  destruct (lsc_spec m l (acc mod m) (pw mod m) ltac:(apply Z.mod_pos_bound; lia)
              ltac:(apply Z.mod_pos_bound; lia)) as [H1 H2].
  rewrite H1, H2, !Z.mod_mod by exact Hm. split.
  - apply cg_add; [exact Hm | apply cg_mod; exact Hm |].
    apply cg_mul; [exact Hm | apply cg_mod; exact Hm | reflexivity].
  - apply cg_mul; [exact Hm | apply cg_mod; exact Hm | reflexivity].
Qed.

(** [geoZ x n] and [x^n] modulo [m], by the binary digits of [n]. *)
Fixpoint gpp (x m : Z) (p : positive) : Z * Z :=
  match p with
  | xH => (1 mod m, x mod m)
  | xO p' => let (g, y) := gpp x m p' in ((g * (1 + y)) mod m, (y * y) mod m)
  | xI p' => let (g, y) := gpp x m p' in ((1 + x * (g * (1 + y))) mod m, (x * (y * y)) mod m)
  end.

Definition gpN (x m : Z) (n : N) : Z * Z :=
  match n with N0 => (0, 1 mod m) | Npos p => gpp x m p end.

Lemma geoZ_double : forall x n, geoZ x (n + n) = geoZ x n * (1 + x ^ Z.of_nat n).
Proof. intros x n. rewrite geoZ_add. ring. Qed.

Lemma gpp_spec : forall x m p, m <> 0 ->
  fst (gpp x m p) = geoZ x (Pos.to_nat p) mod m /\ snd (gpp x m p) = x ^ Z.pos p mod m.
Proof.
  intros x m p Hm. induction p as [p IH | p IH |].
  - cbn [gpp]. destruct (gpp x m p) as [g y] eqn:E. cbn [fst snd] in *. destruct IH as [Hg Hy].
    rewrite Pos2Nat.inj_xI, Pos2Z.inj_xI. split.
    + replace (S (2 * Pos.to_nat p)) with (S (Pos.to_nat p + Pos.to_nat p)) by lia.
      cbn [geoZ]. rewrite geoZ_double, positive_nat_Z.
      apply cg_add; [exact Hm | reflexivity |]. apply cg_mul; [exact Hm | reflexivity |].
      apply cg_mul; [exact Hm | rewrite Hg; apply cg_mod; exact Hm |].
      apply cg_add; [exact Hm | reflexivity | rewrite Hy; apply cg_mod; exact Hm].
    + replace (2 * Z.pos p + 1) with (Z.succ (Z.pos p + Z.pos p)) by lia.
      rewrite Z.pow_succ_r, Z.pow_add_r by lia. symmetry.
      apply cg_mul; [exact Hm | reflexivity |].
      apply cg_mul; [exact Hm | rewrite Hy; symmetry; apply cg_mod; exact Hm |
                     rewrite Hy; symmetry; apply cg_mod; exact Hm].
  - cbn [gpp]. destruct (gpp x m p) as [g y] eqn:E. cbn [fst snd] in *. destruct IH as [Hg Hy].
    rewrite Pos2Nat.inj_xO, Pos2Z.inj_xO. split.
    + replace (2 * Pos.to_nat p)%nat with (Pos.to_nat p + Pos.to_nat p)%nat by lia.
      rewrite geoZ_double, positive_nat_Z.
      apply cg_mul; [exact Hm | rewrite Hg; apply cg_mod; exact Hm |].
      apply cg_add; [exact Hm | reflexivity | rewrite Hy; apply cg_mod; exact Hm].
    + replace (2 * Z.pos p) with (Z.pos p + Z.pos p) by lia. rewrite Z.pow_add_r by lia. symmetry.
      apply cg_mul; [exact Hm | rewrite Hy; symmetry; apply cg_mod; exact Hm |
                     rewrite Hy; symmetry; apply cg_mod; exact Hm].
  - cbn [gpp fst snd]. rewrite Pos2Nat.inj_1. cbn [geoZ]. rewrite Z.mul_0_r, Z.add_0_r.
    split; [reflexivity | rewrite Z.pow_1_r; reflexivity].
Qed.

Lemma gpN_spec : forall x m n, m <> 0 ->
  fst (gpN x m n) = geoZ x (N.to_nat n) mod m /\ snd (gpN x m n) = x ^ Z.of_N n mod m.
Proof.
  intros x m [| p] Hm.
  - cbn. split; reflexivity.
  - exact (gpp_spec x m p Hm).
Qed.

(** Blocks with the count replaced by a period [o] of the block and the residue [r] of the count. *)
Inductive rblk := RL (l : list bool) | RR (P : list bool) (o r : N).

Inductive mblk : blk -> rblk -> Prop :=
  | mL : forall l, mblk (Lit l) (RL l)
  | mR : forall P q o r, Z.of_nat q mod Z.of_N o = Z.of_N r -> mblk (Rep P q) (RR P o r).

(** A period [o] of a block is checked by [v * geo(x, o) = 0] and [x^o = 1] modulo [m], with
    [v = bval P] and [x = 2^|P|]: then the block and its width modulo [m] depend on [q mod o] only. *)
Fixpoint resB (m : Z) (bs : list rblk) (acc pw : Z) : option (Z * Z) :=
  match bs with
  | [] => Some (acc, pw)
  | RL l :: bs' => let (a, p) := lscan m l acc pw in resB m bs' a p
  | RR P o r :: bs' =>
    let (v, x) := lscan m P 0 1 in
    let (go, xo) := gpN x m o in
    let (gr, xr) := gpN x m r in
    if (0 <? o)%N && ((v * go) mod m =? 0) && (xo =? 1 mod m) then
      resB m bs' ((acc + pw * (v * gr)) mod m) ((pw * xr) mod m)
    else None
  end.

Definition resW (m : Z) (bs : list rblk) : option Z :=
  match resB m bs 0 1 with Some (a, _) => Some (a mod m) | None => None end.

Lemma geo_period : forall m X V (o a r : nat), m <> 0 ->
  (V * geoZ X o) mod m = 0 -> X ^ Z.of_nat o mod m = 1 mod m ->
  (V * geoZ X (o * a + r)) mod m = (V * geoZ X r) mod m /\
  X ^ Z.of_nat (o * a + r) mod m = X ^ Z.of_nat r mod m.
Proof.
  intros m X V o a r Hm Hg Hx.
  assert (Hxa : X ^ Z.of_nat (o * a) mod m = 1 mod m).
  { pose proof (pow_order X (Z.of_nat o) m a 0 Hm ltac:(lia) ltac:(lia) Hx) as H.
    rewrite Z.add_0_r, Z.pow_0_r in H. rewrite Nat2Z.inj_mul. exact H. }
  split.
  - rewrite geoZ_add, geoZ_mul.
    replace (V * (geoZ X o * geoZ (X ^ Z.of_nat o) a + X ^ Z.of_nat (o * a) * geoZ X r))
      with ((V * geoZ X o) * geoZ (X ^ Z.of_nat o) a + X ^ Z.of_nat (o * a) * (V * geoZ X r)) by ring.
    transitivity ((0 * geoZ (X ^ Z.of_nat o) a + 1 * (V * geoZ X r)) mod m).
    + apply cg_add; [exact Hm | |].
      * apply cg_mul; [exact Hm | rewrite Hg; reflexivity | reflexivity].
      * apply cg_mul; [exact Hm | exact Hxa | reflexivity].
    + f_equal. ring.
  - rewrite Nat2Z.inj_add, Z.pow_add_r by lia.
    rewrite <- (Z.mul_1_l (X ^ Z.of_nat r)) at 2.
    apply cg_mul; [exact Hm | exact Hxa | reflexivity].
Qed.

Lemma cnt_split : forall q o r, Z.of_nat q mod Z.of_N o = Z.of_N r -> (0 < o)%N ->
  q = (N.to_nat o * (q / N.to_nat o) + N.to_nat r)%nat.
Proof.
  intros q o r H Ho.
  assert (Hr : N.to_nat r = (q mod N.to_nat o)%nat).
  { apply Nat2Z.inj. rewrite Nat2Z.inj_mod, N_nat_Z, N_nat_Z. symmetry. exact H. }
  rewrite Hr. apply Nat.div_mod_eq.
Qed.

Theorem resB_sound : forall m bs rbs acc pw a p, 0 < m -> Forall2 mblk bs rbs ->
  resB m rbs acc pw = Some (a, p) ->
  a mod m = (acc + pw * Z.of_nat (bval (den bs))) mod m /\
  p mod m = (pw * 2 ^ Z.of_nat (length (den bs))) mod m.
Proof.
  intros m bs rbs acc pw a p Hm0 HF. assert (Hm : m <> 0) by lia.
  revert acc pw. induction HF as [| b rb bs rbs Hb HF IH]; intros acc pw H.
  - cbn [resB] in H. injection H as <- <-. cbn [den bval length].
    change (Z.of_nat 0) with 0. rewrite Z.pow_0_r. split; f_equal; ring.
  - inversion Hb as [l | P q o r Hq]; subst.
    + cbn [resB] in H. destruct (lscan m l acc pw) as [a1 p1] eqn:El.
      destruct (lscan_spec m l acc pw Hm0) as [H1 H2]. rewrite El in H1, H2. cbn [fst snd] in H1, H2.
      destruct (IH a1 p1 H) as [Ha Hp].
      cbn [den bden]. rewrite bval_app, length_app, Nat2Z.inj_add, Nat2Z.inj_mul, pow2Z.
      split.
      * rewrite Ha.
        replace (acc + pw * (Z.of_nat (bval l) + 2 ^ Z.of_nat (length l) * Z.of_nat (bval (den bs))))
          with ((acc + pw * Z.of_nat (bval l)) + (pw * 2 ^ Z.of_nat (length l)) * Z.of_nat (bval (den bs)))
          by ring.
        apply cg_add; [exact Hm | exact H1 |]. apply cg_mul; [exact Hm | exact H2 | reflexivity].
      * rewrite Hp, ?Nat2Z.inj_add, Z.pow_add_r by lia. rewrite Z.mul_assoc.
        apply cg_mul; [exact Hm | exact H2 | reflexivity].
    + cbn [resB] in H. destruct (lscan m P 0 1) as [v x] eqn:El.
      destruct (lscan_spec m P 0 1 Hm0) as [Hv Hx]. rewrite El in Hv, Hx. cbn [fst snd] in Hv, Hx.
      rewrite Z.add_0_l, Z.mul_1_l in Hv. rewrite Z.mul_1_l in Hx.
      destruct (gpN x m o) as [go xo] eqn:Eo. destruct (gpN_spec x m o Hm) as [Hgo Hxo].
      rewrite Eo in Hgo, Hxo. cbn [fst snd] in Hgo, Hxo.
      destruct (gpN x m r) as [gr xr] eqn:Er. destruct (gpN_spec x m r Hm) as [Hgr Hxr].
      rewrite Er in Hgr, Hxr. cbn [fst snd] in Hgr, Hxr.
      destruct ((0 <? o)%N && ((v * go) mod m =? 0) && (xo =? 1 mod m)) eqn:Ec; [| discriminate].
      apply andb_prop in Ec. destruct Ec as [Ec C3]. apply andb_prop in Ec. destruct Ec as [C1 C2].
      apply N.ltb_lt in C1. apply Z.eqb_eq in C2. apply Z.eqb_eq in C3.
      destruct (IH _ _ H) as [Ha Hp].
      set (X := 2 ^ Z.of_nat (length P)) in *. set (V := Z.of_nat (bval P)) in *.
      (* the checks, transported from [x], [v] to [X], [V] *)
      assert (HG : forall n, geoZ x n mod m = geoZ X n mod m)
        by (intro n; apply geoZ_cong; [exact Hm | exact Hx]).
      assert (HP : forall n : nat, x ^ Z.of_nat n mod m = X ^ Z.of_nat n mod m)
        by (intro n; apply cg_pow; [exact Hm | exact Hx]).
      assert (K1 : (V * geoZ X (N.to_nat o)) mod m = 0).
      { rewrite <- C2. symmetry. apply cg_mul; [exact Hm | exact Hv |].
        rewrite Hgo, cg_mod by exact Hm. apply HG. }
      assert (K2 : X ^ Z.of_nat (N.to_nat o) mod m = 1 mod m).
      { rewrite <- HP, N_nat_Z, <- Hxo, <- C3. reflexivity. }
      pose proof (cnt_split q o r Hq C1) as Eq.
      destruct (geo_period m X V (N.to_nat o) (q / N.to_nat o) (N.to_nat r) Hm K1 K2) as [G1 G2].
      rewrite <- Eq in G1, G2.
      cbn [den bden]. rewrite bval_app, length_app, Nat2Z.inj_add, Nat2Z.inj_mul, pow2Z.
      rewrite bval_rp, length_rp_pow. fold X. fold V.
      assert (R1 : (pw * (v * gr)) mod m = (pw * (V * geoZ X q)) mod m).
      { apply cg_mul; [exact Hm | reflexivity |]. rewrite G1.
        apply cg_mul; [exact Hm | exact Hv |].
        rewrite Hgr, cg_mod by exact Hm. apply HG. }
      assert (R2 : (pw * xr) mod m = (pw * X ^ Z.of_nat q) mod m).
      { apply cg_mul; [exact Hm | reflexivity |]. rewrite G2, <- HP, N_nat_Z, Hxr.
        apply cg_mod. exact Hm. }
      split.
      * rewrite Ha.
        replace (acc + pw * (V * geoZ X q + X ^ Z.of_nat q * Z.of_nat (bval (den bs))))
          with ((acc + pw * (V * geoZ X q)) + (pw * X ^ Z.of_nat q) * Z.of_nat (bval (den bs))) by ring.
        apply cg_add; [exact Hm | | apply cg_mul; [exact Hm | | reflexivity]].
        -- rewrite cg_mod by exact Hm. apply cg_add; [exact Hm | reflexivity | exact R1].
        -- rewrite cg_mod by exact Hm. exact R2.
      * rewrite Hp, ?Nat2Z.inj_add, Z.pow_add_r by lia. rewrite ?length_rp_pow. fold X.
        rewrite Z.mul_assoc.
        apply cg_mul; [exact Hm | rewrite cg_mod by exact Hm; exact R2 | reflexivity].
Qed.

Theorem resW_sound : forall m bs rbs v, 0 < m -> Forall2 mblk bs rbs -> resW m rbs = Some v ->
  Z.of_nat (bval (den bs)) mod m = v.
Proof.
  intros m bs rbs v Hm HF H. unfold resW in H.
  destruct (resB m rbs 0 1) as [[a p] |] eqn:E; [| discriminate]. injection H as <-.
  destruct (resB_sound m bs rbs 0 1 a p Hm HF E) as [Ha _]. rewrite Ha. f_equal. ring.
Qed.

(** ** Helpers for the level files *)

(** The smallest power of 3 (up to [3^k]) that is a period of the block [P] modulo [m];
    for [m = 3^j] and [|P|] even, [3^j] is always one. Only used to choose [o]. *)
Definition isper (m : Z) (P : list bool) (o : N) : bool :=
  let (v, x) := lscan m P 0 1 in
  let (go, xo) := gpN x m o in
  ((v * go) mod m =? 0) && (xo =? 1 mod m).

Fixpoint minper (m : Z) (P : list bool) (k : nat) (o : N) : N :=
  match k with
  | O => o
  | S k' => if isper m P o then o else minper m P k' (3 * o)%N
  end.

(** A count given as [a * o + r] with [r < o] in [nat]. *)
Lemma mblk_lin : forall P (a o r : nat), (r < o)%nat ->
  mblk (Rep P (a * o + r)) (RR P (N.of_nat o) (N.of_nat r)).
Proof.
  intros P a o r Hr. constructor. rewrite !nat_N_Z.
  rewrite Nat2Z.inj_add, Nat2Z.inj_mul, Z.add_comm, Z_mod_plus_full. apply Z.mod_small. lia.
Qed.

(** A count that is a literal. *)
Lemma mblk_lit : forall P (n o : N), (0 < o)%N ->
  mblk (Rep P (N.to_nat n)) (RR P o (n mod o)).
Proof.
  intros P n o Ho. constructor. rewrite N_nat_Z, N2Z.inj_mod. reflexivity.
Qed.

End Res694.

Module Gen694.

(** * 1RB1LB_1RC0RD_0LA1RE_0RF1LC_1LA0RB_---1LC: helpers of the generated level files

    Small functions that let a level file choose its own cuts by computation (the rounds of one
    instance, the first round boundary of each block that repeats one period later), and the
    lemmas that the level files share: lower bounds of block words, the complement and the
    length of a block word. *)

Import Individual62.
Import T694_levels End694 Sym694 Lev694 Lvl1_694 Eng694 Cert694 Run694 Res694.
Import Lia Arith PeanoNat Bool NArith ZArith.
Import Coq.Lists.List.
Import ListNotations.

(** [lia] with a closed term replaced by a variable first: on a closed count or a closed
    [bval] the preprocessing of [lia] may try to reduce it. *)
Ltac gl c := repeat match goal with H : _ |- _ => revert H end; generalize c; intros; lia.

Lemma h_pos : forall x, 1 <= 2 + 2 * x.
Proof. intro x. lia. Qed.

(** Value of a [resW] computation as a literal. *)
Definition gv (o : option Z) : Z := match o with Some v => v | None => (-1)%Z end.

(** ** Rounds of an instance *)

(** The state after a number of rounds (one round: four evaluator steps and [strip]). *)
Fixpoint grst (rounds : nat) (st : sst) : sst :=
  match rounds with
  | O => st
  | S c => match grun false 4 st 0 0 with (s1, _, _) => grst c (strip s1) end
  end.

(** Keep [L] cells after the leading ones. *)
Definition gcut (L : nat) (st : sst) : sst :=
  match st with (pre, x, post) => (pre, x, firstn (leadx x post + L) post) end.

Definition grl (rounds : nat) (st : sst) (F : list bool) : list (Z * nat) :=
  match crun rounds 4 (addpost st F) with Some (_, l) => l | None => [] end.

(** The part of a state that [gcut] keeps, as a number. *)
Definition gsig (L : nat) (st : sst) : N :=
  match st with
  | (pre, x, post) =>
    fold_right (fun (y : bool) (acc : N) => (2 * acc + (if y then 1 else 0))%N) 1%N
               (pre ++ x :: firstn (leadx x post + L) post)
  end.

(** [(round, cells eaten, state signature)] after each round, as long as the rounds succeed
    and make progress. *)
Fixpoint gtrace (L fuel : nat) (idx pos last : N) (st : sst) : list (N * N * N) :=
  match fuel with
  | O => []
  | S c =>
    match grun false 4 st 0 0 with
    | (s1, _, b) =>
      if (b =? 0)%Z then
        let s2 := strip s1 in
        let pos' := (pos + 3 * N.of_nat (stripsh s1))%N in
        match s2 with
        | (_, x, post) =>
          let m := (pos' + N.of_nat (leadx x post))%N in
          if (m <=? last)%N then []
          else ((idx + 1)%N, m, gsig L s2) :: gtrace L c (idx + 1)%N pos' m s2
        end
      else []
    end
  end.

(** The first round between [lo] and [hi] cells whose state recurs exactly [p] cells later:
    [(round, cells, rounds per period)]. *)
Fixpoint gfind (p lo hi : N) (tr : list (N * N * N)) : N * N * N :=
  match tr with
  | [] => (0, 0, 0)%N
  | (r, m, g) :: tr' =>
    if (lo <=? m)%N && (m <=? hi)%N then
      match find (fun e => (snd (fst e) =? m + p)%N && (snd e =? g)%N) tr' with
      | Some (r', _, _) => (r, m, (r' - r)%N)
      | None => gfind p lo hi tr'
      end
    else gfind p lo hi tr'
  end.

(** The same for a recurrence after [k] copies, for the first [k] of a list that has one:
    [(round, cells, rounds per k copies, k)].  [hie] is the last admissible position plus
    one period. *)
Fixpoint gfindk (p lo hie : N) (ks : list N) (tr : list (N * N * N)) : N * N * N * N :=
  match ks with
  | [] => (0, 0, 0, 1)%N
  | k :: ks' =>
    let f := gfind (k * p) lo (hie - k * p) tr in
    if (snd f =? 0)%N then gfindk p lo hie ks' tr else (f, k)
  end.

(** The last round at [hi] cells or earlier. *)
Fixpoint glast (hi : N) (tr : list (N * N * N)) (acc : N * N) : N * N :=
  match tr with
  | [] => acc
  | (r, m, _) :: tr' => if (m <=? hi)%N then glast hi tr' (r, m) else acc
  end.

Lemma rp1_split : forall (P : list bool) k, rp P 1 = firstn k P ++ skipn k P.
Proof. intros P k. unfold rp. cbn [repeat concat]. rewrite app_nil_r, firstn_skipn. reflexivity. Qed.

(** ** Lower bounds *)

Lemma bval_app_hi : forall a b, bval b <= bval (a ++ b).
Proof.
  intros a b. rewrite bval_app.
  assert (2 ^ length a <> 0)%nat by (apply Nat.pow_nonzero; lia). nia.
Qed.

Lemma bval_last_ge : forall bs e, bval e <= bval (den (bs ++ [Lit e])).
Proof.
  induction bs as [| x bs IH]; intro e.
  - cbn [app den bden]. rewrite app_nil_r. lia.
  - cbn [app den]. pose proof (bval_app_hi (bden x) (den (bs ++ [Lit e]))) as H.
    specialize (IH e). lia.
Qed.

Lemma lbZ : forall bs e, (Z.of_N (bvalN e) <= Z.of_nat (bval (den (bs ++ [Lit e]))))%Z.
Proof. intros bs e. rewrite <- bvalZ. apply Nat2Z.inj_le. apply bval_last_ge. Qed.

(** ** The low literal of a block word *)

Lemma bval_low : forall a l,
  (Z.of_nat (bval (a ++ l)) mod 2 ^ Z.of_nat (length a) = Z.of_N (bvalN a))%Z.
Proof.
  intros a l. rewrite bval_app, Nat2Z.inj_add, Nat2Z.inj_mul, Nat2Z.inj_pow.
  change (Z.of_nat 2) with 2%Z. rewrite (Z.mul_comm (2 ^ Z.of_nat (length a))), Z_mod_plus_full.
  rewrite <- bvalZ. apply Z.mod_small. pose proof (bval_lt a) as H.
  apply Nat2Z.inj_lt in H. rewrite Nat2Z.inj_pow in H. change (Z.of_nat 2) with 2%Z in H. lia.
Qed.

Lemma bval_low_den : forall a bs,
  (Z.of_nat (bval (den (Lit a :: bs))) mod 2 ^ Z.of_nat (length a) = Z.of_N (bvalN a))%Z.
Proof. intros a bs. cbn [den bden]. apply bval_low. Qed.

(** ** Complement and length of a block word *)

Definition nblk (x : blk) : blk :=
  match x with Lit l => Lit (map negb l) | Rep P q => Rep (map negb P) q end.

Lemma map_rp : forall (f : bool -> bool) P q, map f (rp P q) = rp (map f P) q.
Proof.
  intros f P q. induction q as [| q IH]; [reflexivity |]. rewrite !rp_S, map_app, IH. reflexivity.
Qed.

Lemma negb_den : forall bs, map negb (den bs) = den (map nblk bs).
Proof.
  induction bs as [| x bs IH]; [reflexivity |]. cbn [den map]. rewrite map_app, IH.
  destruct x; cbn [bden nblk]; [reflexivity | rewrite map_rp; reflexivity].
Qed.

Fixpoint hlen (bs : list blk) : nat :=
  match bs with
  | [] => O
  | Lit l :: bs' => Nat.div2 (length l) + hlen bs'
  | Rep P q :: bs' => q * Nat.div2 (length P) + hlen bs'
  end.

Fixpoint evenB (bs : list blk) : bool :=
  match bs with
  | [] => true
  | Lit l :: bs' => Nat.even (length l) && evenB bs'
  | Rep P _ :: bs' => Nat.even (length P) && evenB bs'
  end.

Lemma even_half : forall n, Nat.even n = true -> n = 2 * Nat.div2 n.
Proof.
  intros n E. destruct (Nat.even_spec n) as [H _]. destruct (H E) as [m Hm].
  rewrite Hm, Nat.div2_double. reflexivity.
Qed.

Lemma den_len : forall bs, evenB bs = true -> length (den bs) = 2 * hlen bs.
Proof.
  induction bs as [| x bs IH]; intro E; [reflexivity |].
  destruct x as [l | P q]; cbn [evenB] in E; apply andb_prop in E; destruct E as [E1 E2];
    cbn [den bden hlen]; rewrite length_app, (IH E2).
  - pose proof (even_half _ E1). lia.
  - rewrite length_rp. pose proof (even_half _ E1). nia.
Qed.

End Gen694.

Module L23.

(** * 1RB1LB_1RC0RD_0LA1RE_0RF1LC_1LA0RB_---1LC: from level 2 to level 3

    Level 2 has the 24-bit counter word [b2] (value 4252556) and class 3.  Its end phase is one
    computation ([endcert]); the next counter word is the quotient by 3 of
    [0100 (10)^(h-2) C2], a word with one repeated block, divided block by block ([dmB]). *)

Import Individual62.
Import T694_levels End694 Sym694 Lev694 Lvl1_694 Eng694 Cert694.
Import Lia Arith PeanoNat Bool NArith ZArith.
Import Coq.Lists.List.
Import ListNotations.

Definition b2 : list bool := Eval vm_compute in zbits 4252556 24.

Lemma b2_val : bval b2 = N.to_nat 4252556%N.
Proof. rewrite <- (bvalN_spec b2). change (bvalN b2) with 4252556%N. reflexivity. Qed.

Lemma lvl2 : Lvl 3 b2 12 [true].
Proof.
  split; [reflexivity |]. destruct level1 as [n H]. exists n.
  replace (3 + 3 * bval b2 + 3) with (N.to_nat 12757674%N) by (rewrite b2_val; lia).
  exact H.
Qed.

(** ** The end phase *)

Definition st2 : sst := (c1101, true, rep10 3 ++ c1101 ++ encb false b2 ++ [true]).

Definition ec2 := Eval vm_compute in endcert 3000 st2.

Definition A2 : Z := Eval vm_compute in match ec2 with Some (a, _, _, _) => a | None => 0%Z end.
Definition z1_2 : nat := Eval vm_compute in match ec2 with Some (_, z, _, _) => z | None => O end.
Definition z2_2 : nat := Eval vm_compute in match ec2 with Some (_, _, z, _) => z | None => O end.
Definition w3 : list bool := Eval vm_compute in match ec2 with Some (_, _, _, x) => x | None => [] end.
Definition lc2 : nat := Eval vm_compute in (z1_2 + z2_2 - 1) / 3.
Definition C2 : list bool := Eval vm_compute in zbits A2 (2 * lc2).

Lemma ec2_ok : endcert 3000 st2 = Some (A2, z1_2, z2_2, w3).
Proof. vm_compute. reflexivity. Qed.

Lemma C2_val : Z.of_N (bvalN C2) = A2.
Proof. vm_compute. reflexivity. Qed.

Lemma C2_len : length C2 = 2 * lc2.
Proof. vm_compute. reflexivity. Qed.

Lemma z_2 : z1_2 + z2_2 = 3 * lc2 + 1.
Proof. vm_compute. reflexivity. Qed.

Lemma end2 : forall k, (1 <= k)%nat -> exists n M',
  tickN 3 n (rep10 k ++ c1101 ++ repeat true (3 * (2 + 2 * bval b2)) ++ rep10 3 ++ c1101 ++
             encb false b2 ++ [true]) =
    Some (Slev M' (3 * (2 + 2 * bval b2 + lc2) + 1) w3) /\
  Z.of_nat M' = (Z.of_nat k + Z.of_nat (bval C2) * pw4 (2 + 2 * bval b2))%Z.
Proof.
  intros k Hk.
  destruct (endcert_sound _ _ _ _ _ _ ec2_ok (2 + 2 * bval b2) k Hk) as [n [M' [E D]]].
  unfold st2, conc in E. pose proof z_2 as Hz.
  exists n, M'. split.
  - replace (3 * (2 + 2 * bval b2 + lc2) + 1) with (z1_2 + 3 * (2 + 2 * bval b2) + z2_2) by lia.
    exact E.
  - rewrite D, (bvalZ C2), C2_val. reflexivity.
Qed.

(** ** The division *)

Definition q3 : nat := N.to_nat 2835037%N.

Lemma h2_eq : 2 * bval b2 = q3 * 3 + 1.
Proof. unfold q3. rewrite b2_val. lia. Qed.

Lemma Zl2_den : forall q,
  [false; false; true; false] ++ rep01 (q * 3 + 1) ++ C2 =
  den [Lit [false; false; true; false]; Rep (rp [false; true] 3) q; Lit (rp [false; true] 1 ++ C2)].
Proof.
  intro q. cbn [den bden]. change (rep01 (q * 3 + 1)) with (rp [false; true] (q * 3 + 1)).
  rewrite rp_add, rp_mul, app_nil_r, <- ?app_assoc. reflexivity.
Qed.

Definition dv2 := Eval vm_compute in
  dmB 3 [Lit [false; false; true; false]; Rep (rp [false; true] 3) O; Lit (rp [false; true] 1 ++ C2)] 0.

Definition lo3 : list bool := Eval vm_compute in match dv2 with Some ([Lit a; _; _], _) => a | _ => [] end.
Definition P3 : list bool := Eval vm_compute in match dv2 with Some ([_; Rep p _; _], _) => p | _ => [] end.
Definition hi3 : list bool := Eval vm_compute in match dv2 with Some ([_; _; Lit a], _) => a | _ => [] end.
Definition r3 : N := Eval vm_compute in match dv2 with Some (_, r) => r | None => 0%N end.

Lemma dv2_ok : forall q,
  dmB 3 [Lit [false; false; true; false]; Rep (rp [false; true] 3) q; Lit (rp [false; true] 1 ++ C2)] 0 =
  Some ([Lit lo3; Rep P3 q; Lit hi3], r3).
Proof. intro q. vm_compute. reflexivity. Qed.

(** ** Level 3 *)

Definition b3 (q : nat) : list bool := den [Lit lo3; Rep P3 q; Lit hi3].
Definition u3 : nat := 2 + 2 * bval b2 + lc2.

Theorem lvl3 : Lvl (3 + N.to_nat r3) (b3 q3) u3 w3.
Proof.
  apply (level_next 3 b2 12 [true] C2 lc2 (b3 q3) r3 w3 lvl2 C2_len end2).
  rewrite h2_eq, Zl2_den. apply dmB_sound. apply dv2_ok.
Qed.

End L23.

Module L34.

(** * 1RB1LB_1RC0RD_0LA1RE_0RF1LC_1LA0RB_---1LC: from level 3 to level 4

    Level 3 has class 4 and the counter word [b3 q = lo3 ++ P3^q ++ hi3].  The step is proved
    for every [q] of the form [3 q' + 1]; the real value of [q] is used only in the last
    theorem.  The end phase is the class 4 certificate on the 4-bit literal [lo3]; the division
    by 3 runs over five blocks, two of them repeated. *)

Import Individual62.
Import T694_levels End694 Sym694 Lev694 Lvl1_694 Eng694 Cert694 L23.
Import Lia Arith PeanoNat Bool NArith ZArith.
Import Coq.Lists.List.
Import ListNotations.

(** ** The end phase *)

Definition c4_3 := Eval vm_compute in c4cert 3000 3000 4 lo3 w3.

Definition s3 : nat := Eval vm_compute in match c4_3 with Some (s, _, _, _, _) => s | None => O end.
Definition la3 : nat := Eval vm_compute in match c4_3 with Some (_, x, _, _, _) => x | None => O end.
Definition cb3 : list bool := Eval vm_compute in match c4_3 with Some (_, _, x, _, _) => x | None => [] end.
Definition ab3 : list bool := Eval vm_compute in match c4_3 with Some (_, _, _, x, _) => x | None => [] end.
Definition w4 : list bool := Eval vm_compute in match c4_3 with Some (_, _, _, _, x) => x | None => [] end.

Lemma c4_3_ok : c4cert 3000 3000 4 lo3 w3 = Some (s3, la3, cb3, ab3, w4).
Proof. vm_compute. reflexivity. Qed.

Lemma b3_split : forall q, b3 q = lo3 ++ (rp P3 q ++ hi3).
Proof. intro q. unfold b3. cbn [den bden]. rewrite app_nil_r. reflexivity. Qed.

Lemma rest3_len : forall q, length (rp P3 q ++ hi3) = 2 * (3 * q + 16).
Proof.
  intro q. rewrite length_app, length_rp.
  change (length P3) with 6%nat. change (length hi3) with 32%nat. lia.
Qed.

Definition C3 (q : nat) : list bool := cb3 ++ map negb (rp P3 q ++ hi3) ++ ab3.

Lemma C3_len : forall q, length (C3 q) = 2 * (3 * q + 23).
Proof.
  intro q. unfold C3. rewrite !length_app, length_map, rest3_len.
  change (length cb3) with 12%nat. change (length ab3) with 2%nat. lia.
Qed.

Lemma end3 : forall q k, (1 <= k)%nat -> exists n M',
  tickN 3 n (rep10 k ++ c1101 ++ repeat true (3 * (2 + 2 * bval (b3 q))) ++ rep10 4 ++ c1101 ++
             encb false (b3 q) ++ w3) =
    Some (Slev M' (3 * (2 + 2 * bval (b3 q) + (3 * q + 23)) + 1) w4) /\
  Z.of_nat M' = (Z.of_nat k + Z.of_nat (bval (C3 q)) * pw4 (2 + 2 * bval (b3 q)))%Z.
Proof.
  intros q k Hk.
  assert (Hh : (1 <= 2 + 2 * bval (b3 q))%nat) by lia.
  destruct (c4cert_sound _ _ _ _ _ _ _ _ _ _ c4_3_ok (rp P3 q ++ hi3) (3 * q + 16)
              (2 + 2 * bval (b3 q)) (rest3_len q) Hh k Hk) as [n [M' [E D]]].
  exists n, M'. split; [| exact D].
  replace (3 * (2 + 2 * bval (b3 q) + (3 * q + 23)) + 1)
    with (3 * (2 + 2 * bval (b3 q) + (s3 + (3 * q + 16) + la3)) + 1)
    by (change s3 with 6%nat; change la3 with 1%nat; lia).
  rewrite <- (b3_split q) in E. exact E.
Qed.

(** ** The word of level 3 modulo 3 *)

Lemma b3_reblock : forall q',
  b3 (q' * 3 + 1) = den [Lit lo3; Rep (rp P3 3) q'; Lit (rp P3 1 ++ hi3)].
Proof. intro q'. unfold b3. cbn [den bden]. rewrite rp_add, rp_mul, <- ?app_assoc. reflexivity. Qed.

Definition dvT3 := Eval vm_compute in dmB 3 [Lit lo3; Rep (rp P3 3) O; Lit (rp P3 1 ++ hi3)] 0.

Definition tl3 : list bool := Eval vm_compute in match dvT3 with Some ([Lit a; _; _], _) => a | _ => [] end.
Definition tP3 : list bool := Eval vm_compute in match dvT3 with Some ([_; Rep p _; _], _) => p | _ => [] end.
Definition th3 : list bool := Eval vm_compute in match dvT3 with Some ([_; _; Lit a], _) => a | _ => [] end.

Lemma dvT3_ok : forall q',
  dmB 3 [Lit lo3; Rep (rp P3 3) q'; Lit (rp P3 1 ++ hi3)] 0 = Some ([Lit tl3; Rep tP3 q'; Lit th3], 2%N).
Proof. intro q'. vm_compute. reflexivity. Qed.

Definition t3 (q' : nat) : list bool := den [Lit tl3; Rep tP3 q'; Lit th3].

Lemma T3_mod : forall q', bval (b3 (q' * 3 + 1)) = 3 * bval (t3 q') + 2.
Proof.
  intro q'. pose proof (dmB_sound _ _ _ _ _ (dvT3_ok q')) as H. rewrite <- b3_reblock in H.
  assert (H03 : (0 < 3)%N) by reflexivity.
  destruct (dm_spec 3 _ 0 _ _ H03 H) as [He _]. unfold t3. lia.
Qed.

Definition j3 (q' : nat) : nat := 2 * bval (t3 q') + 1.

Lemma h3_eq : forall q', 2 * bval (b3 (q' * 3 + 1)) = j3 q' * 3 + 1.
Proof. intro q'. rewrite T3_mod. unfold j3. lia. Qed.

(** ** The division *)

Definition nP3 : list bool := Eval vm_compute in map negb P3.
Definition nhi3 : list bool := Eval vm_compute in map negb hi3.

Lemma C3_blocks : forall q',
  C3 (q' * 3 + 1) = cb3 ++ rp (rp nP3 3) q' ++ rp nP3 1 ++ nhi3 ++ ab3.
Proof.
  intro q'. unfold C3. rewrite map_app, map_rp, rp_add, rp_mul, <- ?app_assoc. reflexivity.
Qed.

Lemma Zl3_den : forall q' j,
  [false; false; true; false] ++ rep01 (j * 3 + 1) ++ C3 (q' * 3 + 1) =
  den [Lit [false; false; true; false]; Rep (rp [false; true] 3) j; Lit (rp [false; true] 1 ++ cb3);
       Rep (rp nP3 3) q'; Lit (rp nP3 1 ++ nhi3 ++ ab3)].
Proof.
  intros q' j. rewrite C3_blocks. cbn [den bden].
  change (rep01 (j * 3 + 1)) with (rp [false; true] (j * 3 + 1)).
  rewrite rp_add, rp_mul, app_nil_r, <- ?app_assoc. reflexivity.
Qed.

Definition dv3 := Eval vm_compute in
  dmB 3 [Lit [false; false; true; false]; Rep (rp [false; true] 3) O; Lit (rp [false; true] 1 ++ cb3);
         Rep (rp nP3 3) O; Lit (rp nP3 1 ++ nhi3 ++ ab3)] 0.

Definition a4 : list bool := Eval vm_compute in match dv3 with Some ([Lit a; _; _; _; _], _) => a | _ => [] end.
Definition Pj4 : list bool := Eval vm_compute in match dv3 with Some ([_; Rep p _; _; _; _], _) => p | _ => [] end.
Definition m4 : list bool := Eval vm_compute in match dv3 with Some ([_; _; Lit a; _; _], _) => a | _ => [] end.
Definition Pq4 : list bool := Eval vm_compute in match dv3 with Some ([_; _; _; Rep p _; _], _) => p | _ => [] end.
Definition e4 : list bool := Eval vm_compute in match dv3 with Some ([_; _; _; _; Lit a], _) => a | _ => [] end.
Definition r4 : N := Eval vm_compute in match dv3 with Some (_, r) => r | None => 0%N end.

Lemma dv3_ok : forall q' j,
  dmB 3 [Lit [false; false; true; false]; Rep (rp [false; true] 3) j; Lit (rp [false; true] 1 ++ cb3);
         Rep (rp nP3 3) q'; Lit (rp nP3 1 ++ nhi3 ++ ab3)] 0 =
  Some ([Lit a4; Rep Pj4 j; Lit m4; Rep Pq4 q'; Lit e4], r4).
Proof. intros q' j. vm_compute. reflexivity. Qed.

(** ** Level 4 *)

Definition b4 (q' j : nat) : list bool := den [Lit a4; Rep Pj4 j; Lit m4; Rep Pq4 q'; Lit e4].

Theorem lvl4_gen : forall q' u,
  Lvl 4 (b3 (q' * 3 + 1)) u w3 ->
  Lvl (3 + N.to_nat r4) (b4 q' (j3 q'))
      (2 + 2 * bval (b3 (q' * 3 + 1)) + (3 * (q' * 3 + 1) + 23)) w4.
Proof.
  intros q' u H.
  apply (level_next 4 (b3 (q' * 3 + 1)) u w3 (C3 (q' * 3 + 1)) (3 * (q' * 3 + 1) + 23)
           (b4 q' (j3 q')) r4 w4 H (C3_len _) (end3 _)).
  rewrite h3_eq, Zl3_den. apply dmB_sound. apply dv3_ok.
Qed.

(** The real chain. *)
Definition q4 : nat := N.to_nat 945012%N.
Definition u4 : nat := 2 + 2 * bval (b3 (q4 * 3 + 1)) + (3 * (q4 * 3 + 1) + 23).

Theorem lvl4 : Lvl (3 + N.to_nat r4) (b4 q4 (j3 q4)) u4 w4.
Proof.
  assert (E : q3 = q4 * 3 + 1) by (unfold q3, q4; lia).
  pose proof lvl3 as H. rewrite E in H. exact (lvl4_gen q4 _ H).
Qed.

End L34.

Module L45.

(** * 1RB1LB_1RC0RD_0LA1RE_0RF1LC_1LA0RB_---1LC: from level 4 to level 5

    Level 4 has class 5 and the counter word [b4 q' j] with two repeated blocks.  The end phase
    eats the word a few bits per round: a run up to the first block, a cycle per copy of the
    first block, a run across the junction, a cycle per copy of the second block and a closing
    computation.  The contributions add up to a word with two repeated blocks ([asm]). *)

Import Individual62.
Import T694_levels End694 Sym694 Lev694 Lvl1_694 Eng694 Cert694 Run694 L23 L34.
Import Lia Arith PeanoNat Bool NArith ZArith.
Import Coq.Lists.List.
Import ListNotations.

(** ** The cells of the counter word *)

Definition o1 : bool := Eval vm_compute in par false a4.
Definition o2 : bool := Eval vm_compute in par o1 m4.
Definition Hd4 : list bool := Eval vm_compute in rep10 5 ++ c1101 ++ encb false a4.
Definition EJ : list bool := Eval vm_compute in encb o1 Pj4.
Definition EM : list bool := Eval vm_compute in encb o1 m4.
Definition EQ : list bool := Eval vm_compute in encb o2 Pq4.
Definition EE : list bool := Eval vm_compute in encb o2 e4.

Definition cells4 (q' j : nat) : list bool := rep10 5 ++ c1101 ++ encb false (b4 q' j) ++ w4.

Lemma cells4_eq : forall q' j, cells4 q' j = Hd4 ++ rp EJ j ++ EM ++ rp EQ q' ++ EE ++ w4.
Proof.
  intros q' j. unfold cells4, b4. cbn [den bden]. rewrite app_nil_r.
  rewrite (encb_app a4). change (par false a4) with o1.
  rewrite (encb_rp Pj4 o1 eq_refl), (encb_app m4). change (par o1 m4) with o2.
  rewrite (encb_rp Pq4 o2 eq_refl).
  change Hd4 with (rep10 5 ++ c1101 ++ encb false a4). change EJ with (encb o1 Pj4).
  change EM with (encb o1 m4). change EQ with (encb o2 Pq4). change EE with (encb o2 e4).
  rewrite <- ?app_assoc. reflexivity.
Qed.

(** ** Boundary states, read off one instance *)

Definition inst : list bool := Eval vm_compute in cells4 5 8.

Definition bst (n m L : nat) : sst :=
  let '(_, _, post) := fst (fst (grun true n (c1101, true, inst) 0 0)) in
  (c1101, true, firstn (m mod 3 + L) (skipn (m - m mod 3) post)).

Definition st0 : sst := (c1101, true, []).
Definition S1 : sst := Eval vm_compute in bst 28 28 6.
Definition S2 : sst := Eval vm_compute in bst 108 121 3.

Definition u1 : list bool := Eval vm_compute in firstn 5 EJ.
Definition v1 : list bool := Eval vm_compute in skipn 5 EJ.
Definition u2 : list bool := Eval vm_compute in firstn 11 EQ.
Definition v2 : list bool := Eval vm_compute in skipn 11 EQ.

Definition F0 : list bool := Eval vm_compute in Hd4 ++ rp EJ 1 ++ u1.
Definition F1c : list bool := Eval vm_compute in v1 ++ u1.
Definition F1 : list bool := Eval vm_compute in v1 ++ EM ++ rp EQ 0 ++ u2.
Definition F2c : list bool := Eval vm_compute in v2 ++ u2.
Definition Fw : list bool := Eval vm_compute in v2 ++ EE ++ w4.

Lemma cells4_cut : forall n1 n2,
  cells4 (n2 + 1) (n1 + 2) = (F0 ++ rp F1c n1 ++ F1 ++ rp F2c n2 ++ []) ++ Fw.
Proof.
  intros n1 n2. rewrite cells4_eq.
  replace (n1 + 2) with (1 + n1 + 1) by lia. replace (n2 + 1) with (0 + n2 + 1) by lia.
  rewrite (rp_recut EJ u1 v1 n1 1 1 v1 eq_refl eq_refl), (rp_recut EQ u2 v2 n2 0 1 v2 eq_refl eq_refl).
  change F0 with (Hd4 ++ rp EJ 1 ++ u1). change F1c with (v1 ++ u1).
  change F1 with (v1 ++ EM ++ rp EQ 0 ++ u2). change F2c with (v2 ++ u2).
  change Fw with (v2 ++ EE ++ w4).
  rewrite app_nil_r, <- ?app_assoc. reflexivity.
Qed.

(** ** Runs and cycles *)

Definition a0 : Z := Eval vm_compute in snd (fst (grun false 28 (addpost st0 F0) 0 0)).
Definition a1c : Z := Eval vm_compute in snd (fst (grun false 8 (addpost S1 F1c) 0 0)).
Definition a1 : Z := Eval vm_compute in snd (fst (grun false 32 (addpost S1 F1) 0 0)).
Definition a2c : Z := Eval vm_compute in snd (fst (grun false 24 (addpost S2 F2c) 0 0)).

Lemma R0 : Run st0 F0 S1 9 a0.
Proof. apply (runck_sound 28). vm_compute. reflexivity. Qed.

Lemma C1 : Run S1 F1c S1 3 a1c.
Proof. apply (runck_sound 8). vm_compute. reflexivity. Qed.

Lemma R1 : Run S1 F1 S2 13 a1.
Proof. apply (runck_sound 32). vm_compute. reflexivity. Qed.

Lemma C2 : Run S2 F2c S2 9 a2c.
Proof. apply (runck_sound 24). vm_compute. reflexivity. Qed.

Definition segs (n1 n2 : nat) : list seg := [SL a0 9; SC a1c 3 n1; SL a1 13; SC a2c 9 n2].

Lemma runA : forall n1 n2,
  Run st0 (F0 ++ rp F1c n1 ++ F1 ++ rp F2c n2 ++ []) S2 (segSh (segs n1 n2)) (segV (segs n1 n2)).
Proof.
  intros n1 n2. unfold segs.
  exact (run_SL _ _ _ _ _ _ _ _ R0 (run_SC _ _ _ _ _ _ _ _ C1
          (run_SL _ _ _ _ _ _ _ _ R1 (run_SC _ _ _ _ _ _ _ _ C2 (run_end _))))).
Qed.

(** ** The carry chain *)

Definition as4 := Eval vm_compute in asm 0 (segs 0 0).
Definition c0w : list bool := Eval vm_compute in match as4 with Some ([Lit a; _; _; _], _) => a | _ => [] end.
Definition c1w : list bool := Eval vm_compute in match as4 with Some ([_; Rep p _; _; _], _) => p | _ => [] end.
Definition c2w : list bool := Eval vm_compute in match as4 with Some ([_; _; Lit a; _], _) => a | _ => [] end.
Definition c3w : list bool := Eval vm_compute in match as4 with Some ([_; _; _; Rep p _], _) => p | _ => [] end.
Definition cA : Z := Eval vm_compute in match as4 with Some (_, c) => c | None => (-1)%Z end.

Lemma as4_ok : forall n1 n2,
  asm 0 (segs n1 n2) = Some ([Lit c0w; Rep c1w n1; Lit c2w; Rep c3w n2], cA).
Proof. intros n1 n2. vm_compute. reflexivity. Qed.

(** ** The closing computation *)

Definition ec4 := Eval vm_compute in endcert 3000 (addpost S2 Fw).
Definition ae4 : Z := Eval vm_compute in match ec4 with Some (a, _, _, _) => a | None => 0%Z end.
Definition z1_4 : nat := Eval vm_compute in match ec4 with Some (_, z, _, _) => z | None => O end.
Definition z2_4 : nat := Eval vm_compute in match ec4 with Some (_, _, z, _) => z | None => O end.
Definition w5 : list bool := Eval vm_compute in match ec4 with Some (_, _, _, x) => x | None => [] end.
Definition la4 : nat := Eval vm_compute in (z1_4 + z2_4 - 1) / 3.
Definition tp4 : N := Eval vm_compute in Z.to_N ((cA + ae4) / 4 ^ Z.of_nat la4).
Definition ab4 : list bool := Eval vm_compute in zbits ((cA + ae4) mod 4 ^ Z.of_nat la4) (2 * la4).

Lemma ec4_ok : endcert 3000 (addpost S2 Fw) = Some (ae4, z1_4, z2_4, w5).
Proof. vm_compute. reflexivity. Qed.

Lemma cA_nn : (0 <= cA)%Z.
Proof. apply Z.leb_le. vm_compute. reflexivity. Qed.

Lemma ab4_val : (Z.of_N (bvalN ab4) + Z.of_N tp4 * pw4 la4 = cA + ae4)%Z.
Proof. vm_compute. reflexivity. Qed.

Lemma ab4_len : length ab4 = 2 * la4.
Proof. vm_compute. reflexivity. Qed.

Lemma z_4 : z1_4 + z2_4 = 3 * la4 + 1.
Proof. vm_compute. reflexivity. Qed.

Definition C4 (n1 n2 : nat) : list bool := den [Lit c0w; Rep c1w n1; Lit c2w; Rep c3w n2] ++ ab4.
Definition lc4 (n1 n2 : nat) : nat := segSh (segs n1 n2) + la4.

Lemma C4_len : forall n1 n2, length (C4 n1 n2) = 2 * lc4 n1 n2.
Proof.
  intros n1 n2.
  exact (proj1 (stageA st0 _ S2 (segs n1 n2) 3000 Fw ae4 z1_4 z2_4 w5 _ cA ab4 la4 (Z.of_N tp4)
                  (runA n1 n2) ec4_ok (as4_ok n1 n2) cA_nn ab4_val ab4_len z_4)).
Qed.

Lemma end4 : forall n1 n2 h k, (1 <= k)%nat -> exists n M',
  tickN 3 n (rep10 k ++ c1101 ++ repeat true (3 * h) ++ rep10 5 ++ c1101 ++
             encb false (b4 (n2 + 1) (n1 + 2)) ++ w4) =
    Some (Slev M' (3 * (h + lc4 n1 n2) + 1) w5) /\
  Z.of_nat M' = (Z.of_nat k +
                 (Z.of_nat (bval (C4 n1 n2)) + Z.of_N tp4 * pw4 (lc4 n1 n2)) * pw4 h)%Z.
Proof.
  intros n1 n2 h k Hk.
  destruct (stageA st0 _ S2 (segs n1 n2) 3000 Fw ae4 z1_4 z2_4 w5 _ cA ab4 la4 (Z.of_N tp4)
              (runA n1 n2) ec4_ok (as4_ok n1 n2) cA_nn ab4_val ab4_len z_4) as [_ H].
  destruct (H h k Hk) as [n [M' [E D]]]. exists n, M'. split; [| exact D].
  change (rep10 5 ++ c1101 ++ encb false (b4 (n2 + 1) (n1 + 2)) ++ w4) with (cells4 (n2 + 1) (n1 + 2)).
  rewrite cells4_cut.
  cbv [st0 conc] in E. rewrite ?app_nil_r, <- ?app_assoc in E. rewrite ?app_nil_r, <- ?app_assoc.
  exact E.
Qed.

(** ** Residues of the counts

    The division of the next total needs the counts of level 4 modulo 3: one more division of
    the quotient word of level 3, and the value of the level-4 word modulo 3. *)

Lemma bval_app_ge : forall a b, bval b <= bval (a ++ b).
Proof.
  intros a b. rewrite bval_app.
  assert (2 ^ length a <> 0)%nat by (apply Nat.pow_nonzero; lia). nia.
Qed.

Lemma t3_reblock : forall q'', t3 (q'' * 3) = den [Lit tl3; Rep (rp tP3 3) q''; Lit th3].
Proof. intro q''. unfold t3. cbn [den bden]. rewrite rp_mul. reflexivity. Qed.

Definition dvt3 := Eval vm_compute in dmB 3 [Lit tl3; Rep (rp tP3 3) O; Lit th3] 0.
Definition ttl3 : list bool := Eval vm_compute in match dvt3 with Some ([Lit a; _; _], _) => a | _ => [] end.
Definition ttP3 : list bool := Eval vm_compute in match dvt3 with Some ([_; Rep p _; _], _) => p | _ => [] end.
Definition tth3 : list bool := Eval vm_compute in match dvt3 with Some ([_; _; Lit a], _) => a | _ => [] end.

Lemma dvt3_ok : forall q'',
  dmB 3 [Lit tl3; Rep (rp tP3 3) q''; Lit th3] 0 = Some ([Lit ttl3; Rep ttP3 q''; Lit tth3], 0%N).
Proof. intro q''. vm_compute. reflexivity. Qed.

Definition tt3 (q'' : nat) : list bool := den [Lit ttl3; Rep ttP3 q''; Lit tth3].

Lemma t3_mod : forall q'', bval (t3 (q'' * 3)) = 3 * bval (tt3 q'').
Proof.
  intro q''. pose proof (dmB_sound _ _ _ _ _ (dvt3_ok q'')) as H. rewrite <- t3_reblock in H.
  assert (H03 : (0 < 3)%N) by reflexivity.
  destruct (dm_spec 3 _ 0 _ _ H03 H) as [He _]. unfold tt3. lia.
Qed.

Lemma tt3_pos : forall q'', 1 <= bval (tt3 q'').
Proof.
  intro q''. unfold tt3. cbn [den bden].
  assert (Hh : (1 <= bvalN (tth3 ++ []))%N) by (apply N.leb_le; vm_compute; reflexivity).
  pose proof (bvalN_spec (tth3 ++ [])) as Hs.
  pose proof (bval_app_ge ttl3 (rp ttP3 q'' ++ tth3 ++ [])) as H1.
  pose proof (bval_app_ge (rp ttP3 q'') (tth3 ++ [])) as H2. lia.
Qed.

Lemma b4_reblock : forall n1' n2',
  b4 (n2' * 3 + 2 + 1) (n1' * 3 + 2 + 2) =
  den [Lit a4; Rep (rp Pj4 3) (n1' + 1); Lit (rp Pj4 1 ++ m4); Rep (rp Pq4 3) (n2' + 1); Lit e4].
Proof.
  intros n1' n2'. replace (n2' * 3 + 2 + 1) with ((n2' + 1) * 3) by lia.
  replace (n1' * 3 + 2 + 2) with ((n1' + 1) * 3 + 1) by lia.
  unfold b4. cbn [den bden]. rewrite rp_add, !rp_mul, <- ?app_assoc. reflexivity.
Qed.

Definition dvT4 := Eval vm_compute in
  dmB 3 [Lit a4; Rep (rp Pj4 3) O; Lit (rp Pj4 1 ++ m4); Rep (rp Pq4 3) O; Lit e4] 0.
Definition t4a : list bool := Eval vm_compute in match dvT4 with Some ([Lit a; _; _; _; _], _) => a | _ => [] end.
Definition t4Pj : list bool := Eval vm_compute in match dvT4 with Some ([_; Rep p _; _; _; _], _) => p | _ => [] end.
Definition t4m : list bool := Eval vm_compute in match dvT4 with Some ([_; _; Lit a; _; _], _) => a | _ => [] end.
Definition t4Pq : list bool := Eval vm_compute in match dvT4 with Some ([_; _; _; Rep p _; _], _) => p | _ => [] end.
Definition t4e : list bool := Eval vm_compute in match dvT4 with Some ([_; _; _; _; Lit a], _) => a | _ => [] end.

Lemma dvT4_ok : forall j q,
  dmB 3 [Lit a4; Rep (rp Pj4 3) j; Lit (rp Pj4 1 ++ m4); Rep (rp Pq4 3) q; Lit e4] 0 =
  Some ([Lit t4a; Rep t4Pj j; Lit t4m; Rep t4Pq q; Lit t4e], 1%N).
Proof. intros j q. vm_compute. reflexivity. Qed.

Definition t4 (n1' n2' : nat) : list bool :=
  den [Lit t4a; Rep t4Pj (n1' + 1); Lit t4m; Rep t4Pq (n2' + 1); Lit t4e].

Lemma T4_mod : forall n1' n2',
  bval (b4 (n2' * 3 + 2 + 1) (n1' * 3 + 2 + 2)) = 3 * bval (t4 n1' n2') + 1.
Proof.
  intros n1' n2'. pose proof (dmB_sound _ _ _ _ _ (dvT4_ok (n1' + 1) (n2' + 1))) as H.
  rewrite <- b4_reblock in H.
  assert (H03 : (0 < 3)%N) by reflexivity.
  destruct (dm_spec 3 _ 0 _ _ H03 H) as [He _]. unfold t4. lia.
Qed.

Definition g4 (n1' n2' : nat) : nat := 2 * bval (t4 n1' n2').

Lemma h4_eq : forall n1' n2',
  2 * bval (b4 (n2' * 3 + 2 + 1) (n1' * 3 + 2 + 2)) = g4 n1' n2' * 3 + 2.
Proof. intros n1' n2'. rewrite T4_mod. unfold g4. lia. Qed.

(** ** The division *)

Lemma Zl4_den : forall n1' n2' g,
  [false; false; true; false] ++ rep01 (g * 3 + 2) ++ C4 (n1' * 3 + 2) (n2' * 3 + 2) =
  den [Lit [false; false; true; false]; Rep (rp [false; true] 3) g; Lit (rp [false; true] 2 ++ c0w);
       Rep (rp c1w 3) n1'; Lit (rp c1w 2 ++ c2w); Rep (rp c3w 3) n2'; Lit (rp c3w 2 ++ ab4)].
Proof.
  intros n1' n2' g. unfold C4. cbn [den bden].
  change (rep01 (g * 3 + 2)) with (rp [false; true] (g * 3 + 2)).
  rewrite !rp_add, !rp_mul, ?app_nil_r, <- ?app_assoc. reflexivity.
Qed.

Definition dv4 := Eval vm_compute in
  dmB 3 [Lit [false; false; true; false]; Rep (rp [false; true] 3) O; Lit (rp [false; true] 2 ++ c0w);
         Rep (rp c1w 3) O; Lit (rp c1w 2 ++ c2w); Rep (rp c3w 3) O; Lit (rp c3w 2 ++ ab4)] tp4.
Definition a5 : list bool := Eval vm_compute in match dv4 with Some ([Lit a; _; _; _; _; _; _], _) => a | _ => [] end.
Definition Pg5 : list bool := Eval vm_compute in match dv4 with Some ([_; Rep p _; _; _; _; _; _], _) => p | _ => [] end.
Definition m5a : list bool := Eval vm_compute in match dv4 with Some ([_; _; Lit a; _; _; _; _], _) => a | _ => [] end.
Definition Pj5 : list bool := Eval vm_compute in match dv4 with Some ([_; _; _; Rep p _; _; _; _], _) => p | _ => [] end.
Definition m5b : list bool := Eval vm_compute in match dv4 with Some ([_; _; _; _; Lit a; _; _], _) => a | _ => [] end.
Definition Pq5 : list bool := Eval vm_compute in match dv4 with Some ([_; _; _; _; _; Rep p _; _], _) => p | _ => [] end.
Definition e5 : list bool := Eval vm_compute in match dv4 with Some ([_; _; _; _; _; _; Lit a], _) => a | _ => [] end.
Definition r5 : N := Eval vm_compute in match dv4 with Some (_, r) => r | None => 0%N end.

Lemma dv4_ok : forall g n1' n2',
  dmB 3 [Lit [false; false; true; false]; Rep (rp [false; true] 3) g; Lit (rp [false; true] 2 ++ c0w);
         Rep (rp c1w 3) n1'; Lit (rp c1w 2 ++ c2w); Rep (rp c3w 3) n2'; Lit (rp c3w 2 ++ ab4)] tp4 =
  Some ([Lit a5; Rep Pg5 g; Lit m5a; Rep Pj5 n1'; Lit m5b; Rep Pq5 n2'; Lit e5], r5).
Proof. intros g n1' n2'. vm_compute. reflexivity. Qed.

Lemma tp4_lt : (tp4 < 3)%N.
Proof. reflexivity. Qed.

(** ** Level 5 *)

Definition b5 (g n1' n2' : nat) : list bool :=
  den [Lit a5; Rep Pg5 g; Lit m5a; Rep Pj5 n1'; Lit m5b; Rep Pq5 n2'; Lit e5].

Theorem lvl5_gen : forall n1' n2' u,
  Lvl 5 (b4 (n2' * 3 + 2 + 1) (n1' * 3 + 2 + 2)) u w4 ->
  Lvl (3 + N.to_nat r5) (b5 (g4 n1' n2') n1' n2')
      (2 + 2 * bval (b4 (n2' * 3 + 2 + 1) (n1' * 3 + 2 + 2)) + lc4 (n1' * 3 + 2) (n2' * 3 + 2)) w5.
Proof.
  intros n1' n2' u H.
  apply (level_next_top 5 (b4 (n2' * 3 + 2 + 1) (n1' * 3 + 2 + 2)) u w4
           (C4 (n1' * 3 + 2) (n2' * 3 + 2)) (lc4 (n1' * 3 + 2) (n2' * 3 + 2)) tp4
           (b5 (g4 n1' n2') n1' n2') r5 w5 H (C4_len _ _) tp4_lt
           (fun k Hk => end4 _ _ _ k Hk)).
  rewrite h4_eq, Zl4_den. apply dmB_sound. apply dv4_ok.
Qed.

(** The real chain. *)
Definition q5 : nat := N.to_nat 315004%N.
Definition n2r : nat := N.to_nat 315003%N.
Definition n1r : nat := 2 * bval (tt3 q5) - 1.
Definition u5 : nat :=
  2 + 2 * bval (b4 (n2r * 3 + 2 + 1) (n1r * 3 + 2 + 2)) + lc4 (n1r * 3 + 2) (n2r * 3 + 2).

Theorem lvl5 : Lvl (3 + N.to_nat r5) (b5 (g4 n1r n2r) n1r n2r) u5 w5.
Proof.
  assert (E1 : q4 = n2r * 3 + 2 + 1) by (unfold q4, n2r; lia).
  assert (E2 : j3 q4 = n1r * 3 + 2 + 2).
  { unfold j3. replace q4 with (q5 * 3) by (unfold q4, q5; lia).
    rewrite t3_mod. pose proof (tt3_pos q5). unfold n1r. lia. }
  pose proof lvl4 as H. rewrite E2, E1 in H. exact (lvl5_gen n1r n2r _ H).
Qed.

End L45.

Module L56.

(** * 1RB1LB_1RC0RD_0LA1RE_0RF1LC_1LA0RB_---1LC: from level 5 to level 6

    Level 5 has class 3 and the counter word [b5 g n1' n2'] with three repeated blocks.  The
    end phase is certified round by round ([crun_run]): a run to the first block, then for each
    block a cycle per copy and a run across the next junction, and a closing computation. *)

Import Individual62.
Import T694_levels End694 Sym694 Lev694 Lvl1_694 Eng694 Cert694 Run694 L23 L34 L45.
Import Lia Arith PeanoNat Bool NArith ZArith.
Import Coq.Lists.List.
Import ListNotations.

(** ** The cells of the counter word *)

Definition p1 : bool := Eval vm_compute in par false a5.
Definition p2 : bool := Eval vm_compute in par p1 m5a.
Definition p3 : bool := Eval vm_compute in par p2 m5b.
Definition Hd5 : list bool := Eval vm_compute in rep10 3 ++ c1101 ++ encb false a5.
Definition EG5 : list bool := Eval vm_compute in encb p1 Pg5.
Definition EA5 : list bool := Eval vm_compute in encb p1 m5a.
Definition EJ5 : list bool := Eval vm_compute in encb p2 Pj5.
Definition EB5 : list bool := Eval vm_compute in encb p2 m5b.
Definition EQ5 : list bool := Eval vm_compute in encb p3 Pq5.
Definition EE5 : list bool := Eval vm_compute in encb p3 e5.

Definition cells5 (g n1 n2 : nat) : list bool := rep10 3 ++ c1101 ++ encb false (b5 g n1 n2) ++ w5.

Lemma cells5_eq : forall g n1 n2,
  cells5 g n1 n2 = Hd5 ++ rp EG5 g ++ EA5 ++ rp EJ5 n1 ++ EB5 ++ rp EQ5 n2 ++ EE5 ++ w5.
Proof.
  intros g n1 n2. unfold cells5, b5. cbn [den bden]. rewrite app_nil_r.
  rewrite (encb_app a5). change (par false a5) with p1.
  rewrite (encb_rp Pg5 p1 eq_refl), (encb_app m5a). change (par p1 m5a) with p2.
  rewrite (encb_rp Pj5 p2 eq_refl), (encb_app m5b). change (par p2 m5b) with p3.
  rewrite (encb_rp Pq5 p3 eq_refl).
  change Hd5 with (rep10 3 ++ c1101 ++ encb false a5). change EG5 with (encb p1 Pg5).
  change EA5 with (encb p1 m5a). change EJ5 with (encb p2 Pj5). change EB5 with (encb p2 m5b).
  change EQ5 with (encb p3 Pq5). change EE5 with (encb p3 e5).
  rewrite <- ?app_assoc. reflexivity.
Qed.

(** ** Boundary states, read off one instance *)

Definition inst5 : list bool := Eval vm_compute in cells5 8 6 5.

Fixpoint rst (rounds : nat) (st : sst) : sst :=
  match rounds with
  | O => st
  | S c => match grun false 4 st 0 0 with (s1, _, _) => rst c (strip s1) end
  end.

Definition cutL (L : nat) (st : sst) : sst :=
  match st with (pre, x, post) => (pre, x, firstn (leadx x post + L) post) end.

Definition st50 : sst := (c1101, true, []).
Definition SG : sst := Eval vm_compute in cutL 12 (rst 5 (c1101, true, inst5)).
Definition SJ : sst := Eval vm_compute in cutL 12 (rst 15 (c1101, true, inst5)).
Definition SQ : sst := Eval vm_compute in cutL 30 (rst 51 (c1101, true, inst5)).

Definition ug : list bool := Eval vm_compute in firstn 3 EG5.
Definition vg : list bool := Eval vm_compute in skipn 3 EG5.
Definition uj : list bool := Eval vm_compute in firstn 12 EJ5.
Definition vj : list bool := Eval vm_compute in skipn 12 EJ5.
Definition uq : list bool := Eval vm_compute in firstn 36 EQ5.
Definition vq : list bool := Eval vm_compute in skipn 36 EQ5.

Definition G0 : list bool := Eval vm_compute in Hd5 ++ rp EG5 3 ++ ug.
Definition Gc : list bool := Eval vm_compute in vg ++ ug.
Definition G1 : list bool := Eval vm_compute in vg ++ EA5 ++ rp EJ5 0 ++ uj.
Definition Jc : list bool := Eval vm_compute in vj ++ uj.
Definition G2 : list bool := Eval vm_compute in vj ++ EB5 ++ rp EQ5 0 ++ uq.
Definition Qc : list bool := Eval vm_compute in vq ++ uq.
Definition Gw : list bool := Eval vm_compute in vq ++ EE5 ++ w5.

Lemma cells5_cut : forall ng nj nq,
  cells5 (ng + 4) (nj + 1) (nq + 1) =
  (G0 ++ rp Gc ng ++ G1 ++ rp Jc nj ++ G2 ++ rp Qc nq ++ []) ++ Gw.
Proof.
  intros ng nj nq. rewrite cells5_eq.
  replace (ng + 4) with (3 + ng + 1) by lia. replace (nj + 1) with (0 + nj + 1) by lia.
  replace (nq + 1) with (0 + nq + 1) by lia.
  rewrite (rp_recut EG5 ug vg ng 3 1 vg eq_refl eq_refl),
          (rp_recut EJ5 uj vj nj 0 1 vj eq_refl eq_refl),
          (rp_recut EQ5 uq vq nq 0 1 vq eq_refl eq_refl).
  change G0 with (Hd5 ++ rp EG5 3 ++ ug). change Gc with (vg ++ ug).
  change G1 with (vg ++ EA5 ++ rp EJ5 0 ++ uj). change Jc with (vj ++ uj).
  change G2 with (vj ++ EB5 ++ rp EQ5 0 ++ uq). change Qc with (vq ++ uq).
  change Gw with (vq ++ EE5 ++ w5).
  rewrite app_nil_r, <- ?app_assoc. reflexivity.
Qed.

(** ** Runs and cycles, round by round *)

Definition rl (rounds : nat) (st : sst) (F : list bool) : list (Z * nat) :=
  match crun rounds 4 (addpost st F) with Some (_, l) => l | None => [] end.

Definition lG0 : list (Z * nat) := Eval vm_compute in rl 5 st50 G0.
Definition lGc : list (Z * nat) := Eval vm_compute in rl 1 SG Gc.
Definition lG1 : list (Z * nat) := Eval vm_compute in rl 6 SG G1.
Definition lJc : list (Z * nat) := Eval vm_compute in rl 4 SJ Jc.
Definition lG2 : list (Z * nat) := Eval vm_compute in rl 16 SJ G2.
Definition lQc : list (Z * nat) := Eval vm_compute in rl 17 SQ Qc.

Lemma RG0 : Run st50 G0 SG (pSh lG0) (pV lG0).
Proof. apply (crun_run 5 4). vm_compute. reflexivity. Qed.

Lemma CG : Run SG Gc SG (pSh lGc) (pV lGc).
Proof. apply (crun_run 1 4). vm_compute. reflexivity. Qed.

Lemma RG1 : Run SG G1 SJ (pSh lG1) (pV lG1).
Proof. apply (crun_run 6 4). vm_compute. reflexivity. Qed.

Lemma CJ : Run SJ Jc SJ (pSh lJc) (pV lJc).
Proof. apply (crun_run 4 4). vm_compute. reflexivity. Qed.

Lemma RG2 : Run SJ G2 SQ (pSh lG2) (pV lG2).
Proof. apply (crun_run 16 4). vm_compute. reflexivity. Qed.

Lemma CQ : Run SQ Qc SQ (pSh lQc) (pV lQc).
Proof. apply (crun_run 17 4). vm_compute. reflexivity. Qed.

Definition segs5 (ng nj nq : nat) : list seg :=
  [SP lG0; SK lGc ng; SP lG1; SK lJc nj; SP lG2; SK lQc nq].

Lemma runA5 : forall ng nj nq,
  Run st50 (G0 ++ rp Gc ng ++ G1 ++ rp Jc nj ++ G2 ++ rp Qc nq ++ []) SQ
      (segSh (segs5 ng nj nq)) (segV (segs5 ng nj nq)).
Proof.
  intros ng nj nq. unfold segs5.
  exact (run_SP _ _ _ _ _ _ _ RG0 (run_SK _ _ _ _ _ _ _ CG
          (run_SP _ _ _ _ _ _ _ RG1 (run_SK _ _ _ _ _ _ _ CJ
            (run_SP _ _ _ _ _ _ _ RG2 (run_SK _ _ _ _ _ _ _ CQ (run_end _))))))).
Qed.

(** ** The carry chain *)

Definition as5 := Eval vm_compute in asm 0 (segs5 0 0 0).
Definition k0 : list bool := Eval vm_compute in match as5 with Some ([Lit a; _; _; _; _; _], _) => a | _ => [] end.
Definition kg : list bool := Eval vm_compute in match as5 with Some ([_; Rep p _; _; _; _; _], _) => p | _ => [] end.
Definition k1 : list bool := Eval vm_compute in match as5 with Some ([_; _; Lit a; _; _; _], _) => a | _ => [] end.
Definition kj : list bool := Eval vm_compute in match as5 with Some ([_; _; _; Rep p _; _; _], _) => p | _ => [] end.
Definition k2 : list bool := Eval vm_compute in match as5 with Some ([_; _; _; _; Lit a; _], _) => a | _ => [] end.
Definition kq : list bool := Eval vm_compute in match as5 with Some ([_; _; _; _; _; Rep p _], _) => p | _ => [] end.
Definition cB : Z := Eval vm_compute in match as5 with Some (_, c) => c | None => (-1)%Z end.

Lemma as5_ok : forall ng nj nq,
  asm 0 (segs5 ng nj nq) = Some ([Lit k0; Rep kg ng; Lit k1; Rep kj nj; Lit k2; Rep kq nq], cB).
Proof. intros ng nj nq. vm_compute. reflexivity. Qed.

(** ** The closing computation *)

Definition ec5 := Eval vm_compute in endcert 3000 (addpost SQ Gw).
Definition ae5 : Z := Eval vm_compute in match ec5 with Some (a, _, _, _) => a | None => 0%Z end.
Definition z1_5 : nat := Eval vm_compute in match ec5 with Some (_, z, _, _) => z | None => O end.
Definition z2_5 : nat := Eval vm_compute in match ec5 with Some (_, _, z, _) => z | None => O end.
Definition w6 : list bool := Eval vm_compute in match ec5 with Some (_, _, _, x) => x | None => [] end.
Definition la5 : nat := Eval vm_compute in (z1_5 + z2_5 - 1) / 3.
Definition tp5 : N := Eval vm_compute in Z.to_N ((cB + ae5) / 4 ^ Z.of_nat la5).
Definition ab5 : list bool := Eval vm_compute in zbits ((cB + ae5) mod 4 ^ Z.of_nat la5) (2 * la5).

Lemma ec5_ok : endcert 3000 (addpost SQ Gw) = Some (ae5, z1_5, z2_5, w6).
Proof. vm_compute. reflexivity. Qed.

Lemma cB_nn : (0 <= cB)%Z.
Proof. apply Z.leb_le. vm_compute. reflexivity. Qed.

Lemma ab5_val : (Z.of_N (bvalN ab5) + Z.of_N tp5 * pw4 la5 = cB + ae5)%Z.
Proof. vm_compute. reflexivity. Qed.

Lemma ab5_len : length ab5 = 2 * la5.
Proof. vm_compute. reflexivity. Qed.

Lemma z_5 : z1_5 + z2_5 = 3 * la5 + 1.
Proof. vm_compute. reflexivity. Qed.

Definition C5 (ng nj nq : nat) : list bool :=
  den [Lit k0; Rep kg ng; Lit k1; Rep kj nj; Lit k2; Rep kq nq] ++ ab5.
Definition lc5 (ng nj nq : nat) : nat := segSh (segs5 ng nj nq) + la5.

Lemma C5_len : forall ng nj nq, length (C5 ng nj nq) = 2 * lc5 ng nj nq.
Proof.
  intros ng nj nq.
  exact (proj1 (stageA st50 _ SQ (segs5 ng nj nq) 3000 Gw ae5 z1_5 z2_5 w6 _ cB ab5 la5 (Z.of_N tp5)
                  (runA5 ng nj nq) ec5_ok (as5_ok ng nj nq) cB_nn ab5_val ab5_len z_5)).
Qed.

Lemma end5 : forall ng nj nq h k, (1 <= k)%nat -> exists n M',
  tickN 3 n (rep10 k ++ c1101 ++ repeat true (3 * h) ++ rep10 3 ++ c1101 ++
             encb false (b5 (ng + 4) (nj + 1) (nq + 1)) ++ w5) =
    Some (Slev M' (3 * (h + lc5 ng nj nq) + 1) w6) /\
  Z.of_nat M' = (Z.of_nat k +
                 (Z.of_nat (bval (C5 ng nj nq)) + Z.of_N tp5 * pw4 (lc5 ng nj nq)) * pw4 h)%Z.
Proof.
  intros ng nj nq h k Hk.
  destruct (stageA st50 _ SQ (segs5 ng nj nq) 3000 Gw ae5 z1_5 z2_5 w6 _ cB ab5 la5 (Z.of_N tp5)
              (runA5 ng nj nq) ec5_ok (as5_ok ng nj nq) cB_nn ab5_val ab5_len z_5) as [_ H].
  destruct (H h k Hk) as [n [M' [E D]]]. exists n, M'. split; [| exact D].
  change (rep10 3 ++ c1101 ++ encb false (b5 (ng + 4) (nj + 1) (nq + 1)) ++ w5)
    with (cells5 (ng + 4) (nj + 1) (nq + 1)).
  rewrite cells5_cut.
  cbv [st50 conc] in E. rewrite ?app_nil_r, <- ?app_assoc in E. rewrite ?app_nil_r, <- ?app_assoc.
  exact E.
Qed.

(** ** Residues of the counts

    The level-5 word needs all three counts modulo 3.  Two of them are values of lower
    quotient words, which are divided once more. *)

Lemma tt3_reblock : forall q, tt3 (q * 3 + 1) = den [Lit ttl3; Rep (rp ttP3 3) q; Lit (rp ttP3 1 ++ tth3)].
Proof. intro q. unfold tt3. cbn [den bden]. rewrite rp_add, rp_mul, <- ?app_assoc. reflexivity. Qed.

Definition dvtt3 := Eval vm_compute in dmB 3 [Lit ttl3; Rep (rp ttP3 3) O; Lit (rp ttP3 1 ++ tth3)] 0.
Definition x3l : list bool := Eval vm_compute in match dvtt3 with Some ([Lit a; _; _], _) => a | _ => [] end.
Definition x3P : list bool := Eval vm_compute in match dvtt3 with Some ([_; Rep p _; _], _) => p | _ => [] end.
Definition x3h : list bool := Eval vm_compute in match dvtt3 with Some ([_; _; Lit a], _) => a | _ => [] end.

Lemma dvtt3_ok : forall q,
  dmB 3 [Lit ttl3; Rep (rp ttP3 3) q; Lit (rp ttP3 1 ++ tth3)] 0 = Some ([Lit x3l; Rep x3P q; Lit x3h], 2%N).
Proof. intro q. vm_compute. reflexivity. Qed.

Definition ttt3 (q : nat) : list bool := den [Lit x3l; Rep x3P q; Lit x3h].

Lemma tt3_mod : forall q, bval (tt3 (q * 3 + 1)) = 3 * bval (ttt3 q) + 2.
Proof.
  intro q. pose proof (dmB_sound _ _ _ _ _ (dvtt3_ok q)) as H. rewrite <- tt3_reblock in H.
  assert (H03 : (0 < 3)%N) by reflexivity.
  destruct (dm_spec 3 _ 0 _ _ H03 H) as [He _]. unfold ttt3. lia.
Qed.

Lemma t4_reblock : forall a q,
  t4 (a * 3) (q * 3) =
  den [Lit t4a; Rep (rp t4Pj 3) a; Lit (rp t4Pj 1 ++ t4m); Rep (rp t4Pq 3) q; Lit (rp t4Pq 1 ++ t4e)].
Proof.
  intros a q. unfold t4. cbn [den bden]. rewrite !rp_add, !rp_mul, <- ?app_assoc. reflexivity.
Qed.

Definition dvt4 := Eval vm_compute in
  dmB 3 [Lit t4a; Rep (rp t4Pj 3) O; Lit (rp t4Pj 1 ++ t4m); Rep (rp t4Pq 3) O; Lit (rp t4Pq 1 ++ t4e)] 0.
Definition x4a : list bool := Eval vm_compute in match dvt4 with Some ([Lit a; _; _; _; _], _) => a | _ => [] end.
Definition x4Pj : list bool := Eval vm_compute in match dvt4 with Some ([_; Rep p _; _; _; _], _) => p | _ => [] end.
Definition x4m : list bool := Eval vm_compute in match dvt4 with Some ([_; _; Lit a; _; _], _) => a | _ => [] end.
Definition x4Pq : list bool := Eval vm_compute in match dvt4 with Some ([_; _; _; Rep p _; _], _) => p | _ => [] end.
Definition x4e : list bool := Eval vm_compute in match dvt4 with Some ([_; _; _; _; Lit a], _) => a | _ => [] end.

Lemma dvt4_ok : forall a q,
  dmB 3 [Lit t4a; Rep (rp t4Pj 3) a; Lit (rp t4Pj 1 ++ t4m); Rep (rp t4Pq 3) q; Lit (rp t4Pq 1 ++ t4e)] 0 =
  Some ([Lit x4a; Rep x4Pj a; Lit x4m; Rep x4Pq q; Lit x4e], 0%N).
Proof. intros a q. vm_compute. reflexivity. Qed.

Definition tt4 (a q : nat) : list bool := den [Lit x4a; Rep x4Pj a; Lit x4m; Rep x4Pq q; Lit x4e].

Lemma t4_mod : forall a q, bval (t4 (a * 3) (q * 3)) = 3 * bval (tt4 a q).
Proof.
  intros a q. pose proof (dmB_sound _ _ _ _ _ (dvt4_ok a q)) as H. rewrite <- t4_reblock in H.
  assert (H03 : (0 < 3)%N) by reflexivity.
  destruct (dm_spec 3 _ 0 _ _ H03 H) as [He _]. unfold tt4. lia.
Qed.

Lemma tt4_pos : forall a q, 1 <= bval (tt4 a q).
Proof.
  intros a q. unfold tt4. cbn [den bden].
  assert (Hh : (1 <= bvalN (x4e ++ []))%N) by (apply N.leb_le; vm_compute; reflexivity).
  pose proof (bvalN_spec (x4e ++ [])) as Hs.
  pose proof (bval_app_ge x4a (rp x4Pj a ++ x4m ++ rp x4Pq q ++ x4e ++ [])) as H1.
  pose proof (bval_app_ge (rp x4Pj a) (x4m ++ rp x4Pq q ++ x4e ++ [])) as H2.
  pose proof (bval_app_ge x4m (rp x4Pq q ++ x4e ++ [])) as H3.
  pose proof (bval_app_ge (rp x4Pq q) (x4e ++ [])) as H4. lia.
Qed.

Lemma b5_reblock : forall ng' nj' nq',
  b5 (ng' * 3 + 2 + 4) (nj' * 3 + 2 + 1) (nq' * 3 + 2 + 1) =
  den [Lit a5; Rep (rp Pg5 3) (ng' + 2); Lit m5a; Rep (rp Pj5 3) (nj' + 1); Lit m5b;
       Rep (rp Pq5 3) (nq' + 1); Lit e5].
Proof.
  intros ng' nj' nq'. replace (ng' * 3 + 2 + 4) with ((ng' + 2) * 3) by lia.
  replace (nj' * 3 + 2 + 1) with ((nj' + 1) * 3) by lia.
  replace (nq' * 3 + 2 + 1) with ((nq' + 1) * 3) by lia.
  unfold b5. cbn [den bden]. rewrite !rp_mul. reflexivity.
Qed.

Definition dvT5 := Eval vm_compute in
  dmB 3 [Lit a5; Rep (rp Pg5 3) O; Lit m5a; Rep (rp Pj5 3) O; Lit m5b; Rep (rp Pq5 3) O; Lit e5] 0.
Definition t5a : list bool := Eval vm_compute in match dvT5 with Some ([Lit a; _; _; _; _; _; _], _) => a | _ => [] end.
Definition t5Pg : list bool := Eval vm_compute in match dvT5 with Some ([_; Rep p _; _; _; _; _; _], _) => p | _ => [] end.
Definition t5m : list bool := Eval vm_compute in match dvT5 with Some ([_; _; Lit a; _; _; _; _], _) => a | _ => [] end.
Definition t5Pj : list bool := Eval vm_compute in match dvT5 with Some ([_; _; _; Rep p _; _; _; _], _) => p | _ => [] end.
Definition t5n : list bool := Eval vm_compute in match dvT5 with Some ([_; _; _; _; Lit a; _; _], _) => a | _ => [] end.
Definition t5Pq : list bool := Eval vm_compute in match dvT5 with Some ([_; _; _; _; _; Rep p _; _], _) => p | _ => [] end.
Definition t5e : list bool := Eval vm_compute in match dvT5 with Some ([_; _; _; _; _; _; Lit a], _) => a | _ => [] end.

Lemma dvT5_ok : forall a b c,
  dmB 3 [Lit a5; Rep (rp Pg5 3) a; Lit m5a; Rep (rp Pj5 3) b; Lit m5b; Rep (rp Pq5 3) c; Lit e5] 0 =
  Some ([Lit t5a; Rep t5Pg a; Lit t5m; Rep t5Pj b; Lit t5n; Rep t5Pq c; Lit t5e], 2%N).
Proof. intros a b c. vm_compute. reflexivity. Qed.

Definition t5 (ng' nj' nq' : nat) : list bool :=
  den [Lit t5a; Rep t5Pg (ng' + 2); Lit t5m; Rep t5Pj (nj' + 1); Lit t5n; Rep t5Pq (nq' + 1); Lit t5e].

Lemma T5_mod : forall ng' nj' nq',
  bval (b5 (ng' * 3 + 2 + 4) (nj' * 3 + 2 + 1) (nq' * 3 + 2 + 1)) = 3 * bval (t5 ng' nj' nq') + 2.
Proof.
  intros ng' nj' nq'.
  pose proof (dmB_sound _ _ _ _ _ (dvT5_ok (ng' + 2) (nj' + 1) (nq' + 1))) as H.
  rewrite <- b5_reblock in H.
  assert (H03 : (0 < 3)%N) by reflexivity.
  destruct (dm_spec 3 _ 0 _ _ H03 H) as [He _]. unfold t5. lia.
Qed.

Definition G5 (ng' nj' nq' : nat) : nat := 2 * bval (t5 ng' nj' nq') + 1.

Lemma h5_eq : forall ng' nj' nq',
  2 * bval (b5 (ng' * 3 + 2 + 4) (nj' * 3 + 2 + 1) (nq' * 3 + 2 + 1)) = G5 ng' nj' nq' * 3 + 1.
Proof. intros ng' nj' nq'. rewrite T5_mod. unfold G5. lia. Qed.

(** ** The division *)

Lemma Zl5_den : forall ng nj' nq G,
  [false; false; true; false] ++ rep01 (G * 3 + 1) ++ C5 ng (nj' * 3 + 2) nq =
  den [Lit [false; false; true; false]; Rep (rp [false; true] 3) G; Lit (rp [false; true] 1 ++ k0);
       Rep kg ng; Lit k1; Rep (rp kj 3) nj'; Lit (rp kj 2 ++ k2); Rep kq nq; Lit ab5].
Proof.
  intros ng nj' nq G. unfold C5. cbn [den bden].
  change (rep01 (G * 3 + 1)) with (rp [false; true] (G * 3 + 1)).
  rewrite !rp_add, !rp_mul, ?app_nil_r, <- ?app_assoc. reflexivity.
Qed.

Definition dv5 := Eval vm_compute in
  dmB 3 [Lit [false; false; true; false]; Rep (rp [false; true] 3) O; Lit (rp [false; true] 1 ++ k0);
         Rep kg O; Lit k1; Rep (rp kj 3) O; Lit (rp kj 2 ++ k2); Rep kq O; Lit ab5] tp5.
Definition a6 : list bool := Eval vm_compute in match dv5 with Some ([Lit a; _; _; _; _; _; _; _; _], _) => a | _ => [] end.
Definition P6z : list bool := Eval vm_compute in match dv5 with Some ([_; Rep p _; _; _; _; _; _; _; _], _) => p | _ => [] end.
Definition m6a : list bool := Eval vm_compute in match dv5 with Some ([_; _; Lit a; _; _; _; _; _; _], _) => a | _ => [] end.
Definition P6g : list bool := Eval vm_compute in match dv5 with Some ([_; _; _; Rep p _; _; _; _; _; _], _) => p | _ => [] end.
Definition m6b : list bool := Eval vm_compute in match dv5 with Some ([_; _; _; _; Lit a; _; _; _; _], _) => a | _ => [] end.
Definition P6j : list bool := Eval vm_compute in match dv5 with Some ([_; _; _; _; _; Rep p _; _; _; _], _) => p | _ => [] end.
Definition m6c : list bool := Eval vm_compute in match dv5 with Some ([_; _; _; _; _; _; Lit a; _; _], _) => a | _ => [] end.
Definition P6q : list bool := Eval vm_compute in match dv5 with Some ([_; _; _; _; _; _; _; Rep p _; _], _) => p | _ => [] end.
Definition e6 : list bool := Eval vm_compute in match dv5 with Some ([_; _; _; _; _; _; _; _; Lit a], _) => a | _ => [] end.
Definition r6 : N := Eval vm_compute in match dv5 with Some (_, r) => r | None => 0%N end.

Lemma dv5_ok : forall G ng nj' nq,
  dmB 3 [Lit [false; false; true; false]; Rep (rp [false; true] 3) G; Lit (rp [false; true] 1 ++ k0);
         Rep kg ng; Lit k1; Rep (rp kj 3) nj'; Lit (rp kj 2 ++ k2); Rep kq nq; Lit ab5] tp5 =
  Some ([Lit a6; Rep P6z G; Lit m6a; Rep P6g ng; Lit m6b; Rep P6j nj'; Lit m6c; Rep P6q nq; Lit e6], r6).
Proof. intros G ng nj' nq. vm_compute. reflexivity. Qed.

Lemma tp5_lt : (tp5 < 3)%N.
Proof. reflexivity. Qed.

(** ** Level 6 *)

Definition b6 (G ng nj' nq : nat) : list bool :=
  den [Lit a6; Rep P6z G; Lit m6a; Rep P6g ng; Lit m6b; Rep P6j nj'; Lit m6c; Rep P6q nq; Lit e6].

Theorem lvl6_gen : forall ng' nj' nq' u,
  Lvl 3 (b5 (ng' * 3 + 2 + 4) (nj' * 3 + 2 + 1) (nq' * 3 + 2 + 1)) u w5 ->
  Lvl (3 + N.to_nat r6) (b6 (G5 ng' nj' nq') (ng' * 3 + 2) nj' (nq' * 3 + 2))
      (2 + 2 * bval (b5 (ng' * 3 + 2 + 4) (nj' * 3 + 2 + 1) (nq' * 3 + 2 + 1)) +
       lc5 (ng' * 3 + 2) (nj' * 3 + 2) (nq' * 3 + 2)) w6.
Proof.
  intros ng' nj' nq' u H.
  apply (level_next_top 3 (b5 (ng' * 3 + 2 + 4) (nj' * 3 + 2 + 1) (nq' * 3 + 2 + 1)) u w5
           (C5 (ng' * 3 + 2) (nj' * 3 + 2) (nq' * 3 + 2)) (lc5 (ng' * 3 + 2) (nj' * 3 + 2) (nq' * 3 + 2))
           tp5 (b6 (G5 ng' nj' nq') (ng' * 3 + 2) nj' (nq' * 3 + 2)) r6 w6 H (C5_len _ _ _) tp5_lt
           (fun k Hk => end5 _ _ _ _ k Hk)).
  rewrite h5_eq, Zl5_den. apply dmB_sound. apply dv5_ok.
Qed.

(** The real chain. *)
Definition q6 : nat := N.to_nat 105001%N.
Definition X6 : nat := bval (ttt3 q6).
Definition Y6 : nat := bval (tt4 (2 * X6 + 1) q6).
Definition ngr : nat := 2 * Y6 - 2.
Definition njr : nat := 2 * X6.
Definition nqr : nat := N.to_nat 105000%N.
Definition u6 : nat :=
  2 + 2 * bval (b5 (ngr * 3 + 2 + 4) (njr * 3 + 2 + 1) (nqr * 3 + 2 + 1)) +
  lc5 (ngr * 3 + 2) (njr * 3 + 2) (nqr * 3 + 2).

Theorem lvl6 : Lvl (3 + N.to_nat r6) (b6 (G5 ngr njr nqr) (ngr * 3 + 2) njr (nqr * 3 + 2)) u6 w6.
Proof.
  assert (EX : bval (tt3 q5) = 3 * X6 + 2).
  { replace q5 with (q6 * 3 + 1) by (unfold q5, q6; lia). apply tt3_mod. }
  assert (Ej : n1r = njr * 3 + 2 + 1) by (unfold n1r, njr; lia).
  assert (Eq : n2r = nqr * 3 + 2 + 1) by (unfold n2r, nqr; lia).
  assert (Eg : g4 n1r n2r = ngr * 3 + 2 + 4).
  { unfold g4. unfold njr in Ej.
    replace n1r with ((2 * X6 + 1) * 3) by lia.
    replace n2r with (q6 * 3) by (unfold n2r, q6; lia).
    rewrite t4_mod. pose proof (tt4_pos (2 * X6 + 1) q6). unfold ngr, Y6. lia. }
  pose proof lvl5 as H. rewrite Eg, Ej, Eq in H. exact (lvl6_gen ngr njr nqr _ H).
Qed.

End L56.

Module L6i.

(** * 1RB1LB_1RC0RD_0LA1RE_0RF1LC_1LA0RB_---1LC: level 6, counts and residues

    The four counts of the level-6 word as constants, their residues modulo [3^8] (by the
    residue evaluator [resW]), lower bounds, and the value of the word modulo [3^8].  The later
    level files use a level only through statements of this form. *)

Import Individual62.
Import T694_levels End694 Sym694 Lev694 Lvl1_694 Eng694 Cert694 Run694 L23 L34 L45 L56.
Import Res694 Gen694.
Import Lia Arith PeanoNat Bool NArith ZArith.
Import Coq.Lists.List.
Import ListNotations.

(** ** The quotient words of the lower levels modulo 3^8 *)

Definition vX6 : Z := Eval vm_compute in
  gv (resW 6561 [RL x3l; RR x3P 6561 (105001 mod 6561); RL x3h]).

Lemma X6_res : (Z.of_nat X6 mod 6561 = vX6)%Z.
Proof.
  unfold X6, ttt3.
  apply (resW_sound 6561 [Lit x3l; Rep x3P q6; Lit x3h] [RL x3l; RR x3P 6561 (105001 mod 6561); RL x3h]);
    [lia | | vm_compute; reflexivity].
  exact (Forall2_cons _ _ (mL x3l) (Forall2_cons _ _ (mblk_lit x3P 105001 6561 eq_refl)
           (Forall2_cons _ _ (mL x3h) (Forall2_nil _)))).
Qed.

Definition rA6 : N := Eval vm_compute in Z.to_N ((2 * vX6 + 1) mod 6561).

Lemma A6_res : (Z.of_nat (2 * X6 + 1) mod Z.of_N 6561 = Z.of_N rA6)%Z.
Proof. pose proof X6_res as H. unfold vX6 in H. unfold rA6. cbn [Z.of_N]. gl X6. Qed.

Lemma Q6_res : (Z.of_nat (nqr + 1) mod Z.of_N 6561 = Z.of_N (105001 mod 6561))%Z.
Proof. unfold nqr. rewrite Nat2Z.inj_add, N_nat_Z. vm_compute. reflexivity. Qed.

Definition vY6 : Z := Eval vm_compute in
  gv (resW 6561 [RL x4a; RR x4Pj 6561 rA6; RL x4m; RR x4Pq 6561 (105001 mod 6561); RL x4e]).

Lemma Y6_res : (Z.of_nat Y6 mod 6561 = vY6)%Z.
Proof.
  unfold Y6, tt4.
  apply (resW_sound 6561 [Lit x4a; Rep x4Pj (2 * X6 + 1); Lit x4m; Rep x4Pq q6; Lit x4e]
           [RL x4a; RR x4Pj 6561 rA6; RL x4m; RR x4Pq 6561 (105001 mod 6561); RL x4e]);
    [lia | | vm_compute; reflexivity].
  exact (Forall2_cons _ _ (mL x4a) (Forall2_cons _ _ (mR x4Pj (2 * X6 + 1) 6561%N rA6 A6_res)
           (Forall2_cons _ _ (mL x4m) (Forall2_cons _ _ (mblk_lit x4Pq 105001 6561 eq_refl)
             (Forall2_cons _ _ (mL x4e) (Forall2_nil _)))))).
Qed.

Lemma Y6_pos : 1 <= Y6.
Proof. exact (tt4_pos (2 * X6 + 1) q6). Qed.

Definition rB6 : N := Eval vm_compute in Z.to_N ((2 * vY6) mod 6561).

Lemma B6_res : (Z.of_nat (ngr + 2) mod Z.of_N 6561 = Z.of_N rB6)%Z.
Proof.
  pose proof Y6_res as H. pose proof Y6_pos as Hp. unfold vY6 in H. unfold ngr, rB6. cbn [Z.of_N]. gl Y6.
Qed.

Lemma J6_res : (Z.of_nat (njr + 1) mod Z.of_N 6561 = Z.of_N rA6)%Z.
Proof. unfold njr. exact A6_res. Qed.

Definition vt5 : Z := Eval vm_compute in
  gv (resW 6561 [RL t5a; RR t5Pg 6561 rB6; RL t5m; RR t5Pj 6561 rA6; RL t5n;
                 RR t5Pq 6561 (105001 mod 6561); RL t5e]).

Lemma t5_res : (Z.of_nat (bval (t5 ngr njr nqr)) mod 6561 = vt5)%Z.
Proof.
  unfold t5.
  apply (resW_sound 6561
           [Lit t5a; Rep t5Pg (ngr + 2); Lit t5m; Rep t5Pj (njr + 1); Lit t5n; Rep t5Pq (nqr + 1); Lit t5e]
           [RL t5a; RR t5Pg 6561 rB6; RL t5m; RR t5Pj 6561 rA6; RL t5n;
            RR t5Pq 6561 (105001 mod 6561); RL t5e]);
    [lia | | vm_compute; reflexivity].
  exact (Forall2_cons _ _ (mL t5a) (Forall2_cons _ _ (mR t5Pg (ngr + 2) 6561%N rB6 B6_res)
           (Forall2_cons _ _ (mL t5m) (Forall2_cons _ _ (mR t5Pj (njr + 1) 6561%N rA6 J6_res)
             (Forall2_cons _ _ (mL t5n)
               (Forall2_cons _ _ (mR t5Pq (nqr + 1) 6561%N (105001 mod 6561)%N Q6_res)
                 (Forall2_cons _ _ (mL t5e) (Forall2_nil _)))))))).
Qed.

(** ** The counts of level 6 *)

Definition c6_1 : nat := G5 ngr njr nqr.
Definition c6_2 : nat := ngr * 3 + 2.
Definition c6_3 : nat := njr.
Definition c6_4 : nat := nqr * 3 + 2.

Theorem lvl6i : Lvl 3 (b6 c6_1 c6_2 c6_3 c6_4) u6 w6.
Proof. exact lvl6. Qed.

Definition rc6_1 : N := Eval vm_compute in Z.to_N ((2 * vt5 + 1) mod 6561).
Definition rc6_2 : N := Eval vm_compute in Z.to_N ((3 * (2 * vY6 - 2) + 2) mod 6561).
Definition rc6_3 : N := Eval vm_compute in Z.to_N ((2 * vX6) mod 6561).
Definition rc6_4 : N := Eval vm_compute in (315002 mod 6561)%N.

Lemma c6_1_res : (Z.of_nat c6_1 mod Z.of_N 6561 = Z.of_N rc6_1)%Z.
Proof. pose proof t5_res as H. unfold vt5 in H. unfold c6_1, G5, rc6_1. cbn [Z.of_N]. gl (bval (t5 ngr njr nqr)). Qed.

Lemma c6_2_res : (Z.of_nat c6_2 mod Z.of_N 6561 = Z.of_N rc6_2)%Z.
Proof.
  pose proof Y6_res as H. pose proof Y6_pos as Hp. unfold vY6 in H. unfold c6_2, ngr, rc6_2.
  cbn [Z.of_N]. gl Y6.
Qed.

Lemma c6_3_res : (Z.of_nat c6_3 mod Z.of_N 6561 = Z.of_N rc6_3)%Z.
Proof. pose proof X6_res as H. unfold vX6 in H. unfold c6_3, njr, rc6_3. cbn [Z.of_N]. gl X6. Qed.

Lemma c6_4_res : (Z.of_nat c6_4 mod Z.of_N 6561 = Z.of_N rc6_4)%Z.
Proof. unfold c6_4, nqr, rc6_4. rewrite Nat2Z.inj_add, Nat2Z.inj_mul, N_nat_Z. vm_compute. reflexivity. Qed.

(** ** Lower bounds *)

Definition lbX6 : N := Eval vm_compute in bvalN x3h.
Definition lbY6 : N := Eval vm_compute in bvalN x4e.
Definition lbt5 : N := Eval vm_compute in bvalN t5e.

Lemma X6_lb : (Z.of_N lbX6 <= Z.of_nat X6)%Z.
Proof. unfold X6, ttt3. exact (lbZ [Lit x3l; Rep x3P q6] x3h). Qed.

Lemma Y6_lb : (Z.of_N lbY6 <= Z.of_nat Y6)%Z.
Proof. unfold Y6, tt4. exact (lbZ [Lit x4a; Rep x4Pj (2 * X6 + 1); Lit x4m; Rep x4Pq q6] x4e). Qed.

Lemma t5_lb : (Z.of_N lbt5 <= Z.of_nat (bval (t5 ngr njr nqr)))%Z.
Proof.
  unfold t5.
  exact (lbZ [Lit t5a; Rep t5Pg (ngr + 2); Lit t5m; Rep t5Pj (njr + 1); Lit t5n; Rep t5Pq (nqr + 1)] t5e).
Qed.

Definition lb6_1 : N := Eval vm_compute in (2 * lbt5 + 1)%N.
Definition lb6_2 : N := Eval vm_compute in (3 * (2 * lbY6 - 2) + 2)%N.
Definition lb6_3 : N := Eval vm_compute in (2 * lbX6)%N.
Definition lb6_4 : N := 315002%N.

Lemma c6_1_lb : (Z.of_N lb6_1 <= Z.of_nat c6_1)%Z.
Proof. pose proof t5_lb as H. unfold lbt5 in H. unfold c6_1, G5, lb6_1. cbn [Z.of_N] in *. gl (bval (t5 ngr njr nqr)). Qed.

Lemma c6_2_lb : (Z.of_N lb6_2 <= Z.of_nat c6_2)%Z.
Proof. pose proof Y6_lb as H. unfold lbY6 in H. unfold c6_2, ngr, lb6_2. cbn [Z.of_N] in *. gl Y6. Qed.

Lemma c6_3_lb : (Z.of_N lb6_3 <= Z.of_nat c6_3)%Z.
Proof. pose proof X6_lb as H. unfold lbX6 in H. unfold c6_3, njr, lb6_3. cbn [Z.of_N] in *. gl X6. Qed.

Lemma c6_4_lb : (Z.of_N lb6_4 <= Z.of_nat c6_4)%Z.
Proof. unfold c6_4, nqr, lb6_4. rewrite Nat2Z.inj_add, Nat2Z.inj_mul, N_nat_Z. vm_compute. intro HH; discriminate HH. Qed.

(** ** The counts modulo 32

    A block whose cycle is two copies long needs its count modulo 2.  The low literal of a
    block word has 4 bits, so the word is known modulo 16. *)

Definition tX6 : N := Eval vm_compute in bvalN x3l.
Definition tY6 : N := Eval vm_compute in bvalN x4a.
Definition tt5 : N := Eval vm_compute in bvalN t5a.

Lemma X6_low : (Z.of_nat X6 mod 16 = Z.of_N tX6)%Z.
Proof. unfold X6, ttt3. exact (bval_low_den x3l [Rep x3P q6; Lit x3h]). Qed.

Lemma Y6_low : (Z.of_nat Y6 mod 16 = Z.of_N tY6)%Z.
Proof.
  unfold Y6, tt4. exact (bval_low_den x4a [Rep x4Pj (2 * X6 + 1); Lit x4m; Rep x4Pq q6; Lit x4e]).
Qed.

Lemma t5_low : (Z.of_nat (bval (t5 ngr njr nqr)) mod 16 = Z.of_N tt5)%Z.
Proof.
  unfold t5.
  exact (bval_low_den t5a [Rep t5Pg (ngr + 2); Lit t5m; Rep t5Pj (njr + 1); Lit t5n; Rep t5Pq (nqr + 1); Lit t5e]).
Qed.

Definition rb6_1 : N := Eval vm_compute in ((2 * tt5 + 1) mod 32)%N.
Definition rb6_2 : N := Eval vm_compute in Z.to_N ((3 * (2 * Z.of_N tY6 - 2) + 2) mod 32).
Definition rb6_3 : N := Eval vm_compute in ((2 * tX6) mod 32)%N.
Definition rb6_4 : N := Eval vm_compute in (315002 mod 32)%N.

Lemma c6_1_res2 : (Z.of_nat c6_1 mod Z.of_N 32 = Z.of_N rb6_1)%Z.
Proof.
  pose proof t5_low as H. unfold tt5 in H. unfold c6_1, G5, rb6_1. cbn [Z.of_N] in *.
  gl (bval (t5 ngr njr nqr)).
Qed.

Lemma c6_2_res2 : (Z.of_nat c6_2 mod Z.of_N 32 = Z.of_N rb6_2)%Z.
Proof.
  pose proof Y6_low as H. pose proof Y6_pos as Hp. unfold tY6 in H. unfold c6_2, ngr, rb6_2.
  cbn [Z.of_N] in *. gl Y6.
Qed.

Lemma c6_3_res2 : (Z.of_nat c6_3 mod Z.of_N 32 = Z.of_N rb6_3)%Z.
Proof. pose proof X6_low as H. unfold tX6 in H. unfold c6_3, njr, rb6_3. cbn [Z.of_N] in *. gl X6. Qed.

Lemma c6_4_res2 : (Z.of_nat c6_4 mod Z.of_N 32 = Z.of_N rb6_4)%Z.
Proof. unfold c6_4, nqr, rb6_4. rewrite Nat2Z.inj_add, Nat2Z.inj_mul, N_nat_Z. vm_compute. reflexivity. Qed.

Definition t2_6 : N := Eval vm_compute in bvalN a6.

Lemma T6_low : forall c1 c2 c3 c4, (Z.of_nat (bval (b6 c1 c2 c3 c4)) mod 16 = Z.of_N t2_6)%Z.
Proof.
  intros c1 c2 c3 c4. unfold b6.
  exact (bval_low_den a6 [Rep P6z c1; Lit m6a; Rep P6g c2; Lit m6b; Rep P6j c3; Lit m6c; Rep P6q c4; Lit e6]).
Qed.

(** ** The word of level 6 modulo 3^8 *)

Definition vT6 : Z := Eval vm_compute in
  gv (resW 6561 [RL a6; RR P6z 6561 rc6_1; RL m6a; RR P6g 6561 rc6_2; RL m6b; RR P6j 6561 rc6_3;
                 RL m6c; RR P6q 6561 rc6_4; RL e6]).

Lemma T6_res : (Z.of_nat (bval (b6 c6_1 c6_2 c6_3 c6_4)) mod 6561 = vT6)%Z.
Proof.
  unfold b6.
  apply (resW_sound 6561
           [Lit a6; Rep P6z c6_1; Lit m6a; Rep P6g c6_2; Lit m6b; Rep P6j c6_3; Lit m6c; Rep P6q c6_4; Lit e6]
           [RL a6; RR P6z 6561 rc6_1; RL m6a; RR P6g 6561 rc6_2; RL m6b; RR P6j 6561 rc6_3;
            RL m6c; RR P6q 6561 rc6_4; RL e6]);
    [lia | | vm_compute; reflexivity].
  exact (Forall2_cons _ _ (mL a6) (Forall2_cons _ _ (mR P6z c6_1 6561%N rc6_1 c6_1_res)
           (Forall2_cons _ _ (mL m6a) (Forall2_cons _ _ (mR P6g c6_2 6561%N rc6_2 c6_2_res)
             (Forall2_cons _ _ (mL m6b) (Forall2_cons _ _ (mR P6j c6_3 6561%N rc6_3 c6_3_res)
               (Forall2_cons _ _ (mL m6c) (Forall2_cons _ _ (mR P6q c6_4 6561%N rc6_4 c6_4_res)
                 (Forall2_cons _ _ (mL e6) (Forall2_nil _)))))))))).
Qed.

Definition lbe6 : N := Eval vm_compute in bvalN e6.

Lemma T6_lb : forall c1 c2 c3 c4, (Z.of_N lbe6 <= Z.of_nat (bval (b6 c1 c2 c3 c4)))%Z.
Proof.
  intros c1 c2 c3 c4. unfold b6.
  exact (lbZ [Lit a6; Rep P6z c1; Lit m6a; Rep P6g c2; Lit m6b; Rep P6j c3; Lit m6c; Rep P6q c4] e6).
Qed.

End L6i.

Module L67a.

(** * 1RB1LB_1RC0RD_0LA1RE_0RF1LC_1LA0RB_---1LC: the end phase of level 6

    Level 6 has class 3 and a counter word with 4 repeated blocks.  The end phase is
    certified round by round ([crun_run]): a run to the first block, then for each block a
    cycle per copy and a run across the next junction, and a closing computation.  The cuts
    are computed from the rounds of one instance.  Generated by a script. *)

Import Individual62.
Import T694_levels End694 Sym694 Lev694 Lvl1_694 Eng694 Cert694 Run694 Res694 Gen694.
Import L23 L34 L45 L56 L6i.
Import Lia Arith PeanoNat Bool NArith ZArith.
Import Coq.Lists.List.
Import ListNotations.

(** ** The cells of the counter word *)

Definition pa6_0 : bool := Eval vm_compute in par false a6.
Lemma pa6_0_eq : par false a6 = pa6_0.
Proof. vm_compute. reflexivity. Qed.
Definition pa6_1 : bool := Eval vm_compute in par pa6_0 m6a.
Lemma pa6_1_eq : par pa6_0 m6a = pa6_1.
Proof. vm_compute. reflexivity. Qed.
Definition pa6_2 : bool := Eval vm_compute in par pa6_1 m6b.
Lemma pa6_2_eq : par pa6_1 m6b = pa6_2.
Proof. vm_compute. reflexivity. Qed.
Definition pa6_3 : bool := Eval vm_compute in par pa6_2 m6c.
Lemma pa6_3_eq : par pa6_2 m6c = pa6_3.
Proof. vm_compute. reflexivity. Qed.
Lemma pp6_1 : par pa6_0 P6z = pa6_0.
Proof. vm_compute. reflexivity. Qed.
Lemma pp6_2 : par pa6_1 P6g = pa6_1.
Proof. vm_compute. reflexivity. Qed.
Lemma pp6_3 : par pa6_2 P6j = pa6_2.
Proof. vm_compute. reflexivity. Qed.
Lemma pp6_4 : par pa6_3 P6q = pa6_3.
Proof. vm_compute. reflexivity. Qed.

Definition Hd6 : list bool := rep10 3 ++ c1101 ++ encb false a6.
Definition E6_1 : list bool := encb pa6_0 P6z.
Definition J6_1 : list bool := encb pa6_0 m6a.
Definition E6_2 : list bool := encb pa6_1 P6g.
Definition J6_2 : list bool := encb pa6_1 m6b.
Definition E6_3 : list bool := encb pa6_2 P6j.
Definition J6_3 : list bool := encb pa6_2 m6c.
Definition E6_4 : list bool := encb pa6_3 P6q.
Definition J6_4 : list bool := encb pa6_3 e6.

Definition cells6 (c1 c2 c3 c4 : nat) : list bool :=
  rep10 3 ++ c1101 ++ encb false (b6 c1 c2 c3 c4) ++ w6.

Lemma cells6_eq : forall c1 c2 c3 c4,
  cells6 c1 c2 c3 c4 = Hd6 ++ rp E6_1 c1 ++ J6_1 ++ rp E6_2 c2 ++ J6_2 ++ rp E6_3 c3 ++ J6_3 ++ rp
    E6_4 c4 ++ J6_4 ++ w6.
Proof.
  intros c1 c2 c3 c4. unfold cells6, b6, Hd6, E6_1, J6_1, E6_2, J6_2, E6_3, J6_3, E6_4, J6_4.
  cbn [den bden]. rewrite app_nil_r.
  rewrite (encb_app a6), pa6_0_eq.
  rewrite (encb_rp P6z pa6_0 pp6_1), (encb_app m6a), pa6_1_eq.
  rewrite (encb_rp P6g pa6_1 pp6_2), (encb_app m6b), pa6_2_eq.
  rewrite (encb_rp P6j pa6_2 pp6_3), (encb_app m6c), pa6_3_eq.
  rewrite (encb_rp P6q pa6_3 pp6_4).
  rewrite <- ?app_assoc. reflexivity.
Qed.

(** ** Boundaries, computed from the rounds of one instance *)

Definition look6_1 : nat := 36.
Definition dep6_1 : nat := 1.
Definition p6_1 : nat := Eval vm_compute in length E6_1.
Definition N6_1 : nat := Eval vm_compute in
  let b0 := (look6_1 / p6_1 + dep6_1 + 14)%nat in
  (b0 + N.to_nat ((rb6_1 + 4 * 1024 - N.of_nat b0) mod 4)%N)%nat.
Definition look6_2 : nat := 36.
Definition dep6_2 : nat := 1.
Definition p6_2 : nat := Eval vm_compute in length E6_2.
Definition N6_2 : nat := Eval vm_compute in
  let b0 := (look6_2 / p6_2 + dep6_2 + 14)%nat in
  (b0 + N.to_nat ((rb6_2 + 4 * 1024 - N.of_nat b0) mod 4)%N)%nat.
Definition look6_3 : nat := 36.
Definition dep6_3 : nat := 1.
Definition p6_3 : nat := Eval vm_compute in length E6_3.
Definition N6_3 : nat := Eval vm_compute in
  let b0 := (look6_3 / p6_3 + dep6_3 + 14)%nat in
  (b0 + N.to_nat ((rb6_3 + 4 * 1024 - N.of_nat b0) mod 4)%N)%nat.
Definition look6_4 : nat := 36.
Definition dep6_4 : nat := 1.
Definition p6_4 : nat := Eval vm_compute in length E6_4.
Definition N6_4 : nat := Eval vm_compute in
  let b0 := (look6_4 / p6_4 + dep6_4 + 14)%nat in
  (b0 + N.to_nat ((rb6_4 + 4 * 1024 - N.of_nat b0) mod 4)%N)%nat.
Definition looke6 : nat := 36.
Definition inst6 : list bool := cells6 N6_1 N6_2 N6_3 N6_4.
Definition s6_1 : N := Eval vm_compute in N.of_nat (length Hd6).
Definition s6_2 : N := Eval vm_compute in
  (s6_1 + N.of_nat (N6_1 * p6_1 + length J6_1))%N.
Definition s6_3 : N := Eval vm_compute in
  (s6_2 + N.of_nat (N6_2 * p6_2 + length J6_2))%N.
Definition s6_4 : N := Eval vm_compute in
  (s6_3 + N.of_nat (N6_3 * p6_3 + length J6_3))%N.
Definition s6_5 : N := Eval vm_compute in
  (s6_4 + N.of_nat (N6_4 * p6_4 + length J6_4))%N.
Definition tr6 : list (N * N * N) := Eval vm_compute in
  gtrace 36 (length inst6) 0 0 0 (c1101, true, inst6).
Definition f6_1 : N * N * N * N := Eval vm_compute in
  gfindk (N.of_nat p6_1) (s6_1 + N.of_nat (dep6_1 * p6_1))
         (s6_1 + N.of_nat (N6_1 * p6_1) - N.of_nat look6_1) (1%N :: 2%N :: 4%N :: nil) tr6.
Definition rr6_1 : nat := Eval vm_compute in N.to_nat (fst (fst (fst f6_1))).
Definition R6_1 : nat := Eval vm_compute in N.to_nat (snd (fst f6_1)).
Definition kq6_1 : nat := Eval vm_compute in N.to_nat (snd f6_1).
Definition cc6_1 : nat := Eval vm_compute in N.to_nat ((snd (fst (fst f6_1)) + N.of_nat look6_1 - s6_1) / N.of_nat p6_1).
Definition uu6_1 : nat := Eval vm_compute in N.to_nat ((snd (fst (fst f6_1)) + N.of_nat look6_1 - s6_1) mod N.of_nat p6_1).
Definition jj6_1 : nat := Eval vm_compute in (N6_1 - cc6_1 - 1) mod kq6_1.
Definition S6_1 : sst := Eval vm_compute in
  gcut look6_1 (grst rr6_1 (c1101, true, inst6)).
Definition f6_2 : N * N * N * N := Eval vm_compute in
  gfindk (N.of_nat p6_2) (s6_2 + N.of_nat (dep6_2 * p6_2))
         (s6_2 + N.of_nat (N6_2 * p6_2) - N.of_nat look6_2) (1%N :: 2%N :: 4%N :: nil) tr6.
Definition rr6_2 : nat := Eval vm_compute in N.to_nat (fst (fst (fst f6_2))).
Definition R6_2 : nat := Eval vm_compute in N.to_nat (snd (fst f6_2)).
Definition kq6_2 : nat := Eval vm_compute in N.to_nat (snd f6_2).
Definition cc6_2 : nat := Eval vm_compute in N.to_nat ((snd (fst (fst f6_2)) + N.of_nat look6_2 - s6_2) / N.of_nat p6_2).
Definition uu6_2 : nat := Eval vm_compute in N.to_nat ((snd (fst (fst f6_2)) + N.of_nat look6_2 - s6_2) mod N.of_nat p6_2).
Definition jj6_2 : nat := Eval vm_compute in (N6_2 - cc6_2 - 1) mod kq6_2.
Definition S6_2 : sst := Eval vm_compute in
  gcut look6_2 (grst rr6_2 (c1101, true, inst6)).
Definition f6_3 : N * N * N * N := Eval vm_compute in
  gfindk (N.of_nat p6_3) (s6_3 + N.of_nat (dep6_3 * p6_3))
         (s6_3 + N.of_nat (N6_3 * p6_3) - N.of_nat look6_3) (1%N :: 2%N :: 4%N :: nil) tr6.
Definition rr6_3 : nat := Eval vm_compute in N.to_nat (fst (fst (fst f6_3))).
Definition R6_3 : nat := Eval vm_compute in N.to_nat (snd (fst f6_3)).
Definition kq6_3 : nat := Eval vm_compute in N.to_nat (snd f6_3).
Definition cc6_3 : nat := Eval vm_compute in N.to_nat ((snd (fst (fst f6_3)) + N.of_nat look6_3 - s6_3) / N.of_nat p6_3).
Definition uu6_3 : nat := Eval vm_compute in N.to_nat ((snd (fst (fst f6_3)) + N.of_nat look6_3 - s6_3) mod N.of_nat p6_3).
Definition jj6_3 : nat := Eval vm_compute in (N6_3 - cc6_3 - 1) mod kq6_3.
Definition S6_3 : sst := Eval vm_compute in
  gcut look6_3 (grst rr6_3 (c1101, true, inst6)).
Definition f6_4 : N * N * N * N := Eval vm_compute in
  gfindk (N.of_nat p6_4) (s6_4 + N.of_nat (dep6_4 * p6_4))
         (s6_4 + N.of_nat (N6_4 * p6_4) - N.of_nat look6_4) (1%N :: 2%N :: 4%N :: nil) tr6.
Definition rr6_4 : nat := Eval vm_compute in N.to_nat (fst (fst (fst f6_4))).
Definition R6_4 : nat := Eval vm_compute in N.to_nat (snd (fst f6_4)).
Definition kq6_4 : nat := Eval vm_compute in N.to_nat (snd f6_4).
Definition cc6_4 : nat := Eval vm_compute in N.to_nat ((snd (fst (fst f6_4)) + N.of_nat look6_4 - s6_4) / N.of_nat p6_4).
Definition uu6_4 : nat := Eval vm_compute in N.to_nat ((snd (fst (fst f6_4)) + N.of_nat look6_4 - s6_4) mod N.of_nat p6_4).
Definition jj6_4 : nat := Eval vm_compute in (N6_4 - cc6_4 - 1) mod kq6_4.
Definition S6_4 : sst := Eval vm_compute in
  gcut look6_4 (grst rr6_4 (c1101, true, inst6)).
Definition fe6 : N * N := Eval vm_compute in
  glast (s6_5 - N.of_nat (looke6 + 60)) tr6 (0, 0)%N.
Definition rre6 : nat := Eval vm_compute in N.to_nat (fst fe6).
Definition ue6 : nat := Eval vm_compute in
  N.to_nat (snd fe6 + N.of_nat looke6 - (s6_4 + N.of_nat (N6_4 * p6_4))).
Definition Se6 : sst := Eval vm_compute in gcut looke6 (grst rre6 (c1101, true, inst6)).
Definition Rj6_0 : nat := rr6_1.
Definition Rj6_1 : nat := Eval vm_compute in
  rr6_2 - rr6_1 - R6_1 * ((N6_1 - cc6_1 - 1 - jj6_1) / kq6_1).
Definition Rj6_2 : nat := Eval vm_compute in
  rr6_3 - rr6_2 - R6_2 * ((N6_2 - cc6_2 - 1 - jj6_2) / kq6_2).
Definition Rj6_3 : nat := Eval vm_compute in
  rr6_4 - rr6_3 - R6_3 * ((N6_3 - cc6_3 - 1 - jj6_3) / kq6_3).
Definition Rj6_4 : nat := Eval vm_compute in
  rre6 - rr6_4 - R6_4 * ((N6_4 - cc6_4 - 1 - jj6_4) / kq6_4).

(** ** The cuts *)

Definition u6_1 : list bool := firstn uu6_1 E6_1.
Definition v6_1 : list bool := skipn uu6_1 E6_1.
Definition u6_2 : list bool := firstn uu6_2 E6_2.
Definition v6_2 : list bool := skipn uu6_2 E6_2.
Definition u6_3 : list bool := firstn uu6_3 E6_3.
Definition v6_3 : list bool := skipn uu6_3 E6_3.
Definition u6_4 : list bool := firstn uu6_4 E6_4.
Definition v6_4 : list bool := skipn uu6_4 E6_4.
Definition F6_0 : list bool := Hd6 ++ rp E6_1 cc6_1 ++ u6_1.
Definition C6_1 : list bool := v6_1 ++ u6_1.
Definition K6_1 : list bool := rp C6_1 kq6_1.
Lemma tl6_1 : rp E6_1 (jj6_1 + 1) = u6_1 ++ rp C6_1 jj6_1 ++ v6_1.
Proof. vm_compute. reflexivity. Qed.
Definition F6_1 : list bool :=
  (rp C6_1 jj6_1 ++ v6_1) ++ J6_1 ++ rp E6_2 cc6_2 ++ u6_2.
Definition C6_2 : list bool := v6_2 ++ u6_2.
Definition K6_2 : list bool := rp C6_2 kq6_2.
Lemma tl6_2 : rp E6_2 (jj6_2 + 1) = u6_2 ++ rp C6_2 jj6_2 ++ v6_2.
Proof. vm_compute. reflexivity. Qed.
Definition F6_2 : list bool :=
  (rp C6_2 jj6_2 ++ v6_2) ++ J6_2 ++ rp E6_3 cc6_3 ++ u6_3.
Definition C6_3 : list bool := v6_3 ++ u6_3.
Definition K6_3 : list bool := rp C6_3 kq6_3.
Lemma tl6_3 : rp E6_3 (jj6_3 + 1) = u6_3 ++ rp C6_3 jj6_3 ++ v6_3.
Proof. vm_compute. reflexivity. Qed.
Definition F6_3 : list bool :=
  (rp C6_3 jj6_3 ++ v6_3) ++ J6_3 ++ rp E6_4 cc6_4 ++ u6_4.
Definition C6_4 : list bool := v6_4 ++ u6_4.
Definition K6_4 : list bool := rp C6_4 kq6_4.
Lemma tl6_4 : rp E6_4 (jj6_4 + 1) = u6_4 ++ rp C6_4 jj6_4 ++ v6_4.
Proof. vm_compute. reflexivity. Qed.
Definition F6_4 : list bool := (rp C6_4 jj6_4 ++ v6_4) ++ firstn ue6 J6_4.
Definition Fw6 : list bool := skipn ue6 J6_4 ++ w6.

Lemma cells6_cut : forall n1 n2 n3 n4,
  cells6 (cc6_1 + (n1 * kq6_1 + jj6_1) + 1) (cc6_2 + (n2 * kq6_2 + jj6_2) + 1) (cc6_3 + (n3 * kq6_3 +
    jj6_3) + 1) (cc6_4 + (n4 * kq6_4 + jj6_4) + 1) = (F6_0 ++ rp K6_1 n1 ++ F6_1 ++ rp K6_2 n2 ++
    F6_2 ++ rp K6_3 n3 ++ F6_3 ++ rp K6_4 n4 ++ F6_4 ++ []) ++ Fw6.
Proof.
  intros n1 n2 n3 n4. rewrite cells6_eq.
  replace (cc6_1 + (n1 * kq6_1 + jj6_1) + 1) with (cc6_1 + n1 * kq6_1 + (jj6_1 + 1)) by lia.
  rewrite (rp_recut E6_1 u6_1 v6_1 (n1 * kq6_1) cc6_1 (jj6_1 + 1) (rp C6_1 jj6_1 ++ v6_1)
             (eq_sym (firstn_skipn uu6_1 E6_1)) tl6_1).
  rewrite (rp_mul (v6_1 ++ u6_1) kq6_1 n1).
  replace (cc6_2 + (n2 * kq6_2 + jj6_2) + 1) with (cc6_2 + n2 * kq6_2 + (jj6_2 + 1)) by lia.
  rewrite (rp_recut E6_2 u6_2 v6_2 (n2 * kq6_2) cc6_2 (jj6_2 + 1) (rp C6_2 jj6_2 ++ v6_2)
             (eq_sym (firstn_skipn uu6_2 E6_2)) tl6_2).
  rewrite (rp_mul (v6_2 ++ u6_2) kq6_2 n2).
  replace (cc6_3 + (n3 * kq6_3 + jj6_3) + 1) with (cc6_3 + n3 * kq6_3 + (jj6_3 + 1)) by lia.
  rewrite (rp_recut E6_3 u6_3 v6_3 (n3 * kq6_3) cc6_3 (jj6_3 + 1) (rp C6_3 jj6_3 ++ v6_3)
             (eq_sym (firstn_skipn uu6_3 E6_3)) tl6_3).
  rewrite (rp_mul (v6_3 ++ u6_3) kq6_3 n3).
  replace (cc6_4 + (n4 * kq6_4 + jj6_4) + 1) with (cc6_4 + n4 * kq6_4 + (jj6_4 + 1)) by lia.
  rewrite (rp_recut E6_4 u6_4 v6_4 (n4 * kq6_4) cc6_4 (jj6_4 + 1) (rp C6_4 jj6_4 ++ v6_4)
             (eq_sym (firstn_skipn uu6_4 E6_4)) tl6_4).
  rewrite (rp_mul (v6_4 ++ u6_4) kq6_4 n4).
  rewrite <- (firstn_skipn ue6 J6_4) at 1.
  unfold F6_0, K6_1, F6_1, C6_1, K6_2, F6_2, C6_2, K6_3, F6_3, C6_3, K6_4, F6_4, C6_4, Fw6.
  rewrite ?app_nil_r, <- ?app_assoc. reflexivity.
Qed.

(** ** Runs and cycles, round by round *)

Definition st60 : sst := (c1101, true, []).
Definition lF6_0 : list (Z * nat) := Eval vm_compute in grl Rj6_0 st60 F6_0.
Lemma RF6_0 : Run st60 F6_0 S6_1 (pSh lF6_0) (pV lF6_0).
Proof. apply (crun_run Rj6_0 4). vm_compute. reflexivity. Qed.
Definition lC6_1 : list (Z * nat) := Eval vm_compute in grl R6_1 S6_1 K6_1.
Lemma RC6_1 : Run S6_1 K6_1 S6_1 (pSh lC6_1) (pV lC6_1).
Proof. apply (crun_run R6_1 4). vm_compute. reflexivity. Qed.
Definition lF6_1 : list (Z * nat) := Eval vm_compute in grl Rj6_1 S6_1 F6_1.
Lemma RF6_1 : Run S6_1 F6_1 S6_2 (pSh lF6_1) (pV lF6_1).
Proof. apply (crun_run Rj6_1 4). vm_compute. reflexivity. Qed.
Definition lC6_2 : list (Z * nat) := Eval vm_compute in grl R6_2 S6_2 K6_2.
Lemma RC6_2 : Run S6_2 K6_2 S6_2 (pSh lC6_2) (pV lC6_2).
Proof. apply (crun_run R6_2 4). vm_compute. reflexivity. Qed.
Definition lF6_2 : list (Z * nat) := Eval vm_compute in grl Rj6_2 S6_2 F6_2.
Lemma RF6_2 : Run S6_2 F6_2 S6_3 (pSh lF6_2) (pV lF6_2).
Proof. apply (crun_run Rj6_2 4). vm_compute. reflexivity. Qed.
Definition lC6_3 : list (Z * nat) := Eval vm_compute in grl R6_3 S6_3 K6_3.
Lemma RC6_3 : Run S6_3 K6_3 S6_3 (pSh lC6_3) (pV lC6_3).
Proof. apply (crun_run R6_3 4). vm_compute. reflexivity. Qed.
Definition lF6_3 : list (Z * nat) := Eval vm_compute in grl Rj6_3 S6_3 F6_3.
Lemma RF6_3 : Run S6_3 F6_3 S6_4 (pSh lF6_3) (pV lF6_3).
Proof. apply (crun_run Rj6_3 4). vm_compute. reflexivity. Qed.
Definition lC6_4 : list (Z * nat) := Eval vm_compute in grl R6_4 S6_4 K6_4.
Lemma RC6_4 : Run S6_4 K6_4 S6_4 (pSh lC6_4) (pV lC6_4).
Proof. apply (crun_run R6_4 4). vm_compute. reflexivity. Qed.
Definition lF6_4 : list (Z * nat) := Eval vm_compute in grl Rj6_4 S6_4 F6_4.
Lemma RF6_4 : Run S6_4 F6_4 Se6 (pSh lF6_4) (pV lF6_4).
Proof. apply (crun_run Rj6_4 4). vm_compute. reflexivity. Qed.

Definition segs6 (n1 n2 n3 n4 : nat) : list seg :=
  [SP lF6_0; SK lC6_1 n1; SP lF6_1; SK lC6_2 n2; SP lF6_2; SK lC6_3 n3; SP lF6_3; SK lC6_4 n4; SP
    lF6_4].

Lemma runA6 : forall n1 n2 n3 n4,
  Run st60 (F6_0 ++ rp K6_1 n1 ++ F6_1 ++ rp K6_2 n2 ++ F6_2 ++ rp K6_3 n3 ++ F6_3 ++ rp K6_4 n4 ++
    F6_4 ++ []) Se6
      (segSh (segs6 n1 n2 n3 n4)) (segV (segs6 n1 n2 n3 n4)).
Proof.
  intros n1 n2 n3 n4. unfold segs6.
  exact (run_SP _ _ _ _ _ _ _ RF6_0
    (run_SK _ _ _ _ _ _ _ RC6_1
    (run_SP _ _ _ _ _ _ _ RF6_1 (run_SK _ _ _ _ _ _ _ RC6_2
    (run_SP _ _ _ _ _ _ _ RF6_2 (run_SK _ _ _ _ _ _ _ RC6_3
    (run_SP _ _ _ _ _ _ _ RF6_3 (run_SK _ _ _ _ _ _ _ RC6_4
    (run_SP _ _ _ _ _ _ _ RF6_4 (run_end _)))))))))).
Qed.

(** ** The carry chain *)

Definition as6 := Eval vm_compute in asm 0 (segs6 O O O O).
Definition k6_0 : list bool := Eval vm_compute in
  match as6 with Some ([Lit a; _; _; _; _; _; _; _; _], _) => a | _ => [] end.
Definition k6_1 : list bool := Eval vm_compute in
  match as6 with Some ([_; _; Lit a; _; _; _; _; _; _], _) => a | _ => [] end.
Definition k6_2 : list bool := Eval vm_compute in
  match as6 with Some ([_; _; _; _; Lit a; _; _; _; _], _) => a | _ => [] end.
Definition k6_3 : list bool := Eval vm_compute in
  match as6 with Some ([_; _; _; _; _; _; Lit a; _; _], _) => a | _ => [] end.
Definition k6_4 : list bool := Eval vm_compute in
  match as6 with Some ([_; _; _; _; _; _; _; _; Lit a], _) => a | _ => [] end.
Definition kk6_1 : list bool := Eval vm_compute in
  match as6 with Some ([_; Rep p _; _; _; _; _; _; _; _], _) => p | _ => [] end.
Definition kk6_2 : list bool := Eval vm_compute in
  match as6 with Some ([_; _; _; Rep p _; _; _; _; _; _], _) => p | _ => [] end.
Definition kk6_3 : list bool := Eval vm_compute in
  match as6 with Some ([_; _; _; _; _; Rep p _; _; _; _], _) => p | _ => [] end.
Definition kk6_4 : list bool := Eval vm_compute in
  match as6 with Some ([_; _; _; _; _; _; _; Rep p _; _], _) => p | _ => [] end.
Definition cB6 : Z := Eval vm_compute in match as6 with Some (_, c) => c | None => (-1)%Z end.

Lemma as6_ok : forall n1 n2 n3 n4,
  asm 0 (segs6 n1 n2 n3 n4) = Some ([Lit k6_0; Rep kk6_1 n1; Lit k6_1; Rep kk6_2 n2; Lit k6_2; Rep
    kk6_3 n3; Lit k6_3; Rep kk6_4 n4; Lit k6_4], cB6).
Proof. intros n1 n2 n3 n4. vm_compute. reflexivity. Qed.

(** ** The closing computation *)

Definition ec6 := Eval vm_compute in endcert 6000 (addpost Se6 Fw6).
Definition ae6 : Z := Eval vm_compute in match ec6 with Some (a, _, _, _) => a | None => 0%Z end.
Definition z1_6 : nat := Eval vm_compute in match ec6 with Some (_, z, _, _) => z | None => O end.
Definition z2_6 : nat := Eval vm_compute in match ec6 with Some (_, _, z, _) => z | None => O end.
Definition w7 : list bool := Eval vm_compute in match ec6 with Some (_, _, _, x) => x | None => [] end.
Definition la6 : nat := Eval vm_compute in (z1_6 + z2_6 - 1) / 3.
Definition tp6 : N := Eval vm_compute in Z.to_N ((cB6 + ae6) / 4 ^ Z.of_nat la6).
Definition ab6 : list bool := Eval vm_compute in
  zbits ((cB6 + ae6) mod 4 ^ Z.of_nat la6) (2 * la6).

Lemma ec6_ok : endcert 6000 (addpost Se6 Fw6) = Some (ae6, z1_6, z2_6, w7).
Proof. vm_compute. reflexivity. Qed.

Lemma cB6_nn : (0 <= cB6)%Z.
Proof. apply Z.leb_le. vm_compute. reflexivity. Qed.

Lemma ab6_val : (Z.of_N (bvalN ab6) + Z.of_N tp6 * pw4 la6 = cB6 + ae6)%Z.
Proof. vm_compute. reflexivity. Qed.

Lemma ab6_len : length ab6 = 2 * la6.
Proof. vm_compute. reflexivity. Qed.

Lemma z_6 : z1_6 + z2_6 = 3 * la6 + 1.
Proof. vm_compute. reflexivity. Qed.

Definition Cw6 (n1 n2 n3 n4 : nat) : list bool :=
  den [Lit k6_0; Rep kk6_1 n1; Lit k6_1; Rep kk6_2 n2; Lit k6_2; Rep kk6_3 n3; Lit k6_3; Rep kk6_4 n4;
    Lit k6_4] ++ ab6.
Definition lc6 (n1 n2 n3 n4 : nat) : nat := segSh (segs6 n1 n2 n3 n4) + la6.

Lemma Cw6_len : forall n1 n2 n3 n4, length (Cw6 n1 n2 n3 n4) = 2 * lc6 n1 n2 n3 n4.
Proof.
  intros n1 n2 n3 n4.
  exact (proj1 (stageA st60 _ Se6 (segs6 n1 n2 n3 n4) 6000 Fw6 ae6 z1_6 z2_6 w7 _ cB6 ab6 la6
              (Z.of_N tp6) (runA6 n1 n2 n3 n4) ec6_ok (as6_ok n1 n2 n3 n4) cB6_nn ab6_val ab6_len z_6)).
Qed.

Lemma end6 : forall n1 n2 n3 n4 h k, (1 <= k)%nat -> exists n M',
  tickN 3 n (rep10 k ++ c1101 ++ repeat true (3 * h) ++ rep10 3 ++ c1101 ++
             encb false (b6 (cc6_1 + (n1 * kq6_1 + jj6_1) + 1) (cc6_2 + (n2 * kq6_2 + jj6_2) + 1) (cc6_3 + (n3 *
               kq6_3 + jj6_3) + 1) (cc6_4 + (n4 * kq6_4 + jj6_4) + 1)) ++ w6) =
    Some (Slev M' (3 * (h + lc6 n1 n2 n3 n4) + 1) w7) /\
  Z.of_nat M' = (Z.of_nat k +
                 (Z.of_nat (bval (Cw6 n1 n2 n3 n4)) + Z.of_N tp6 * pw4 (lc6 n1 n2 n3 n4)) * pw4 h)%Z.
Proof.
  intros n1 n2 n3 n4 h k Hk.
  destruct (stageA st60 _ Se6 (segs6 n1 n2 n3 n4) 6000 Fw6 ae6 z1_6 z2_6 w7 _ cB6 ab6 la6
              (Z.of_N tp6) (runA6 n1 n2 n3 n4) ec6_ok (as6_ok n1 n2 n3 n4) cB6_nn ab6_val ab6_len z_6) as [_ H].
  destruct (H h k Hk) as [n [M' [E D]]]. exists n, M'. split; [| exact D].
  change (rep10 3 ++ c1101 ++ encb false (b6 (cc6_1 + (n1 * kq6_1 + jj6_1) + 1) (cc6_2 + (n2 * kq6_2 +
    jj6_2) + 1) (cc6_3 + (n3 * kq6_3 + jj6_3) + 1) (cc6_4 + (n4 * kq6_4 + jj6_4) + 1)) ++ w6)
    with (cells6 (cc6_1 + (n1 * kq6_1 + jj6_1) + 1) (cc6_2 + (n2 * kq6_2 + jj6_2) + 1) (cc6_3 + (n3 * kq6_3 + jj6_3) + 1) (cc6_4 + (n4 * kq6_4 + jj6_4) + 1)).
  rewrite cells6_cut.
  cbv [st60 conc] in E. rewrite ?app_nil_r, <- ?app_assoc in E. rewrite ?app_nil_r, <- ?app_assoc.
  exact E.
Qed.

(** ** What the division needs: which blocks are tripled, and the residues of the counts *)

Definition cfg6_trip : list bool := Eval vm_compute in
  map (fun P => negb (N.eqb (bvalN P mod 3) 0)) [kk6_1; kk6_2; kk6_3; kk6_4].
Definition cfg6_rho : list N := Eval vm_compute in
  [(((rc6_1 + 1594323 - (N.of_nat cc6_1 + 1 + N.of_nat jj6_1)%N) * (N.of_nat kq6_1 mod 3)) mod 3)%N; (((rc6_2 + 1594323 - (N.of_nat cc6_2 + 1 + N.of_nat jj6_2)%N) * (N.of_nat kq6_2 mod 3)) mod 3)%N; (((rc6_3 + 1594323 - (N.of_nat cc6_3 + 1 + N.of_nat jj6_3)%N) * (N.of_nat kq6_3 mod 3)) mod 3)%N; (((rc6_4 + 1594323 - (N.of_nat cc6_4 + 1 + N.of_nat jj6_4)%N) * (N.of_nat kq6_4 mod 3)) mod 3)%N].
Definition cfg6_k : list nat := Eval vm_compute in [kq6_1; kq6_2; kq6_3; kq6_4].
Definition cfg6_j : list nat := Eval vm_compute in [jj6_1; jj6_2; jj6_3; jj6_4].
Definition cfg6_rhoT : Z := Eval vm_compute in ((2 * vT6) mod 3)%Z.

End L67a.

Module L67b.

(** * 1RB1LB_1RC0RD_0LA1RE_0RF1LC_1LA0RB_---1LC: from level 6 to level 7

    The division by 3 of [0100 (10)^(h-2) C] with the counts as variables, level 7 for the
    real counts, and the residues modulo 3^7 and lower bounds of the counts of level 7.
    Generated by a script. *)

Import Individual62.
Import T694_levels End694 Sym694 Lev694 Lvl1_694 Eng694 Cert694 Run694 Res694 Gen694.
Import L23 L34 L45 L56 L6i L67a.
Import Lia Arith PeanoNat Bool NArith ZArith.
Import Coq.Lists.List.
Import ListNotations.

(** ** The division *)

Lemma Zl6_den : forall G x1 x2 x3 x4,
  [false; false; true; false] ++ rep01 (G * 3 + 1) ++ Cw6 x1 (x2 * 3 + 2) (x3 * 3 + 0) (x4 * 3 + 0) =
  den [Lit [false; false; true; false]; Rep (rp [false; true] 3) G; Lit (rp [false; true] 1 ++ k6_0);
    Rep kk6_1 x1; Lit (k6_1); Rep (rp kk6_2 3) x2; Lit (rp kk6_2 2 ++ k6_2); Rep (rp kk6_3 3) x3;
    Lit (rp kk6_3 0 ++ k6_3); Rep (rp kk6_4 3) x4; Lit (rp kk6_4 0 ++ k6_4 ++ ab6)].
Proof.
  intros G x1 x2 x3 x4. unfold Cw6. cbn [den bden].
  change (rep01 (G * 3 + 1)) with (rp [false; true] (G * 3 + 1)).
  rewrite ?rp_add, ?rp_mul, ?app_nil_r, <- ?app_assoc. reflexivity.
Qed.

Definition dv6 := Eval vm_compute in
  dmB 3 [Lit [false; false; true; false]; Rep (rp [false; true] 3) O; Lit (rp [false; true] 1 ++
    k6_0); Rep kk6_1 O; Lit (k6_1); Rep (rp kk6_2 3) O; Lit (rp kk6_2 2 ++ k6_2); Rep (rp kk6_3 3)
    O; Lit (rp kk6_3 0 ++ k6_3); Rep (rp kk6_4 3) O; Lit (rp kk6_4 0 ++ k6_4 ++ ab6)] tp6.
Definition a7_0 : list bool := Eval vm_compute in
  match dv6 with Some ([Lit a; _; _; _; _; _; _; _; _; _; _], _) => a | _ => [] end.
Definition a7_1 : list bool := Eval vm_compute in
  match dv6 with Some ([_; _; Lit a; _; _; _; _; _; _; _; _], _) => a | _ => [] end.
Definition a7_2 : list bool := Eval vm_compute in
  match dv6 with Some ([_; _; _; _; Lit a; _; _; _; _; _; _], _) => a | _ => [] end.
Definition a7_3 : list bool := Eval vm_compute in
  match dv6 with Some ([_; _; _; _; _; _; Lit a; _; _; _; _], _) => a | _ => [] end.
Definition a7_4 : list bool := Eval vm_compute in
  match dv6 with Some ([_; _; _; _; _; _; _; _; Lit a; _; _], _) => a | _ => [] end.
Definition a7_5 : list bool := Eval vm_compute in
  match dv6 with Some ([_; _; _; _; _; _; _; _; _; _; Lit a], _) => a | _ => [] end.
Definition P7_1 : list bool := Eval vm_compute in
  match dv6 with Some ([_; Rep p _; _; _; _; _; _; _; _; _; _], _) => p | _ => [] end.
Definition P7_2 : list bool := Eval vm_compute in
  match dv6 with Some ([_; _; _; Rep p _; _; _; _; _; _; _; _], _) => p | _ => [] end.
Definition P7_3 : list bool := Eval vm_compute in
  match dv6 with Some ([_; _; _; _; _; Rep p _; _; _; _; _; _], _) => p | _ => [] end.
Definition P7_4 : list bool := Eval vm_compute in
  match dv6 with Some ([_; _; _; _; _; _; _; Rep p _; _; _; _], _) => p | _ => [] end.
Definition P7_5 : list bool := Eval vm_compute in
  match dv6 with Some ([_; _; _; _; _; _; _; _; _; Rep p _; _], _) => p | _ => [] end.
Definition r7 : N := Eval vm_compute in match dv6 with Some (_, r) => r | None => 9%N end.
Definition je7 : nat := Eval vm_compute in 3 + N.to_nat r7.

Lemma dv6_ok : forall G x1 x2 x3 x4,
  dmB 3 [Lit [false; false; true; false]; Rep (rp [false; true] 3) G; Lit (rp [false; true] 1 ++
    k6_0); Rep kk6_1 x1; Lit (k6_1); Rep (rp kk6_2 3) x2; Lit (rp kk6_2 2 ++ k6_2); Rep (rp kk6_3 3)
    x3; Lit (rp kk6_3 0 ++ k6_3); Rep (rp kk6_4 3) x4; Lit (rp kk6_4 0 ++ k6_4 ++ ab6)] tp6 =
  Some ([Lit a7_0; Rep P7_1 G; Lit a7_1; Rep P7_2 x1; Lit a7_2; Rep P7_3 x2; Lit a7_3; Rep P7_4 x3;
    Lit a7_4; Rep P7_5 x4; Lit a7_5], r7).
Proof. intros G x1 x2 x3 x4. vm_compute. reflexivity. Qed.

Lemma tp6_lt : (tp6 < 3)%N.
Proof. reflexivity. Qed.

(** ** Level 7 *)

Definition b7 (d1 d2 d3 d4 d5 : nat) : list bool :=
  den [Lit a7_0; Rep P7_1 d1; Lit a7_1; Rep P7_2 d2; Lit a7_2; Rep P7_3 d3; Lit a7_3; Rep P7_4 d4; Lit
    a7_4; Rep P7_5 d5; Lit a7_5].

Definition c7_1 : nat := (2 * bval (b6 c6_1 c6_2 c6_3 c6_4)) / 3.
Definition c7_2 : nat := ((c6_1 - (cc6_1 + 1 + jj6_1)) / kq6_1).
Definition c7_3 : nat := ((c6_2 - (cc6_2 + 1 + jj6_2)) / kq6_2) / 3.
Definition c7_4 : nat := ((c6_3 - (cc6_3 + 1 + jj6_3)) / kq6_3) / 3.
Definition c7_5 : nat := ((c6_4 - (cc6_4 + 1 + jj6_4)) / kq6_4) / 3.

Lemma ET6 : 2 * bval (b6 c6_1 c6_2 c6_3 c6_4) = c7_1 * 3 + 1.
Proof. pose proof T6_res as H. unfold vT6 in H. unfold c7_1. gl (bval (b6 c6_1 c6_2 c6_3 c6_4)). Qed.

Lemma EC6_1 : c6_1 = cc6_1 + (c7_2 * kq6_1 + jj6_1) + 1.
Proof.
  pose proof c6_1_res as H. pose proof c6_1_res2 as H2. pose proof c6_1_lb as Hb.
  unfold rc6_1 in H. unfold rb6_1 in H2. unfold lb6_1 in Hb.
  unfold c7_2, cc6_1, kq6_1, jj6_1. cbn [Z.of_N] in H, H2, Hb. gl c6_1.
Qed.

Lemma EC6_2 : c6_2 = cc6_2 + ((c7_3 * 3 + 2) * kq6_2 + jj6_2) + 1.
Proof.
  pose proof c6_2_res as H. pose proof c6_2_res2 as H2. pose proof c6_2_lb as Hb.
  unfold rc6_2 in H. unfold rb6_2 in H2. unfold lb6_2 in Hb.
  unfold c7_3, cc6_2, kq6_2, jj6_2. cbn [Z.of_N] in H, H2, Hb. gl c6_2.
Qed.

Lemma EC6_3 : c6_3 = cc6_3 + ((c7_4 * 3 + 0) * kq6_3 + jj6_3) + 1.
Proof.
  pose proof c6_3_res as H. pose proof c6_3_res2 as H2. pose proof c6_3_lb as Hb.
  unfold rc6_3 in H. unfold rb6_3 in H2. unfold lb6_3 in Hb.
  unfold c7_4, cc6_3, kq6_3, jj6_3. cbn [Z.of_N] in H, H2, Hb. gl c6_3.
Qed.

Lemma EC6_4 : c6_4 = cc6_4 + ((c7_5 * 3 + 0) * kq6_4 + jj6_4) + 1.
Proof.
  pose proof c6_4_res as H. pose proof c6_4_res2 as H2. pose proof c6_4_lb as Hb.
  unfold rc6_4 in H. unfold rb6_4 in H2. unfold lb6_4 in Hb.
  unfold c7_5, cc6_4, kq6_4, jj6_4. cbn [Z.of_N] in H, H2, Hb. gl c6_4.
Qed.

Definition u7 : nat :=
  2 + 2 * bval (b6 (cc6_1 + (c7_2 * kq6_1 + jj6_1) + 1) (cc6_2 + ((c7_3 * 3 + 2) * kq6_2 + jj6_2) + 1)
    (cc6_3 + ((c7_4 * 3 + 0) * kq6_3 + jj6_3) + 1) (cc6_4 + ((c7_5 * 3 + 0) * kq6_4 + jj6_4) + 1)) +
    lc6 c7_2 (c7_3 * 3 + 2) (c7_4 * 3 + 0) (c7_5 * 3 + 0).

Theorem lvl7 : Lvl je7 (b7 c7_1 c7_2 c7_3 c7_4 c7_5) u7 w7.
Proof.
  pose proof lvl6i as H. pose proof ET6 as HT.
  rewrite EC6_1 in H, HT.
  rewrite EC6_2 in H, HT.
  rewrite EC6_3 in H, HT.
  rewrite EC6_4 in H, HT.
  apply (level_next_top _ (b6 (cc6_1 + (c7_2 * kq6_1 + jj6_1) + 1) (cc6_2 + ((c7_3 * 3 + 2) * kq6_2 +
    jj6_2) + 1) (cc6_3 + ((c7_4 * 3 + 0) * kq6_3 + jj6_3) + 1) (cc6_4 + ((c7_5 * 3 + 0) * kq6_4 +
    jj6_4) + 1)) _ w6 (Cw6 c7_2 (c7_3 * 3 + 2) (c7_4 * 3 + 0) (c7_5 * 3 + 0)) (lc6 c7_2 (c7_3 * 3 +
    2) (c7_4 * 3 + 0) (c7_5 * 3 + 0)) tp6 (b7 c7_1 c7_2 c7_3 c7_4 c7_5) r7 w7 H (Cw6_len _ _ _ _)
    tp6_lt (fun k Hk => end6 _ _ _ _ _ k Hk)).
  rewrite HT, Zl6_den. apply dmB_sound. apply dv6_ok.
Qed.

(** ** The counts of level 7 modulo 3^7, and lower bounds *)

Definition rc7_1 : N := Eval vm_compute in Z.to_N (((2 * vT6 - 1) / 3) mod 2187).
Lemma c7_1_res : (Z.of_nat c7_1 mod Z.of_N 2187 = Z.of_N rc7_1)%Z.
Proof.
  pose proof T6_res as H. unfold vT6 in H. unfold c7_1, rc7_1. cbn [Z.of_N].
  gl (bval (b6 c6_1 c6_2 c6_3 c6_4)).
Qed.
Definition lb7_1 : N := Eval vm_compute in ((2 * lbe6) / 3)%N.
Lemma c7_1_lb : (Z.of_N lb7_1 <= Z.of_nat c7_1)%Z.
Proof.
  pose proof (T6_lb c6_1 c6_2 c6_3 c6_4) as H. unfold lbe6 in H. unfold c7_1, lb7_1.
  cbn [Z.of_N] in *. gl (bval (b6 c6_1 c6_2 c6_3 c6_4)).
Qed.
Definition rb7_1 : N := Eval vm_compute in Z.to_N (((2 * Z.of_N t2_6 - 1) * 11) mod 32).
Lemma c7_1_res2 : (Z.of_nat c7_1 mod Z.of_N 32 = Z.of_N rb7_1)%Z.
Proof.
  pose proof T6_res as H. unfold vT6 in H.
  pose proof (T6_low c6_1 c6_2 c6_3 c6_4) as H2. unfold t2_6 in H2.
  unfold c7_1, rb7_1. cbn [Z.of_N] in *. gl (bval (b6 c6_1 c6_2 c6_3 c6_4)).
Qed.

Definition rc7_2 : N := Eval vm_compute in
  Z.to_N (((Z.of_N rc6_1 - (Z.of_nat cc6_1 + 1 + Z.of_nat jj6_1)) * 1) mod 2187).
Definition lb7_2 : N := Eval vm_compute in ((lb6_1 - (N.of_nat cc6_1 + 1 + N.of_nat jj6_1)) / 1)%N.
Definition rb7_2 : N := Eval vm_compute in
  Z.to_N ((((Z.of_N rb6_1 - (Z.of_nat cc6_1 + 1 + Z.of_nat jj6_1)) mod 32) / 1) mod 32).
Lemma c7_2_res : (Z.of_nat c7_2 mod Z.of_N 2187 = Z.of_N rc7_2)%Z.
Proof.
  pose proof c6_1_res as H. pose proof c6_1_res2 as H2. pose proof c6_1_lb as Hb.
  unfold rc6_1 in H. unfold rb6_1 in H2. unfold lb6_1 in Hb.
  unfold c7_2, rc7_2, cc6_1, kq6_1, jj6_1. cbn [Z.of_N] in *. gl c6_1.
Qed.
Lemma c7_2_res2 : (Z.of_nat c7_2 mod Z.of_N 32 = Z.of_N rb7_2)%Z.
Proof.
  pose proof c6_1_res as H. pose proof c6_1_res2 as H2. pose proof c6_1_lb as Hb.
  unfold rc6_1 in H. unfold rb6_1 in H2. unfold lb6_1 in Hb.
  unfold c7_2, rb7_2, cc6_1, kq6_1, jj6_1. cbn [Z.of_N] in *. gl c6_1.
Qed.
Lemma c7_2_lb : (Z.of_N lb7_2 <= Z.of_nat c7_2)%Z.
Proof.
  pose proof c6_1_res as H. pose proof c6_1_res2 as H2. pose proof c6_1_lb as Hb.
  unfold rc6_1 in H. unfold rb6_1 in H2. unfold lb6_1 in Hb.
  unfold c7_2, lb7_2, cc6_1, kq6_1, jj6_1. cbn [Z.of_N] in *. gl c6_1.
Qed.

Definition rc7_3 : N := Eval vm_compute in
  Z.to_N (((((Z.of_N rc6_2 - (Z.of_nat cc6_2 + 1 + Z.of_nat jj6_2)) * 1) mod 6561) / 3) mod 2187).
Definition lb7_3 : N := Eval vm_compute in (((lb6_2 - (N.of_nat cc6_2 + 1 + N.of_nat jj6_2)) / 1) / 3)%N.
Definition rb7_3 : N := Eval vm_compute in
  Z.to_N (((((Z.of_N rb6_2 - (Z.of_nat cc6_2 + 1 + Z.of_nat jj6_2)) mod 32) / 1 - 2) * 11) mod 32).
Lemma c7_3_res : (Z.of_nat c7_3 mod Z.of_N 2187 = Z.of_N rc7_3)%Z.
Proof.
  pose proof c6_2_res as H. pose proof c6_2_res2 as H2. pose proof c6_2_lb as Hb.
  unfold rc6_2 in H. unfold rb6_2 in H2. unfold lb6_2 in Hb.
  unfold c7_3, rc7_3, cc6_2, kq6_2, jj6_2. cbn [Z.of_N] in *. gl c6_2.
Qed.
Lemma c7_3_res2 : (Z.of_nat c7_3 mod Z.of_N 32 = Z.of_N rb7_3)%Z.
Proof.
  pose proof c6_2_res as H. pose proof c6_2_res2 as H2. pose proof c6_2_lb as Hb.
  unfold rc6_2 in H. unfold rb6_2 in H2. unfold lb6_2 in Hb.
  unfold c7_3, rb7_3, cc6_2, kq6_2, jj6_2. cbn [Z.of_N] in *. gl c6_2.
Qed.
Lemma c7_3_lb : (Z.of_N lb7_3 <= Z.of_nat c7_3)%Z.
Proof.
  pose proof c6_2_res as H. pose proof c6_2_res2 as H2. pose proof c6_2_lb as Hb.
  unfold rc6_2 in H. unfold rb6_2 in H2. unfold lb6_2 in Hb.
  unfold c7_3, lb7_3, cc6_2, kq6_2, jj6_2. cbn [Z.of_N] in *. gl c6_2.
Qed.

Definition rc7_4 : N := Eval vm_compute in
  Z.to_N (((((Z.of_N rc6_3 - (Z.of_nat cc6_3 + 1 + Z.of_nat jj6_3)) * 1) mod 6561) / 3) mod 2187).
Definition lb7_4 : N := Eval vm_compute in (((lb6_3 - (N.of_nat cc6_3 + 1 + N.of_nat jj6_3)) / 1) / 3)%N.
Definition rb7_4 : N := Eval vm_compute in
  Z.to_N (((((Z.of_N rb6_3 - (Z.of_nat cc6_3 + 1 + Z.of_nat jj6_3)) mod 32) / 1 - 0) * 11) mod 32).
Lemma c7_4_res : (Z.of_nat c7_4 mod Z.of_N 2187 = Z.of_N rc7_4)%Z.
Proof.
  pose proof c6_3_res as H. pose proof c6_3_res2 as H2. pose proof c6_3_lb as Hb.
  unfold rc6_3 in H. unfold rb6_3 in H2. unfold lb6_3 in Hb.
  unfold c7_4, rc7_4, cc6_3, kq6_3, jj6_3. cbn [Z.of_N] in *. gl c6_3.
Qed.
Lemma c7_4_res2 : (Z.of_nat c7_4 mod Z.of_N 32 = Z.of_N rb7_4)%Z.
Proof.
  pose proof c6_3_res as H. pose proof c6_3_res2 as H2. pose proof c6_3_lb as Hb.
  unfold rc6_3 in H. unfold rb6_3 in H2. unfold lb6_3 in Hb.
  unfold c7_4, rb7_4, cc6_3, kq6_3, jj6_3. cbn [Z.of_N] in *. gl c6_3.
Qed.
Lemma c7_4_lb : (Z.of_N lb7_4 <= Z.of_nat c7_4)%Z.
Proof.
  pose proof c6_3_res as H. pose proof c6_3_res2 as H2. pose proof c6_3_lb as Hb.
  unfold rc6_3 in H. unfold rb6_3 in H2. unfold lb6_3 in Hb.
  unfold c7_4, lb7_4, cc6_3, kq6_3, jj6_3. cbn [Z.of_N] in *. gl c6_3.
Qed.

Definition rc7_5 : N := Eval vm_compute in
  Z.to_N (((((Z.of_N rc6_4 - (Z.of_nat cc6_4 + 1 + Z.of_nat jj6_4)) * 1) mod 6561) / 3) mod 2187).
Definition lb7_5 : N := Eval vm_compute in (((lb6_4 - (N.of_nat cc6_4 + 1 + N.of_nat jj6_4)) / 1) / 3)%N.
Definition rb7_5 : N := Eval vm_compute in
  Z.to_N (((((Z.of_N rb6_4 - (Z.of_nat cc6_4 + 1 + Z.of_nat jj6_4)) mod 32) / 1 - 0) * 11) mod 32).
Lemma c7_5_res : (Z.of_nat c7_5 mod Z.of_N 2187 = Z.of_N rc7_5)%Z.
Proof.
  pose proof c6_4_res as H. pose proof c6_4_res2 as H2. pose proof c6_4_lb as Hb.
  unfold rc6_4 in H. unfold rb6_4 in H2. unfold lb6_4 in Hb.
  unfold c7_5, rc7_5, cc6_4, kq6_4, jj6_4. cbn [Z.of_N] in *. gl c6_4.
Qed.
Lemma c7_5_res2 : (Z.of_nat c7_5 mod Z.of_N 32 = Z.of_N rb7_5)%Z.
Proof.
  pose proof c6_4_res as H. pose proof c6_4_res2 as H2. pose proof c6_4_lb as Hb.
  unfold rc6_4 in H. unfold rb6_4 in H2. unfold lb6_4 in Hb.
  unfold c7_5, rb7_5, cc6_4, kq6_4, jj6_4. cbn [Z.of_N] in *. gl c6_4.
Qed.
Lemma c7_5_lb : (Z.of_N lb7_5 <= Z.of_nat c7_5)%Z.
Proof.
  pose proof c6_4_res as H. pose proof c6_4_res2 as H2. pose proof c6_4_lb as Hb.
  unfold rc6_4 in H. unfold rb6_4 in H2. unfold lb6_4 in Hb.
  unfold c7_5, lb7_5, cc6_4, kq6_4, jj6_4. cbn [Z.of_N] in *. gl c6_4.
Qed.

(** ** The word of level 7 modulo 3^7 *)

Definition vT7 : Z := Eval vm_compute in
  gv (resW 2187 [RL a7_0; RR P7_1 2187 rc7_1; RL a7_1; RR P7_2 2187 rc7_2; RL a7_2; RR P7_3 2187
    rc7_3; RL a7_3; RR P7_4 2187 rc7_4; RL a7_4; RR P7_5 2187 rc7_5; RL a7_5]).

Lemma T7_res : (Z.of_nat (bval (b7 c7_1 c7_2 c7_3 c7_4 c7_5)) mod 2187 = vT7)%Z.
Proof.
  unfold b7.
  apply (resW_sound 2187 [Lit a7_0; Rep P7_1 c7_1; Lit a7_1; Rep P7_2 c7_2; Lit a7_2; Rep P7_3 c7_3;
    Lit a7_3; Rep P7_4 c7_4; Lit a7_4; Rep P7_5 c7_5; Lit a7_5]
           [RL a7_0; RR P7_1 2187 rc7_1; RL a7_1; RR P7_2 2187 rc7_2; RL a7_2; RR P7_3 2187 rc7_3; RL a7_3; RR
            P7_4 2187 rc7_4; RL a7_4; RR P7_5 2187 rc7_5; RL a7_5]);
    [lia | | vm_compute; reflexivity].
  exact (Forall2_cons _ _ (mL a7_0)
    (Forall2_cons _ _ (mR P7_1 c7_1 2187%N rc7_1 c7_1_res)
    (Forall2_cons _ _ (mL a7_1)
    (Forall2_cons _ _ (mR P7_2 c7_2 2187%N rc7_2 c7_2_res)
    (Forall2_cons _ _ (mL a7_2)
    (Forall2_cons _ _ (mR P7_3 c7_3 2187%N rc7_3 c7_3_res)
    (Forall2_cons _ _ (mL a7_3)
    (Forall2_cons _ _ (mR P7_4 c7_4 2187%N rc7_4 c7_4_res)
    (Forall2_cons _ _ (mL a7_4)
    (Forall2_cons _ _ (mR P7_5 c7_5 2187%N rc7_5 c7_5_res)
    (Forall2_cons _ _ (mL a7_5) (Forall2_nil _)))))))))))).
Qed.

Definition lbe7 : N := Eval vm_compute in bvalN a7_5.

Lemma T7_lb : forall d1 d2 d3 d4 d5, (Z.of_N lbe7 <= Z.of_nat (bval (b7 d1 d2 d3 d4 d5)))%Z.
Proof.
  intros d1 d2 d3 d4 d5. unfold b7. change lbe7 with (bvalN a7_5).
  exact (lbZ [Lit a7_0; Rep P7_1 d1; Lit a7_1; Rep P7_2 d2; Lit a7_2; Rep P7_3 d3; Lit a7_3; Rep P7_4
    d4; Lit a7_4; Rep P7_5 d5] a7_5).
Qed.

Definition t2_7 : N := Eval vm_compute in bvalN a7_0.

Lemma T7_low : forall d1 d2 d3 d4 d5, (Z.of_nat (bval (b7 d1 d2 d3 d4 d5)) mod 16 = Z.of_N t2_7)%Z.
Proof.
  intros d1 d2 d3 d4 d5. unfold b7.
  exact (bval_low_den a7_0 [Rep P7_1 d1; Lit a7_1; Rep P7_2 d2; Lit a7_2; Rep P7_3 d3; Lit a7_3; Rep
    P7_4 d4; Lit a7_4; Rep P7_5 d5; Lit a7_5]).
Qed.

End L67b.

Module L78a.

(** * 1RB1LB_1RC0RD_0LA1RE_0RF1LC_1LA0RB_---1LC: the end phase of level 7

    Level 7 has class 4: the end phase is one computation on the low literal of the counter
    word ([c4cert]), and the word that is added is the complement of the rest of the counter
    word between two literals.  Generated by a script. *)

Import Individual62.
Import T694_levels End694 Sym694 Lev694 Lvl1_694 Eng694 Cert694 Run694 Res694 Gen694.
Import L23 L34 L45 L56 L6i L67a L67b.
Import Lia Arith PeanoNat Bool NArith ZArith.
Import Coq.Lists.List.
Import ListNotations.

Definition c4_7 := Eval vm_compute in c4cert 6000 6000 je7 a7_0 w7.
Definition s4_7 : nat := Eval vm_compute in match c4_7 with Some (x, _, _, _, _) => x | None => O end.
Definition la7 : nat := Eval vm_compute in match c4_7 with Some (_, x, _, _, _) => x | None => O end.
Definition k7_0 : list bool := Eval vm_compute in match c4_7 with Some (_, _, x, _, _) => x | None => [] end.
Definition ab4_7 : list bool := Eval vm_compute in match c4_7 with Some (_, _, _, x, _) => x | None => [] end.
Definition w8 : list bool := Eval vm_compute in match c4_7 with Some (_, _, _, _, x) => x | None => [] end.
Definition tp7 : N := 0%N.
Definition ab7 : list bool := [].

Lemma c4_7_ok : c4cert 6000 6000 je7 a7_0 w7 = Some (s4_7, la7, k7_0, ab4_7, w8).
Proof. vm_compute. reflexivity. Qed.

Definition rest7 (n1 n2 n3 n4 n5 : nat) : list blk :=
  [Rep P7_1 n1; Lit a7_1; Rep P7_2 n2; Lit a7_2; Rep P7_3 n3; Lit a7_3; Rep P7_4 n4; Lit a7_4; Rep
    P7_5 n5; Lit a7_5].

Lemma rest7_len : forall n1 n2 n3 n4 n5, length (den (rest7 n1 n2 n3 n4 n5)) = 2 * hlen (rest7 n1 n2 n3 n4 n5).
Proof. intros n1 n2 n3 n4 n5. apply den_len. vm_compute. reflexivity. Qed.

Definition kk7_1 : list bool := map negb P7_1.
Definition k7_1 : list bool := map negb a7_1.
Definition kk7_2 : list bool := map negb P7_2.
Definition k7_2 : list bool := map negb a7_2.
Definition kk7_3 : list bool := map negb P7_3.
Definition k7_3 : list bool := map negb a7_3.
Definition kk7_4 : list bool := map negb P7_4.
Definition k7_4 : list bool := map negb a7_4.
Definition kk7_5 : list bool := map negb P7_5.
Definition k7_5 : list bool := map negb a7_5 ++ ab4_7.

Definition Cw7 (n1 n2 n3 n4 n5 : nat) : list bool :=
  den [Lit k7_0; Rep kk7_1 n1; Lit k7_1; Rep kk7_2 n2; Lit k7_2; Rep kk7_3 n3; Lit k7_3; Rep kk7_4 n4;
    Lit k7_4; Rep kk7_5 n5; Lit k7_5] ++ ab7.
Definition lc7 (n1 n2 n3 n4 n5 : nat) : nat := s4_7 + hlen (rest7 n1 n2 n3 n4 n5) + la7.

Lemma Cw7_eq : forall n1 n2 n3 n4 n5,
  Cw7 n1 n2 n3 n4 n5 = k7_0 ++ map negb (den (rest7 n1 n2 n3 n4 n5)) ++ ab4_7.
Proof.
  intros n1 n2 n3 n4 n5. rewrite negb_den. unfold Cw7, rest7, ab7, kk7_1, kk7_2, kk7_3, kk7_4, kk7_5, k7_1, k7_2, k7_3, k7_4, k7_5.
  cbn [map nblk den bden]. rewrite ?app_nil_r, <- ?app_assoc. reflexivity.
Qed.

Lemma Cw7_len : forall n1 n2 n3 n4 n5, length (Cw7 n1 n2 n3 n4 n5) = 2 * lc7 n1 n2 n3 n4 n5.
Proof.
  intros n1 n2 n3 n4 n5. rewrite Cw7_eq, !length_app, length_map, rest7_len. unfold lc7.
  assert (H1 : length k7_0 = 2 * s4_7) by (vm_compute; reflexivity).
  assert (H2 : length ab4_7 = 2 * la7) by (vm_compute; reflexivity).
  rewrite H1, H2. lia.
Qed.

Lemma end7 : forall n1 n2 n3 n4 n5 h k, (1 <= h)%nat -> (1 <= k)%nat -> exists n M',
  tickN 3 n (rep10 k ++ c1101 ++ repeat true (3 * h) ++ rep10 je7 ++ c1101 ++
             encb false (b7 n1 n2 n3 n4 n5) ++ w7) =
    Some (Slev M' (3 * (h + lc7 n1 n2 n3 n4 n5) + 1) w8) /\
  Z.of_nat M' = (Z.of_nat k +
                 (Z.of_nat (bval (Cw7 n1 n2 n3 n4 n5)) + Z.of_N tp7 * pw4 (lc7 n1 n2 n3 n4 n5)) * pw4 h)%Z.
Proof.
  intros n1 n2 n3 n4 n5 h k Hh Hk.
  destruct (c4cert_sound _ _ _ _ _ _ _ _ _ _ c4_7_ok (den (rest7 n1 n2 n3 n4 n5)) (hlen (rest7 n1 n2 n3 n4 n5)) h
              (rest7_len n1 n2 n3 n4 n5) Hh k Hk) as [n [M' [E D]]].
  exists n, M'. split; [exact E |].
  rewrite D, (Cw7_eq n1 n2 n3 n4 n5). unfold tp7. cbn [Z.of_N]. ring.
Qed.

(** ** What the division needs: which blocks are tripled, and the residues of the counts *)

Definition cfg7_trip : list bool := Eval vm_compute in
  map (fun P => negb (N.eqb (bvalN P mod 3) 0)) [kk7_1; kk7_2; kk7_3; kk7_4; kk7_5].
Definition cfg7_rho : list N := Eval vm_compute in
  [(((rc7_1 + 1594323 - 0%N) * (N.of_nat 1%nat mod 3)) mod 3)%N; (((rc7_2 + 1594323 - 0%N) * (N.of_nat 1%nat mod 3)) mod 3)%N; (((rc7_3 + 1594323 - 0%N) * (N.of_nat 1%nat mod 3)) mod 3)%N; (((rc7_4 + 1594323 - 0%N) * (N.of_nat 1%nat mod 3)) mod 3)%N; (((rc7_5 + 1594323 - 0%N) * (N.of_nat 1%nat mod 3)) mod 3)%N].
Definition cfg7_k : list nat := Eval vm_compute in [1%nat; 1%nat; 1%nat; 1%nat; 1%nat].
Definition cfg7_j : list nat := Eval vm_compute in [0%nat; 0%nat; 0%nat; 0%nat; 0%nat].
Definition cfg7_rhoT : Z := Eval vm_compute in ((2 * vT7) mod 3)%Z.

End L78a.

Module L78b.

(** * 1RB1LB_1RC0RD_0LA1RE_0RF1LC_1LA0RB_---1LC: from level 7 to level 8

    The division by 3 of [0100 (10)^(h-2) C] with the counts as variables, level 8 for the
    real counts, and the residues modulo 3^6 and lower bounds of the counts of level 8.
    Generated by a script. *)

Import Individual62.
Import T694_levels End694 Sym694 Lev694 Lvl1_694 Eng694 Cert694 Run694 Res694 Gen694.
Import L23 L34 L45 L56 L6i L67a L67b L78a.
Import Lia Arith PeanoNat Bool NArith ZArith.
Import Coq.Lists.List.
Import ListNotations.

(** ** The division *)

Lemma Zl7_den : forall G x1 x2 x3 x4 x5,
  [false; false; true; false] ++ rep01 (G * 3 + 2) ++ Cw7 (x1 * 3 + 1) (x2 * 3 + 0) (x3 * 3 + 1) (x4 * 3 + 2) (x5 * 3 + 0) =
  den [Lit [false; false; true; false]; Rep (rp [false; true] 3) G; Lit (rp [false; true] 2 ++ k7_0);
    Rep (rp kk7_1 3) x1; Lit (rp kk7_1 1 ++ k7_1); Rep (rp kk7_2 3) x2; Lit (rp kk7_2 0 ++ k7_2);
    Rep (rp kk7_3 3) x3; Lit (rp kk7_3 1 ++ k7_3); Rep (rp kk7_4 3) x4; Lit (rp kk7_4 2 ++ k7_4);
    Rep (rp kk7_5 3) x5; Lit (rp kk7_5 0 ++ k7_5 ++ ab7)].
Proof.
  intros G x1 x2 x3 x4 x5. unfold Cw7. cbn [den bden].
  change (rep01 (G * 3 + 2)) with (rp [false; true] (G * 3 + 2)).
  rewrite ?rp_add, ?rp_mul, ?app_nil_r, <- ?app_assoc. reflexivity.
Qed.

Definition dv7 := Eval vm_compute in
  dmB 3 [Lit [false; false; true; false]; Rep (rp [false; true] 3) O; Lit (rp [false; true] 2 ++
    k7_0); Rep (rp kk7_1 3) O; Lit (rp kk7_1 1 ++ k7_1); Rep (rp kk7_2 3) O; Lit (rp kk7_2 0 ++
    k7_2); Rep (rp kk7_3 3) O; Lit (rp kk7_3 1 ++ k7_3); Rep (rp kk7_4 3) O; Lit (rp kk7_4 2 ++
    k7_4); Rep (rp kk7_5 3) O; Lit (rp kk7_5 0 ++ k7_5 ++ ab7)] tp7.
Definition a8_0 : list bool := Eval vm_compute in
  match dv7 with Some ([Lit a; _; _; _; _; _; _; _; _; _; _; _; _], _) => a | _ => [] end.
Definition a8_1 : list bool := Eval vm_compute in
  match dv7 with Some ([_; _; Lit a; _; _; _; _; _; _; _; _; _; _], _) => a | _ => [] end.
Definition a8_2 : list bool := Eval vm_compute in
  match dv7 with Some ([_; _; _; _; Lit a; _; _; _; _; _; _; _; _], _) => a | _ => [] end.
Definition a8_3 : list bool := Eval vm_compute in
  match dv7 with Some ([_; _; _; _; _; _; Lit a; _; _; _; _; _; _], _) => a | _ => [] end.
Definition a8_4 : list bool := Eval vm_compute in
  match dv7 with Some ([_; _; _; _; _; _; _; _; Lit a; _; _; _; _], _) => a | _ => [] end.
Definition a8_5 : list bool := Eval vm_compute in
  match dv7 with Some ([_; _; _; _; _; _; _; _; _; _; Lit a; _; _], _) => a | _ => [] end.
Definition a8_6 : list bool := Eval vm_compute in
  match dv7 with Some ([_; _; _; _; _; _; _; _; _; _; _; _; Lit a], _) => a | _ => [] end.
Definition P8_1 : list bool := Eval vm_compute in
  match dv7 with Some ([_; Rep p _; _; _; _; _; _; _; _; _; _; _; _], _) => p | _ => [] end.
Definition P8_2 : list bool := Eval vm_compute in
  match dv7 with Some ([_; _; _; Rep p _; _; _; _; _; _; _; _; _; _], _) => p | _ => [] end.
Definition P8_3 : list bool := Eval vm_compute in
  match dv7 with Some ([_; _; _; _; _; Rep p _; _; _; _; _; _; _; _], _) => p | _ => [] end.
Definition P8_4 : list bool := Eval vm_compute in
  match dv7 with Some ([_; _; _; _; _; _; _; Rep p _; _; _; _; _; _], _) => p | _ => [] end.
Definition P8_5 : list bool := Eval vm_compute in
  match dv7 with Some ([_; _; _; _; _; _; _; _; _; Rep p _; _; _; _], _) => p | _ => [] end.
Definition P8_6 : list bool := Eval vm_compute in
  match dv7 with Some ([_; _; _; _; _; _; _; _; _; _; _; Rep p _; _], _) => p | _ => [] end.
Definition r8 : N := Eval vm_compute in match dv7 with Some (_, r) => r | None => 9%N end.
Definition je8 : nat := Eval vm_compute in 3 + N.to_nat r8.

Lemma dv7_ok : forall G x1 x2 x3 x4 x5,
  dmB 3 [Lit [false; false; true; false]; Rep (rp [false; true] 3) G; Lit (rp [false; true] 2 ++
    k7_0); Rep (rp kk7_1 3) x1; Lit (rp kk7_1 1 ++ k7_1); Rep (rp kk7_2 3) x2; Lit (rp kk7_2 0 ++
    k7_2); Rep (rp kk7_3 3) x3; Lit (rp kk7_3 1 ++ k7_3); Rep (rp kk7_4 3) x4; Lit (rp kk7_4 2 ++
    k7_4); Rep (rp kk7_5 3) x5; Lit (rp kk7_5 0 ++ k7_5 ++ ab7)] tp7 =
  Some ([Lit a8_0; Rep P8_1 G; Lit a8_1; Rep P8_2 x1; Lit a8_2; Rep P8_3 x2; Lit a8_3; Rep P8_4 x3;
    Lit a8_4; Rep P8_5 x4; Lit a8_5; Rep P8_6 x5; Lit a8_6], r8).
Proof. intros G x1 x2 x3 x4 x5. vm_compute. reflexivity. Qed.

Lemma tp7_lt : (tp7 < 3)%N.
Proof. reflexivity. Qed.

(** ** Level 8 *)

Definition b8 (d1 d2 d3 d4 d5 d6 : nat) : list bool :=
  den [Lit a8_0; Rep P8_1 d1; Lit a8_1; Rep P8_2 d2; Lit a8_2; Rep P8_3 d3; Lit a8_3; Rep P8_4 d4; Lit
    a8_4; Rep P8_5 d5; Lit a8_5; Rep P8_6 d6; Lit a8_6].

Definition c8_1 : nat := (2 * bval (b7 c7_1 c7_2 c7_3 c7_4 c7_5)) / 3.
Definition c8_2 : nat := c7_1 / 3.
Definition c8_3 : nat := c7_2 / 3.
Definition c8_4 : nat := c7_3 / 3.
Definition c8_5 : nat := c7_4 / 3.
Definition c8_6 : nat := c7_5 / 3.

Lemma ET7 : 2 * bval (b7 c7_1 c7_2 c7_3 c7_4 c7_5) = c8_1 * 3 + 2.
Proof. pose proof T7_res as H. unfold vT7 in H. unfold c8_1. gl (bval (b7 c7_1 c7_2 c7_3 c7_4 c7_5)). Qed.

Lemma EC7_1 : c7_1 = c8_2 * 3 + 1.
Proof.
  pose proof c7_1_res as H. pose proof c7_1_res2 as H2. pose proof c7_1_lb as Hb.
  unfold rc7_1 in H. unfold rb7_1 in H2. unfold lb7_1 in Hb.
  unfold c8_2. cbn [Z.of_N] in H, H2, Hb. gl c7_1.
Qed.

Lemma EC7_2 : c7_2 = c8_3 * 3 + 0.
Proof.
  pose proof c7_2_res as H. pose proof c7_2_res2 as H2. pose proof c7_2_lb as Hb.
  unfold rc7_2 in H. unfold rb7_2 in H2. unfold lb7_2 in Hb.
  unfold c8_3. cbn [Z.of_N] in H, H2, Hb. gl c7_2.
Qed.

Lemma EC7_3 : c7_3 = c8_4 * 3 + 1.
Proof.
  pose proof c7_3_res as H. pose proof c7_3_res2 as H2. pose proof c7_3_lb as Hb.
  unfold rc7_3 in H. unfold rb7_3 in H2. unfold lb7_3 in Hb.
  unfold c8_4. cbn [Z.of_N] in H, H2, Hb. gl c7_3.
Qed.

Lemma EC7_4 : c7_4 = c8_5 * 3 + 2.
Proof.
  pose proof c7_4_res as H. pose proof c7_4_res2 as H2. pose proof c7_4_lb as Hb.
  unfold rc7_4 in H. unfold rb7_4 in H2. unfold lb7_4 in Hb.
  unfold c8_5. cbn [Z.of_N] in H, H2, Hb. gl c7_4.
Qed.

Lemma EC7_5 : c7_5 = c8_6 * 3 + 0.
Proof.
  pose proof c7_5_res as H. pose proof c7_5_res2 as H2. pose proof c7_5_lb as Hb.
  unfold rc7_5 in H. unfold rb7_5 in H2. unfold lb7_5 in Hb.
  unfold c8_6. cbn [Z.of_N] in H, H2, Hb. gl c7_5.
Qed.

Definition u8 : nat :=
  2 + 2 * bval (b7 (c8_2 * 3 + 1) (c8_3 * 3 + 0) (c8_4 * 3 + 1) (c8_5 * 3 + 2) (c8_6 * 3 + 0)) + lc7
    (c8_2 * 3 + 1) (c8_3 * 3 + 0) (c8_4 * 3 + 1) (c8_5 * 3 + 2) (c8_6 * 3 + 0).

Theorem lvl8 : Lvl je8 (b8 c8_1 c8_2 c8_3 c8_4 c8_5 c8_6) u8 w8.
Proof.
  pose proof lvl7 as H. pose proof ET7 as HT.
  rewrite EC7_1 in H, HT.
  rewrite EC7_2 in H, HT.
  rewrite EC7_3 in H, HT.
  rewrite EC7_4 in H, HT.
  rewrite EC7_5 in H, HT.
  apply (level_next_top _ (b7 (c8_2 * 3 + 1) (c8_3 * 3 + 0) (c8_4 * 3 + 1) (c8_5 * 3 + 2) (c8_6 * 3 +
    0)) _ w7 (Cw7 (c8_2 * 3 + 1) (c8_3 * 3 + 0) (c8_4 * 3 + 1) (c8_5 * 3 + 2) (c8_6 * 3 + 0)) (lc7
    (c8_2 * 3 + 1) (c8_3 * 3 + 0) (c8_4 * 3 + 1) (c8_5 * 3 + 2) (c8_6 * 3 + 0)) tp7 (b8 c8_1 c8_2
    c8_3 c8_4 c8_5 c8_6) r8 w8 H (Cw7_len _ _ _ _ _) tp7_lt (fun k Hk => end7 _ _ _ _ _ _ k (h_pos
    _) Hk)).
  rewrite HT, Zl7_den. apply dmB_sound. apply dv7_ok.
Qed.

(** ** The counts of level 8 modulo 3^6, and lower bounds *)

Definition rc8_1 : N := Eval vm_compute in Z.to_N (((2 * vT7 - 2) / 3) mod 729).
Lemma c8_1_res : (Z.of_nat c8_1 mod Z.of_N 729 = Z.of_N rc8_1)%Z.
Proof.
  pose proof T7_res as H. unfold vT7 in H. unfold c8_1, rc8_1. cbn [Z.of_N].
  gl (bval (b7 c7_1 c7_2 c7_3 c7_4 c7_5)).
Qed.
Definition lb8_1 : N := Eval vm_compute in ((2 * lbe7) / 3)%N.
Lemma c8_1_lb : (Z.of_N lb8_1 <= Z.of_nat c8_1)%Z.
Proof.
  pose proof (T7_lb c7_1 c7_2 c7_3 c7_4 c7_5) as H. unfold lbe7 in H. unfold c8_1, lb8_1.
  cbn [Z.of_N] in *. gl (bval (b7 c7_1 c7_2 c7_3 c7_4 c7_5)).
Qed.
Definition rb8_1 : N := Eval vm_compute in Z.to_N (((2 * Z.of_N t2_7 - 2) * 11) mod 32).
Lemma c8_1_res2 : (Z.of_nat c8_1 mod Z.of_N 32 = Z.of_N rb8_1)%Z.
Proof.
  pose proof T7_res as H. unfold vT7 in H.
  pose proof (T7_low c7_1 c7_2 c7_3 c7_4 c7_5) as H2. unfold t2_7 in H2.
  unfold c8_1, rb8_1. cbn [Z.of_N] in *. gl (bval (b7 c7_1 c7_2 c7_3 c7_4 c7_5)).
Qed.

Definition rc8_2 : N := Eval vm_compute in
  Z.to_N (((((Z.of_N rc7_1 - 0) * 1) mod 2187) / 3) mod 729).
Definition lb8_2 : N := Eval vm_compute in (((lb7_1 - 0) / 1) / 3)%N.
Definition rb8_2 : N := Eval vm_compute in
  Z.to_N (((((Z.of_N rb7_1 - 0) mod 32) / 1 - 1) * 11) mod 32).
Lemma c8_2_res : (Z.of_nat c8_2 mod Z.of_N 729 = Z.of_N rc8_2)%Z.
Proof.
  pose proof c7_1_res as H. pose proof c7_1_res2 as H2. pose proof c7_1_lb as Hb.
  unfold rc7_1 in H. unfold rb7_1 in H2. unfold lb7_1 in Hb.
  unfold c8_2, rc8_2. cbn [Z.of_N] in *. gl c7_1.
Qed.
Lemma c8_2_res2 : (Z.of_nat c8_2 mod Z.of_N 32 = Z.of_N rb8_2)%Z.
Proof.
  pose proof c7_1_res as H. pose proof c7_1_res2 as H2. pose proof c7_1_lb as Hb.
  unfold rc7_1 in H. unfold rb7_1 in H2. unfold lb7_1 in Hb.
  unfold c8_2, rb8_2. cbn [Z.of_N] in *. gl c7_1.
Qed.
Lemma c8_2_lb : (Z.of_N lb8_2 <= Z.of_nat c8_2)%Z.
Proof.
  pose proof c7_1_res as H. pose proof c7_1_res2 as H2. pose proof c7_1_lb as Hb.
  unfold rc7_1 in H. unfold rb7_1 in H2. unfold lb7_1 in Hb.
  unfold c8_2, lb8_2. cbn [Z.of_N] in *. gl c7_1.
Qed.

Definition rc8_3 : N := Eval vm_compute in
  Z.to_N (((((Z.of_N rc7_2 - 0) * 1) mod 2187) / 3) mod 729).
Definition lb8_3 : N := Eval vm_compute in (((lb7_2 - 0) / 1) / 3)%N.
Definition rb8_3 : N := Eval vm_compute in
  Z.to_N (((((Z.of_N rb7_2 - 0) mod 32) / 1 - 0) * 11) mod 32).
Lemma c8_3_res : (Z.of_nat c8_3 mod Z.of_N 729 = Z.of_N rc8_3)%Z.
Proof.
  pose proof c7_2_res as H. pose proof c7_2_res2 as H2. pose proof c7_2_lb as Hb.
  unfold rc7_2 in H. unfold rb7_2 in H2. unfold lb7_2 in Hb.
  unfold c8_3, rc8_3. cbn [Z.of_N] in *. gl c7_2.
Qed.
Lemma c8_3_res2 : (Z.of_nat c8_3 mod Z.of_N 32 = Z.of_N rb8_3)%Z.
Proof.
  pose proof c7_2_res as H. pose proof c7_2_res2 as H2. pose proof c7_2_lb as Hb.
  unfold rc7_2 in H. unfold rb7_2 in H2. unfold lb7_2 in Hb.
  unfold c8_3, rb8_3. cbn [Z.of_N] in *. gl c7_2.
Qed.
Lemma c8_3_lb : (Z.of_N lb8_3 <= Z.of_nat c8_3)%Z.
Proof.
  pose proof c7_2_res as H. pose proof c7_2_res2 as H2. pose proof c7_2_lb as Hb.
  unfold rc7_2 in H. unfold rb7_2 in H2. unfold lb7_2 in Hb.
  unfold c8_3, lb8_3. cbn [Z.of_N] in *. gl c7_2.
Qed.

Definition rc8_4 : N := Eval vm_compute in
  Z.to_N (((((Z.of_N rc7_3 - 0) * 1) mod 2187) / 3) mod 729).
Definition lb8_4 : N := Eval vm_compute in (((lb7_3 - 0) / 1) / 3)%N.
Definition rb8_4 : N := Eval vm_compute in
  Z.to_N (((((Z.of_N rb7_3 - 0) mod 32) / 1 - 1) * 11) mod 32).
Lemma c8_4_res : (Z.of_nat c8_4 mod Z.of_N 729 = Z.of_N rc8_4)%Z.
Proof.
  pose proof c7_3_res as H. pose proof c7_3_res2 as H2. pose proof c7_3_lb as Hb.
  unfold rc7_3 in H. unfold rb7_3 in H2. unfold lb7_3 in Hb.
  unfold c8_4, rc8_4. cbn [Z.of_N] in *. gl c7_3.
Qed.
Lemma c8_4_res2 : (Z.of_nat c8_4 mod Z.of_N 32 = Z.of_N rb8_4)%Z.
Proof.
  pose proof c7_3_res as H. pose proof c7_3_res2 as H2. pose proof c7_3_lb as Hb.
  unfold rc7_3 in H. unfold rb7_3 in H2. unfold lb7_3 in Hb.
  unfold c8_4, rb8_4. cbn [Z.of_N] in *. gl c7_3.
Qed.
Lemma c8_4_lb : (Z.of_N lb8_4 <= Z.of_nat c8_4)%Z.
Proof.
  pose proof c7_3_res as H. pose proof c7_3_res2 as H2. pose proof c7_3_lb as Hb.
  unfold rc7_3 in H. unfold rb7_3 in H2. unfold lb7_3 in Hb.
  unfold c8_4, lb8_4. cbn [Z.of_N] in *. gl c7_3.
Qed.

Definition rc8_5 : N := Eval vm_compute in
  Z.to_N (((((Z.of_N rc7_4 - 0) * 1) mod 2187) / 3) mod 729).
Definition lb8_5 : N := Eval vm_compute in (((lb7_4 - 0) / 1) / 3)%N.
Definition rb8_5 : N := Eval vm_compute in
  Z.to_N (((((Z.of_N rb7_4 - 0) mod 32) / 1 - 2) * 11) mod 32).
Lemma c8_5_res : (Z.of_nat c8_5 mod Z.of_N 729 = Z.of_N rc8_5)%Z.
Proof.
  pose proof c7_4_res as H. pose proof c7_4_res2 as H2. pose proof c7_4_lb as Hb.
  unfold rc7_4 in H. unfold rb7_4 in H2. unfold lb7_4 in Hb.
  unfold c8_5, rc8_5. cbn [Z.of_N] in *. gl c7_4.
Qed.
Lemma c8_5_res2 : (Z.of_nat c8_5 mod Z.of_N 32 = Z.of_N rb8_5)%Z.
Proof.
  pose proof c7_4_res as H. pose proof c7_4_res2 as H2. pose proof c7_4_lb as Hb.
  unfold rc7_4 in H. unfold rb7_4 in H2. unfold lb7_4 in Hb.
  unfold c8_5, rb8_5. cbn [Z.of_N] in *. gl c7_4.
Qed.
Lemma c8_5_lb : (Z.of_N lb8_5 <= Z.of_nat c8_5)%Z.
Proof.
  pose proof c7_4_res as H. pose proof c7_4_res2 as H2. pose proof c7_4_lb as Hb.
  unfold rc7_4 in H. unfold rb7_4 in H2. unfold lb7_4 in Hb.
  unfold c8_5, lb8_5. cbn [Z.of_N] in *. gl c7_4.
Qed.

Definition rc8_6 : N := Eval vm_compute in
  Z.to_N (((((Z.of_N rc7_5 - 0) * 1) mod 2187) / 3) mod 729).
Definition lb8_6 : N := Eval vm_compute in (((lb7_5 - 0) / 1) / 3)%N.
Definition rb8_6 : N := Eval vm_compute in
  Z.to_N (((((Z.of_N rb7_5 - 0) mod 32) / 1 - 0) * 11) mod 32).
Lemma c8_6_res : (Z.of_nat c8_6 mod Z.of_N 729 = Z.of_N rc8_6)%Z.
Proof.
  pose proof c7_5_res as H. pose proof c7_5_res2 as H2. pose proof c7_5_lb as Hb.
  unfold rc7_5 in H. unfold rb7_5 in H2. unfold lb7_5 in Hb.
  unfold c8_6, rc8_6. cbn [Z.of_N] in *. gl c7_5.
Qed.
Lemma c8_6_res2 : (Z.of_nat c8_6 mod Z.of_N 32 = Z.of_N rb8_6)%Z.
Proof.
  pose proof c7_5_res as H. pose proof c7_5_res2 as H2. pose proof c7_5_lb as Hb.
  unfold rc7_5 in H. unfold rb7_5 in H2. unfold lb7_5 in Hb.
  unfold c8_6, rb8_6. cbn [Z.of_N] in *. gl c7_5.
Qed.
Lemma c8_6_lb : (Z.of_N lb8_6 <= Z.of_nat c8_6)%Z.
Proof.
  pose proof c7_5_res as H. pose proof c7_5_res2 as H2. pose proof c7_5_lb as Hb.
  unfold rc7_5 in H. unfold rb7_5 in H2. unfold lb7_5 in Hb.
  unfold c8_6, lb8_6. cbn [Z.of_N] in *. gl c7_5.
Qed.

(** ** The word of level 8 modulo 3^6 *)

Definition vT8 : Z := Eval vm_compute in
  gv (resW 729 [RL a8_0; RR P8_1 729 rc8_1; RL a8_1; RR P8_2 729 rc8_2; RL a8_2; RR P8_3 729 rc8_3; RL
    a8_3; RR P8_4 729 rc8_4; RL a8_4; RR P8_5 729 rc8_5; RL a8_5; RR P8_6 729 rc8_6; RL a8_6]).

Lemma T8_res : (Z.of_nat (bval (b8 c8_1 c8_2 c8_3 c8_4 c8_5 c8_6)) mod 729 = vT8)%Z.
Proof.
  unfold b8.
  apply (resW_sound 729 [Lit a8_0; Rep P8_1 c8_1; Lit a8_1; Rep P8_2 c8_2; Lit a8_2; Rep P8_3 c8_3;
    Lit a8_3; Rep P8_4 c8_4; Lit a8_4; Rep P8_5 c8_5; Lit a8_5; Rep P8_6 c8_6; Lit a8_6]
           [RL a8_0; RR P8_1 729 rc8_1; RL a8_1; RR P8_2 729 rc8_2; RL a8_2; RR P8_3 729 rc8_3; RL a8_3; RR
            P8_4 729 rc8_4; RL a8_4; RR P8_5 729 rc8_5; RL a8_5; RR P8_6 729 rc8_6; RL a8_6]);
    [lia | | vm_compute; reflexivity].
  exact (Forall2_cons _ _ (mL a8_0)
    (Forall2_cons _ _ (mR P8_1 c8_1 729%N rc8_1 c8_1_res)
    (Forall2_cons _ _ (mL a8_1)
    (Forall2_cons _ _ (mR P8_2 c8_2 729%N rc8_2 c8_2_res)
    (Forall2_cons _ _ (mL a8_2)
    (Forall2_cons _ _ (mR P8_3 c8_3 729%N rc8_3 c8_3_res)
    (Forall2_cons _ _ (mL a8_3)
    (Forall2_cons _ _ (mR P8_4 c8_4 729%N rc8_4 c8_4_res)
    (Forall2_cons _ _ (mL a8_4)
    (Forall2_cons _ _ (mR P8_5 c8_5 729%N rc8_5 c8_5_res)
    (Forall2_cons _ _ (mL a8_5)
    (Forall2_cons _ _ (mR P8_6 c8_6 729%N rc8_6 c8_6_res)
    (Forall2_cons _ _ (mL a8_6) (Forall2_nil _)))))))))))))).
Qed.

Definition lbe8 : N := Eval vm_compute in bvalN a8_6.

Lemma T8_lb : forall d1 d2 d3 d4 d5 d6, (Z.of_N lbe8 <= Z.of_nat (bval (b8 d1 d2 d3 d4 d5 d6)))%Z.
Proof.
  intros d1 d2 d3 d4 d5 d6. unfold b8. change lbe8 with (bvalN a8_6).
  exact (lbZ [Lit a8_0; Rep P8_1 d1; Lit a8_1; Rep P8_2 d2; Lit a8_2; Rep P8_3 d3; Lit a8_3; Rep P8_4
    d4; Lit a8_4; Rep P8_5 d5; Lit a8_5; Rep P8_6 d6] a8_6).
Qed.

Definition t2_8 : N := Eval vm_compute in bvalN a8_0.

Lemma T8_low : forall d1 d2 d3 d4 d5 d6, (Z.of_nat (bval (b8 d1 d2 d3 d4 d5 d6)) mod 16 = Z.of_N t2_8)%Z.
Proof.
  intros d1 d2 d3 d4 d5 d6. unfold b8.
  exact (bval_low_den a8_0 [Rep P8_1 d1; Lit a8_1; Rep P8_2 d2; Lit a8_2; Rep P8_3 d3; Lit a8_3; Rep
    P8_4 d4; Lit a8_4; Rep P8_5 d5; Lit a8_5; Rep P8_6 d6; Lit a8_6]).
Qed.

End L78b.

Module L89a.

(** * 1RB1LB_1RC0RD_0LA1RE_0RF1LC_1LA0RB_---1LC: the end phase of level 8

    Level 8 has class 3 and a counter word with 6 repeated blocks.  The end phase is
    certified round by round ([crun_run]): a run to the first block, then for each block a
    cycle per copy and a run across the next junction, and a closing computation.  The cuts
    are computed from the rounds of one instance.  Generated by a script. *)

Import Individual62.
Import T694_levels End694 Sym694 Lev694 Lvl1_694 Eng694 Cert694 Run694 Res694 Gen694.
Import L23 L34 L45 L56 L6i L67a L67b L78a L78b.
Import Lia Arith PeanoNat Bool NArith ZArith.
Import Coq.Lists.List.
Import ListNotations.

(** ** The cells of the counter word *)

Definition pa8_0 : bool := Eval vm_compute in par false a8_0.
Lemma pa8_0_eq : par false a8_0 = pa8_0.
Proof. vm_compute. reflexivity. Qed.
Definition pa8_1 : bool := Eval vm_compute in par pa8_0 a8_1.
Lemma pa8_1_eq : par pa8_0 a8_1 = pa8_1.
Proof. vm_compute. reflexivity. Qed.
Definition pa8_2 : bool := Eval vm_compute in par pa8_1 a8_2.
Lemma pa8_2_eq : par pa8_1 a8_2 = pa8_2.
Proof. vm_compute. reflexivity. Qed.
Definition pa8_3 : bool := Eval vm_compute in par pa8_2 a8_3.
Lemma pa8_3_eq : par pa8_2 a8_3 = pa8_3.
Proof. vm_compute. reflexivity. Qed.
Definition pa8_4 : bool := Eval vm_compute in par pa8_3 a8_4.
Lemma pa8_4_eq : par pa8_3 a8_4 = pa8_4.
Proof. vm_compute. reflexivity. Qed.
Definition pa8_5 : bool := Eval vm_compute in par pa8_4 a8_5.
Lemma pa8_5_eq : par pa8_4 a8_5 = pa8_5.
Proof. vm_compute. reflexivity. Qed.
Lemma pp8_1 : par pa8_0 P8_1 = pa8_0.
Proof. vm_compute. reflexivity. Qed.
Lemma pp8_2 : par pa8_1 P8_2 = pa8_1.
Proof. vm_compute. reflexivity. Qed.
Lemma pp8_3 : par pa8_2 P8_3 = pa8_2.
Proof. vm_compute. reflexivity. Qed.
Lemma pp8_4 : par pa8_3 P8_4 = pa8_3.
Proof. vm_compute. reflexivity. Qed.
Lemma pp8_5 : par pa8_4 P8_5 = pa8_4.
Proof. vm_compute. reflexivity. Qed.
Lemma pp8_6 : par pa8_5 P8_6 = pa8_5.
Proof. vm_compute. reflexivity. Qed.

Definition Hd8 : list bool := rep10 je8 ++ c1101 ++ encb false a8_0.
Definition E8_1 : list bool := encb pa8_0 P8_1.
Definition J8_1 : list bool := encb pa8_0 a8_1.
Definition E8_2 : list bool := encb pa8_1 P8_2.
Definition J8_2 : list bool := encb pa8_1 a8_2.
Definition E8_3 : list bool := encb pa8_2 P8_3.
Definition J8_3 : list bool := encb pa8_2 a8_3.
Definition E8_4 : list bool := encb pa8_3 P8_4.
Definition J8_4 : list bool := encb pa8_3 a8_4.
Definition E8_5 : list bool := encb pa8_4 P8_5.
Definition J8_5 : list bool := encb pa8_4 a8_5.
Definition E8_6 : list bool := encb pa8_5 P8_6.
Definition J8_6 : list bool := encb pa8_5 a8_6.

Definition cells8 (c1 c2 c3 c4 c5 c6 : nat) : list bool :=
  rep10 je8 ++ c1101 ++ encb false (b8 c1 c2 c3 c4 c5 c6) ++ w8.

Lemma cells8_eq : forall c1 c2 c3 c4 c5 c6,
  cells8 c1 c2 c3 c4 c5 c6 = Hd8 ++ rp E8_1 c1 ++ J8_1 ++ rp E8_2 c2 ++ J8_2 ++ rp E8_3 c3 ++ J8_3 ++
    rp E8_4 c4 ++ J8_4 ++ rp E8_5 c5 ++ J8_5 ++ rp E8_6 c6 ++ J8_6 ++ w8.
Proof.
  intros c1 c2 c3 c4 c5 c6. unfold cells8, b8, Hd8, E8_1, J8_1, E8_2, J8_2, E8_3, J8_3, E8_4, J8_4, E8_5, J8_5, E8_6, J8_6.
  cbn [den bden]. rewrite app_nil_r.
  rewrite (encb_app a8_0), pa8_0_eq.
  rewrite (encb_rp P8_1 pa8_0 pp8_1), (encb_app a8_1), pa8_1_eq.
  rewrite (encb_rp P8_2 pa8_1 pp8_2), (encb_app a8_2), pa8_2_eq.
  rewrite (encb_rp P8_3 pa8_2 pp8_3), (encb_app a8_3), pa8_3_eq.
  rewrite (encb_rp P8_4 pa8_3 pp8_4), (encb_app a8_4), pa8_4_eq.
  rewrite (encb_rp P8_5 pa8_4 pp8_5), (encb_app a8_5), pa8_5_eq.
  rewrite (encb_rp P8_6 pa8_5 pp8_6).
  rewrite <- ?app_assoc. reflexivity.
Qed.

(** ** Boundaries, computed from the rounds of one instance *)

Definition look8_1 : nat := 36.
Definition dep8_1 : nat := 1.
Definition p8_1 : nat := Eval vm_compute in length E8_1.
Definition N8_1 : nat := Eval vm_compute in
  let b0 := (look8_1 / p8_1 + dep8_1 + 14)%nat in
  (b0 + N.to_nat ((rb8_1 + 4 * 1024 - N.of_nat b0) mod 4)%N)%nat.
Definition look8_2 : nat := 36.
Definition dep8_2 : nat := 1.
Definition p8_2 : nat := Eval vm_compute in length E8_2.
Definition N8_2 : nat := Eval vm_compute in
  let b0 := (look8_2 / p8_2 + dep8_2 + 14)%nat in
  (b0 + N.to_nat ((rb8_2 + 4 * 1024 - N.of_nat b0) mod 4)%N)%nat.
Definition look8_3 : nat := 36.
Definition dep8_3 : nat := 1.
Definition p8_3 : nat := Eval vm_compute in length E8_3.
Definition N8_3 : nat := Eval vm_compute in
  let b0 := (look8_3 / p8_3 + dep8_3 + 14)%nat in
  (b0 + N.to_nat ((rb8_3 + 4 * 1024 - N.of_nat b0) mod 4)%N)%nat.
Definition look8_4 : nat := 36.
Definition dep8_4 : nat := 1.
Definition p8_4 : nat := Eval vm_compute in length E8_4.
Definition N8_4 : nat := Eval vm_compute in
  let b0 := (look8_4 / p8_4 + dep8_4 + 14)%nat in
  (b0 + N.to_nat ((rb8_4 + 4 * 1024 - N.of_nat b0) mod 4)%N)%nat.
Definition look8_5 : nat := 36.
Definition dep8_5 : nat := 1.
Definition p8_5 : nat := Eval vm_compute in length E8_5.
Definition N8_5 : nat := Eval vm_compute in
  let b0 := (look8_5 / p8_5 + dep8_5 + 14)%nat in
  (b0 + N.to_nat ((rb8_5 + 4 * 1024 - N.of_nat b0) mod 4)%N)%nat.
Definition look8_6 : nat := 36.
Definition dep8_6 : nat := 1.
Definition p8_6 : nat := Eval vm_compute in length E8_6.
Definition N8_6 : nat := Eval vm_compute in
  let b0 := (look8_6 / p8_6 + dep8_6 + 14)%nat in
  (b0 + N.to_nat ((rb8_6 + 4 * 1024 - N.of_nat b0) mod 4)%N)%nat.
Definition looke8 : nat := 36.
Definition inst8 : list bool := cells8 N8_1 N8_2 N8_3 N8_4 N8_5 N8_6.
Definition s8_1 : N := Eval vm_compute in N.of_nat (length Hd8).
Definition s8_2 : N := Eval vm_compute in
  (s8_1 + N.of_nat (N8_1 * p8_1 + length J8_1))%N.
Definition s8_3 : N := Eval vm_compute in
  (s8_2 + N.of_nat (N8_2 * p8_2 + length J8_2))%N.
Definition s8_4 : N := Eval vm_compute in
  (s8_3 + N.of_nat (N8_3 * p8_3 + length J8_3))%N.
Definition s8_5 : N := Eval vm_compute in
  (s8_4 + N.of_nat (N8_4 * p8_4 + length J8_4))%N.
Definition s8_6 : N := Eval vm_compute in
  (s8_5 + N.of_nat (N8_5 * p8_5 + length J8_5))%N.
Definition s8_7 : N := Eval vm_compute in
  (s8_6 + N.of_nat (N8_6 * p8_6 + length J8_6))%N.
Definition tr8 : list (N * N * N) := Eval vm_compute in
  gtrace 36 (length inst8) 0 0 0 (c1101, true, inst8).
Definition f8_1 : N * N * N * N := Eval vm_compute in
  gfindk (N.of_nat p8_1) (s8_1 + N.of_nat (dep8_1 * p8_1))
         (s8_1 + N.of_nat (N8_1 * p8_1) - N.of_nat look8_1) (1%N :: 2%N :: 4%N :: nil) tr8.
Definition rr8_1 : nat := Eval vm_compute in N.to_nat (fst (fst (fst f8_1))).
Definition R8_1 : nat := Eval vm_compute in N.to_nat (snd (fst f8_1)).
Definition kq8_1 : nat := Eval vm_compute in N.to_nat (snd f8_1).
Definition cc8_1 : nat := Eval vm_compute in N.to_nat ((snd (fst (fst f8_1)) + N.of_nat look8_1 - s8_1) / N.of_nat p8_1).
Definition uu8_1 : nat := Eval vm_compute in N.to_nat ((snd (fst (fst f8_1)) + N.of_nat look8_1 - s8_1) mod N.of_nat p8_1).
Definition jj8_1 : nat := Eval vm_compute in (N8_1 - cc8_1 - 1) mod kq8_1.
Definition S8_1 : sst := Eval vm_compute in
  gcut look8_1 (grst rr8_1 (c1101, true, inst8)).
Definition f8_2 : N * N * N * N := Eval vm_compute in
  gfindk (N.of_nat p8_2) (s8_2 + N.of_nat (dep8_2 * p8_2))
         (s8_2 + N.of_nat (N8_2 * p8_2) - N.of_nat look8_2) (1%N :: 2%N :: 4%N :: nil) tr8.
Definition rr8_2 : nat := Eval vm_compute in N.to_nat (fst (fst (fst f8_2))).
Definition R8_2 : nat := Eval vm_compute in N.to_nat (snd (fst f8_2)).
Definition kq8_2 : nat := Eval vm_compute in N.to_nat (snd f8_2).
Definition cc8_2 : nat := Eval vm_compute in N.to_nat ((snd (fst (fst f8_2)) + N.of_nat look8_2 - s8_2) / N.of_nat p8_2).
Definition uu8_2 : nat := Eval vm_compute in N.to_nat ((snd (fst (fst f8_2)) + N.of_nat look8_2 - s8_2) mod N.of_nat p8_2).
Definition jj8_2 : nat := Eval vm_compute in (N8_2 - cc8_2 - 1) mod kq8_2.
Definition S8_2 : sst := Eval vm_compute in
  gcut look8_2 (grst rr8_2 (c1101, true, inst8)).
Definition f8_3 : N * N * N * N := Eval vm_compute in
  gfindk (N.of_nat p8_3) (s8_3 + N.of_nat (dep8_3 * p8_3))
         (s8_3 + N.of_nat (N8_3 * p8_3) - N.of_nat look8_3) (1%N :: 2%N :: 4%N :: nil) tr8.
Definition rr8_3 : nat := Eval vm_compute in N.to_nat (fst (fst (fst f8_3))).
Definition R8_3 : nat := Eval vm_compute in N.to_nat (snd (fst f8_3)).
Definition kq8_3 : nat := Eval vm_compute in N.to_nat (snd f8_3).
Definition cc8_3 : nat := Eval vm_compute in N.to_nat ((snd (fst (fst f8_3)) + N.of_nat look8_3 - s8_3) / N.of_nat p8_3).
Definition uu8_3 : nat := Eval vm_compute in N.to_nat ((snd (fst (fst f8_3)) + N.of_nat look8_3 - s8_3) mod N.of_nat p8_3).
Definition jj8_3 : nat := Eval vm_compute in (N8_3 - cc8_3 - 1) mod kq8_3.
Definition S8_3 : sst := Eval vm_compute in
  gcut look8_3 (grst rr8_3 (c1101, true, inst8)).
Definition f8_4 : N * N * N * N := Eval vm_compute in
  gfindk (N.of_nat p8_4) (s8_4 + N.of_nat (dep8_4 * p8_4))
         (s8_4 + N.of_nat (N8_4 * p8_4) - N.of_nat look8_4) (1%N :: 2%N :: 4%N :: nil) tr8.
Definition rr8_4 : nat := Eval vm_compute in N.to_nat (fst (fst (fst f8_4))).
Definition R8_4 : nat := Eval vm_compute in N.to_nat (snd (fst f8_4)).
Definition kq8_4 : nat := Eval vm_compute in N.to_nat (snd f8_4).
Definition cc8_4 : nat := Eval vm_compute in N.to_nat ((snd (fst (fst f8_4)) + N.of_nat look8_4 - s8_4) / N.of_nat p8_4).
Definition uu8_4 : nat := Eval vm_compute in N.to_nat ((snd (fst (fst f8_4)) + N.of_nat look8_4 - s8_4) mod N.of_nat p8_4).
Definition jj8_4 : nat := Eval vm_compute in (N8_4 - cc8_4 - 1) mod kq8_4.
Definition S8_4 : sst := Eval vm_compute in
  gcut look8_4 (grst rr8_4 (c1101, true, inst8)).
Definition f8_5 : N * N * N * N := Eval vm_compute in
  gfindk (N.of_nat p8_5) (s8_5 + N.of_nat (dep8_5 * p8_5))
         (s8_5 + N.of_nat (N8_5 * p8_5) - N.of_nat look8_5) (1%N :: 2%N :: 4%N :: nil) tr8.
Definition rr8_5 : nat := Eval vm_compute in N.to_nat (fst (fst (fst f8_5))).
Definition R8_5 : nat := Eval vm_compute in N.to_nat (snd (fst f8_5)).
Definition kq8_5 : nat := Eval vm_compute in N.to_nat (snd f8_5).
Definition cc8_5 : nat := Eval vm_compute in N.to_nat ((snd (fst (fst f8_5)) + N.of_nat look8_5 - s8_5) / N.of_nat p8_5).
Definition uu8_5 : nat := Eval vm_compute in N.to_nat ((snd (fst (fst f8_5)) + N.of_nat look8_5 - s8_5) mod N.of_nat p8_5).
Definition jj8_5 : nat := Eval vm_compute in (N8_5 - cc8_5 - 1) mod kq8_5.
Definition S8_5 : sst := Eval vm_compute in
  gcut look8_5 (grst rr8_5 (c1101, true, inst8)).
Definition f8_6 : N * N * N * N := Eval vm_compute in
  gfindk (N.of_nat p8_6) (s8_6 + N.of_nat (dep8_6 * p8_6))
         (s8_6 + N.of_nat (N8_6 * p8_6) - N.of_nat look8_6) (1%N :: 2%N :: 4%N :: nil) tr8.
Definition rr8_6 : nat := Eval vm_compute in N.to_nat (fst (fst (fst f8_6))).
Definition R8_6 : nat := Eval vm_compute in N.to_nat (snd (fst f8_6)).
Definition kq8_6 : nat := Eval vm_compute in N.to_nat (snd f8_6).
Definition cc8_6 : nat := Eval vm_compute in N.to_nat ((snd (fst (fst f8_6)) + N.of_nat look8_6 - s8_6) / N.of_nat p8_6).
Definition uu8_6 : nat := Eval vm_compute in N.to_nat ((snd (fst (fst f8_6)) + N.of_nat look8_6 - s8_6) mod N.of_nat p8_6).
Definition jj8_6 : nat := Eval vm_compute in (N8_6 - cc8_6 - 1) mod kq8_6.
Definition S8_6 : sst := Eval vm_compute in
  gcut look8_6 (grst rr8_6 (c1101, true, inst8)).
Definition fe8 : N * N := Eval vm_compute in
  glast (s8_7 - N.of_nat (looke8 + 60)) tr8 (0, 0)%N.
Definition rre8 : nat := Eval vm_compute in N.to_nat (fst fe8).
Definition ue8 : nat := Eval vm_compute in
  N.to_nat (snd fe8 + N.of_nat looke8 - (s8_6 + N.of_nat (N8_6 * p8_6))).
Definition Se8 : sst := Eval vm_compute in gcut looke8 (grst rre8 (c1101, true, inst8)).
Definition Rj8_0 : nat := rr8_1.
Definition Rj8_1 : nat := Eval vm_compute in
  rr8_2 - rr8_1 - R8_1 * ((N8_1 - cc8_1 - 1 - jj8_1) / kq8_1).
Definition Rj8_2 : nat := Eval vm_compute in
  rr8_3 - rr8_2 - R8_2 * ((N8_2 - cc8_2 - 1 - jj8_2) / kq8_2).
Definition Rj8_3 : nat := Eval vm_compute in
  rr8_4 - rr8_3 - R8_3 * ((N8_3 - cc8_3 - 1 - jj8_3) / kq8_3).
Definition Rj8_4 : nat := Eval vm_compute in
  rr8_5 - rr8_4 - R8_4 * ((N8_4 - cc8_4 - 1 - jj8_4) / kq8_4).
Definition Rj8_5 : nat := Eval vm_compute in
  rr8_6 - rr8_5 - R8_5 * ((N8_5 - cc8_5 - 1 - jj8_5) / kq8_5).
Definition Rj8_6 : nat := Eval vm_compute in
  rre8 - rr8_6 - R8_6 * ((N8_6 - cc8_6 - 1 - jj8_6) / kq8_6).

(** ** The cuts *)

Definition u8_1 : list bool := firstn uu8_1 E8_1.
Definition v8_1 : list bool := skipn uu8_1 E8_1.
Definition u8_2 : list bool := firstn uu8_2 E8_2.
Definition v8_2 : list bool := skipn uu8_2 E8_2.
Definition u8_3 : list bool := firstn uu8_3 E8_3.
Definition v8_3 : list bool := skipn uu8_3 E8_3.
Definition u8_4 : list bool := firstn uu8_4 E8_4.
Definition v8_4 : list bool := skipn uu8_4 E8_4.
Definition u8_5 : list bool := firstn uu8_5 E8_5.
Definition v8_5 : list bool := skipn uu8_5 E8_5.
Definition u8_6 : list bool := firstn uu8_6 E8_6.
Definition v8_6 : list bool := skipn uu8_6 E8_6.
Definition F8_0 : list bool := Hd8 ++ rp E8_1 cc8_1 ++ u8_1.
Definition C8_1 : list bool := v8_1 ++ u8_1.
Definition K8_1 : list bool := rp C8_1 kq8_1.
Lemma tl8_1 : rp E8_1 (jj8_1 + 1) = u8_1 ++ rp C8_1 jj8_1 ++ v8_1.
Proof. vm_compute. reflexivity. Qed.
Definition F8_1 : list bool :=
  (rp C8_1 jj8_1 ++ v8_1) ++ J8_1 ++ rp E8_2 cc8_2 ++ u8_2.
Definition C8_2 : list bool := v8_2 ++ u8_2.
Definition K8_2 : list bool := rp C8_2 kq8_2.
Lemma tl8_2 : rp E8_2 (jj8_2 + 1) = u8_2 ++ rp C8_2 jj8_2 ++ v8_2.
Proof. vm_compute. reflexivity. Qed.
Definition F8_2 : list bool :=
  (rp C8_2 jj8_2 ++ v8_2) ++ J8_2 ++ rp E8_3 cc8_3 ++ u8_3.
Definition C8_3 : list bool := v8_3 ++ u8_3.
Definition K8_3 : list bool := rp C8_3 kq8_3.
Lemma tl8_3 : rp E8_3 (jj8_3 + 1) = u8_3 ++ rp C8_3 jj8_3 ++ v8_3.
Proof. vm_compute. reflexivity. Qed.
Definition F8_3 : list bool :=
  (rp C8_3 jj8_3 ++ v8_3) ++ J8_3 ++ rp E8_4 cc8_4 ++ u8_4.
Definition C8_4 : list bool := v8_4 ++ u8_4.
Definition K8_4 : list bool := rp C8_4 kq8_4.
Lemma tl8_4 : rp E8_4 (jj8_4 + 1) = u8_4 ++ rp C8_4 jj8_4 ++ v8_4.
Proof. vm_compute. reflexivity. Qed.
Definition F8_4 : list bool :=
  (rp C8_4 jj8_4 ++ v8_4) ++ J8_4 ++ rp E8_5 cc8_5 ++ u8_5.
Definition C8_5 : list bool := v8_5 ++ u8_5.
Definition K8_5 : list bool := rp C8_5 kq8_5.
Lemma tl8_5 : rp E8_5 (jj8_5 + 1) = u8_5 ++ rp C8_5 jj8_5 ++ v8_5.
Proof. vm_compute. reflexivity. Qed.
Definition F8_5 : list bool :=
  (rp C8_5 jj8_5 ++ v8_5) ++ J8_5 ++ rp E8_6 cc8_6 ++ u8_6.
Definition C8_6 : list bool := v8_6 ++ u8_6.
Definition K8_6 : list bool := rp C8_6 kq8_6.
Lemma tl8_6 : rp E8_6 (jj8_6 + 1) = u8_6 ++ rp C8_6 jj8_6 ++ v8_6.
Proof. vm_compute. reflexivity. Qed.
Definition F8_6 : list bool := (rp C8_6 jj8_6 ++ v8_6) ++ firstn ue8 J8_6.
Definition Fw8 : list bool := skipn ue8 J8_6 ++ w8.

Lemma cells8_cut : forall n1 n2 n3 n4 n5 n6,
  cells8 (cc8_1 + (n1 * kq8_1 + jj8_1) + 1) (cc8_2 + (n2 * kq8_2 + jj8_2) + 1) (cc8_3 + (n3 * kq8_3 +
    jj8_3) + 1) (cc8_4 + (n4 * kq8_4 + jj8_4) + 1) (cc8_5 + (n5 * kq8_5 + jj8_5) + 1) (cc8_6 + (n6 *
    kq8_6 + jj8_6) + 1) = (F8_0 ++ rp K8_1 n1 ++ F8_1 ++ rp K8_2 n2 ++ F8_2 ++ rp K8_3 n3 ++ F8_3 ++
    rp K8_4 n4 ++ F8_4 ++ rp K8_5 n5 ++ F8_5 ++ rp K8_6 n6 ++ F8_6 ++ []) ++ Fw8.
Proof.
  intros n1 n2 n3 n4 n5 n6. rewrite cells8_eq.
  replace (cc8_1 + (n1 * kq8_1 + jj8_1) + 1) with (cc8_1 + n1 * kq8_1 + (jj8_1 + 1)) by lia.
  rewrite (rp_recut E8_1 u8_1 v8_1 (n1 * kq8_1) cc8_1 (jj8_1 + 1) (rp C8_1 jj8_1 ++ v8_1)
             (eq_sym (firstn_skipn uu8_1 E8_1)) tl8_1).
  rewrite (rp_mul (v8_1 ++ u8_1) kq8_1 n1).
  replace (cc8_2 + (n2 * kq8_2 + jj8_2) + 1) with (cc8_2 + n2 * kq8_2 + (jj8_2 + 1)) by lia.
  rewrite (rp_recut E8_2 u8_2 v8_2 (n2 * kq8_2) cc8_2 (jj8_2 + 1) (rp C8_2 jj8_2 ++ v8_2)
             (eq_sym (firstn_skipn uu8_2 E8_2)) tl8_2).
  rewrite (rp_mul (v8_2 ++ u8_2) kq8_2 n2).
  replace (cc8_3 + (n3 * kq8_3 + jj8_3) + 1) with (cc8_3 + n3 * kq8_3 + (jj8_3 + 1)) by lia.
  rewrite (rp_recut E8_3 u8_3 v8_3 (n3 * kq8_3) cc8_3 (jj8_3 + 1) (rp C8_3 jj8_3 ++ v8_3)
             (eq_sym (firstn_skipn uu8_3 E8_3)) tl8_3).
  rewrite (rp_mul (v8_3 ++ u8_3) kq8_3 n3).
  replace (cc8_4 + (n4 * kq8_4 + jj8_4) + 1) with (cc8_4 + n4 * kq8_4 + (jj8_4 + 1)) by lia.
  rewrite (rp_recut E8_4 u8_4 v8_4 (n4 * kq8_4) cc8_4 (jj8_4 + 1) (rp C8_4 jj8_4 ++ v8_4)
             (eq_sym (firstn_skipn uu8_4 E8_4)) tl8_4).
  rewrite (rp_mul (v8_4 ++ u8_4) kq8_4 n4).
  replace (cc8_5 + (n5 * kq8_5 + jj8_5) + 1) with (cc8_5 + n5 * kq8_5 + (jj8_5 + 1)) by lia.
  rewrite (rp_recut E8_5 u8_5 v8_5 (n5 * kq8_5) cc8_5 (jj8_5 + 1) (rp C8_5 jj8_5 ++ v8_5)
             (eq_sym (firstn_skipn uu8_5 E8_5)) tl8_5).
  rewrite (rp_mul (v8_5 ++ u8_5) kq8_5 n5).
  replace (cc8_6 + (n6 * kq8_6 + jj8_6) + 1) with (cc8_6 + n6 * kq8_6 + (jj8_6 + 1)) by lia.
  rewrite (rp_recut E8_6 u8_6 v8_6 (n6 * kq8_6) cc8_6 (jj8_6 + 1) (rp C8_6 jj8_6 ++ v8_6)
             (eq_sym (firstn_skipn uu8_6 E8_6)) tl8_6).
  rewrite (rp_mul (v8_6 ++ u8_6) kq8_6 n6).
  rewrite <- (firstn_skipn ue8 J8_6) at 1.
  unfold F8_0, K8_1, F8_1, C8_1, K8_2, F8_2, C8_2, K8_3, F8_3, C8_3, K8_4, F8_4, C8_4, K8_5, F8_5, C8_5, K8_6, F8_6, C8_6, Fw8.
  rewrite ?app_nil_r, <- ?app_assoc. reflexivity.
Qed.

(** ** Runs and cycles, round by round *)

Definition st80 : sst := (c1101, true, []).
Definition lF8_0 : list (Z * nat) := Eval vm_compute in grl Rj8_0 st80 F8_0.
Lemma RF8_0 : Run st80 F8_0 S8_1 (pSh lF8_0) (pV lF8_0).
Proof. apply (crun_run Rj8_0 4). vm_compute. reflexivity. Qed.
Definition lC8_1 : list (Z * nat) := Eval vm_compute in grl R8_1 S8_1 K8_1.
Lemma RC8_1 : Run S8_1 K8_1 S8_1 (pSh lC8_1) (pV lC8_1).
Proof. apply (crun_run R8_1 4). vm_compute. reflexivity. Qed.
Definition lF8_1 : list (Z * nat) := Eval vm_compute in grl Rj8_1 S8_1 F8_1.
Lemma RF8_1 : Run S8_1 F8_1 S8_2 (pSh lF8_1) (pV lF8_1).
Proof. apply (crun_run Rj8_1 4). vm_compute. reflexivity. Qed.
Definition lC8_2 : list (Z * nat) := Eval vm_compute in grl R8_2 S8_2 K8_2.
Lemma RC8_2 : Run S8_2 K8_2 S8_2 (pSh lC8_2) (pV lC8_2).
Proof. apply (crun_run R8_2 4). vm_compute. reflexivity. Qed.
Definition lF8_2 : list (Z * nat) := Eval vm_compute in grl Rj8_2 S8_2 F8_2.
Lemma RF8_2 : Run S8_2 F8_2 S8_3 (pSh lF8_2) (pV lF8_2).
Proof. apply (crun_run Rj8_2 4). vm_compute. reflexivity. Qed.
Definition lC8_3 : list (Z * nat) := Eval vm_compute in grl R8_3 S8_3 K8_3.
Lemma RC8_3 : Run S8_3 K8_3 S8_3 (pSh lC8_3) (pV lC8_3).
Proof. apply (crun_run R8_3 4). vm_compute. reflexivity. Qed.
Definition lF8_3 : list (Z * nat) := Eval vm_compute in grl Rj8_3 S8_3 F8_3.
Lemma RF8_3 : Run S8_3 F8_3 S8_4 (pSh lF8_3) (pV lF8_3).
Proof. apply (crun_run Rj8_3 4). vm_compute. reflexivity. Qed.
Definition lC8_4 : list (Z * nat) := Eval vm_compute in grl R8_4 S8_4 K8_4.
Lemma RC8_4 : Run S8_4 K8_4 S8_4 (pSh lC8_4) (pV lC8_4).
Proof. apply (crun_run R8_4 4). vm_compute. reflexivity. Qed.
Definition lF8_4 : list (Z * nat) := Eval vm_compute in grl Rj8_4 S8_4 F8_4.
Lemma RF8_4 : Run S8_4 F8_4 S8_5 (pSh lF8_4) (pV lF8_4).
Proof. apply (crun_run Rj8_4 4). vm_compute. reflexivity. Qed.
Definition lC8_5 : list (Z * nat) := Eval vm_compute in grl R8_5 S8_5 K8_5.
Lemma RC8_5 : Run S8_5 K8_5 S8_5 (pSh lC8_5) (pV lC8_5).
Proof. apply (crun_run R8_5 4). vm_compute. reflexivity. Qed.
Definition lF8_5 : list (Z * nat) := Eval vm_compute in grl Rj8_5 S8_5 F8_5.
Lemma RF8_5 : Run S8_5 F8_5 S8_6 (pSh lF8_5) (pV lF8_5).
Proof. apply (crun_run Rj8_5 4). vm_compute. reflexivity. Qed.
Definition lC8_6 : list (Z * nat) := Eval vm_compute in grl R8_6 S8_6 K8_6.
Lemma RC8_6 : Run S8_6 K8_6 S8_6 (pSh lC8_6) (pV lC8_6).
Proof. apply (crun_run R8_6 4). vm_compute. reflexivity. Qed.
Definition lF8_6 : list (Z * nat) := Eval vm_compute in grl Rj8_6 S8_6 F8_6.
Lemma RF8_6 : Run S8_6 F8_6 Se8 (pSh lF8_6) (pV lF8_6).
Proof. apply (crun_run Rj8_6 4). vm_compute. reflexivity. Qed.

Definition segs8 (n1 n2 n3 n4 n5 n6 : nat) : list seg :=
  [SP lF8_0; SK lC8_1 n1; SP lF8_1; SK lC8_2 n2; SP lF8_2; SK lC8_3 n3; SP lF8_3; SK lC8_4 n4; SP
    lF8_4; SK lC8_5 n5; SP lF8_5; SK lC8_6 n6; SP lF8_6].

Lemma runA8 : forall n1 n2 n3 n4 n5 n6,
  Run st80 (F8_0 ++ rp K8_1 n1 ++ F8_1 ++ rp K8_2 n2 ++ F8_2 ++ rp K8_3 n3 ++ F8_3 ++ rp K8_4 n4 ++
    F8_4 ++ rp K8_5 n5 ++ F8_5 ++ rp K8_6 n6 ++ F8_6 ++ []) Se8
      (segSh (segs8 n1 n2 n3 n4 n5 n6)) (segV (segs8 n1 n2 n3 n4 n5 n6)).
Proof.
  intros n1 n2 n3 n4 n5 n6. unfold segs8.
  exact (run_SP _ _ _ _ _ _ _ RF8_0
    (run_SK _ _ _ _ _ _ _ RC8_1
    (run_SP _ _ _ _ _ _ _ RF8_1 (run_SK _ _ _ _ _ _ _ RC8_2
    (run_SP _ _ _ _ _ _ _ RF8_2 (run_SK _ _ _ _ _ _ _ RC8_3
    (run_SP _ _ _ _ _ _ _ RF8_3 (run_SK _ _ _ _ _ _ _ RC8_4
    (run_SP _ _ _ _ _ _ _ RF8_4 (run_SK _ _ _ _ _ _ _ RC8_5
    (run_SP _ _ _ _ _ _ _ RF8_5 (run_SK _ _ _ _ _ _ _ RC8_6
    (run_SP _ _ _ _ _ _ _ RF8_6 (run_end _)))))))))))))).
Qed.

(** ** The carry chain *)

Definition as8 := Eval vm_compute in asm 0 (segs8 O O O O O O).
Definition k8_0 : list bool := Eval vm_compute in
  match as8 with Some ([Lit a; _; _; _; _; _; _; _; _; _; _; _; _], _) => a | _ => [] end.
Definition k8_1 : list bool := Eval vm_compute in
  match as8 with Some ([_; _; Lit a; _; _; _; _; _; _; _; _; _; _], _) => a | _ => [] end.
Definition k8_2 : list bool := Eval vm_compute in
  match as8 with Some ([_; _; _; _; Lit a; _; _; _; _; _; _; _; _], _) => a | _ => [] end.
Definition k8_3 : list bool := Eval vm_compute in
  match as8 with Some ([_; _; _; _; _; _; Lit a; _; _; _; _; _; _], _) => a | _ => [] end.
Definition k8_4 : list bool := Eval vm_compute in
  match as8 with Some ([_; _; _; _; _; _; _; _; Lit a; _; _; _; _], _) => a | _ => [] end.
Definition k8_5 : list bool := Eval vm_compute in
  match as8 with Some ([_; _; _; _; _; _; _; _; _; _; Lit a; _; _], _) => a | _ => [] end.
Definition k8_6 : list bool := Eval vm_compute in
  match as8 with Some ([_; _; _; _; _; _; _; _; _; _; _; _; Lit a], _) => a | _ => [] end.
Definition kk8_1 : list bool := Eval vm_compute in
  match as8 with Some ([_; Rep p _; _; _; _; _; _; _; _; _; _; _; _], _) => p | _ => [] end.
Definition kk8_2 : list bool := Eval vm_compute in
  match as8 with Some ([_; _; _; Rep p _; _; _; _; _; _; _; _; _; _], _) => p | _ => [] end.
Definition kk8_3 : list bool := Eval vm_compute in
  match as8 with Some ([_; _; _; _; _; Rep p _; _; _; _; _; _; _; _], _) => p | _ => [] end.
Definition kk8_4 : list bool := Eval vm_compute in
  match as8 with Some ([_; _; _; _; _; _; _; Rep p _; _; _; _; _; _], _) => p | _ => [] end.
Definition kk8_5 : list bool := Eval vm_compute in
  match as8 with Some ([_; _; _; _; _; _; _; _; _; Rep p _; _; _; _], _) => p | _ => [] end.
Definition kk8_6 : list bool := Eval vm_compute in
  match as8 with Some ([_; _; _; _; _; _; _; _; _; _; _; Rep p _; _], _) => p | _ => [] end.
Definition cB8 : Z := Eval vm_compute in match as8 with Some (_, c) => c | None => (-1)%Z end.

Lemma as8_ok : forall n1 n2 n3 n4 n5 n6,
  asm 0 (segs8 n1 n2 n3 n4 n5 n6) = Some ([Lit k8_0; Rep kk8_1 n1; Lit k8_1; Rep kk8_2 n2; Lit k8_2;
    Rep kk8_3 n3; Lit k8_3; Rep kk8_4 n4; Lit k8_4; Rep kk8_5 n5; Lit k8_5; Rep kk8_6 n6; Lit k8_6],
    cB8).
Proof. intros n1 n2 n3 n4 n5 n6. vm_compute. reflexivity. Qed.

(** ** The closing computation *)

Definition ec8 := Eval vm_compute in endcert 6000 (addpost Se8 Fw8).
Definition ae8 : Z := Eval vm_compute in match ec8 with Some (a, _, _, _) => a | None => 0%Z end.
Definition z1_8 : nat := Eval vm_compute in match ec8 with Some (_, z, _, _) => z | None => O end.
Definition z2_8 : nat := Eval vm_compute in match ec8 with Some (_, _, z, _) => z | None => O end.
Definition w9 : list bool := Eval vm_compute in match ec8 with Some (_, _, _, x) => x | None => [] end.
Definition la8 : nat := Eval vm_compute in (z1_8 + z2_8 - 1) / 3.
Definition tp8 : N := Eval vm_compute in Z.to_N ((cB8 + ae8) / 4 ^ Z.of_nat la8).
Definition ab8 : list bool := Eval vm_compute in
  zbits ((cB8 + ae8) mod 4 ^ Z.of_nat la8) (2 * la8).

Lemma ec8_ok : endcert 6000 (addpost Se8 Fw8) = Some (ae8, z1_8, z2_8, w9).
Proof. vm_compute. reflexivity. Qed.

Lemma cB8_nn : (0 <= cB8)%Z.
Proof. apply Z.leb_le. vm_compute. reflexivity. Qed.

Lemma ab8_val : (Z.of_N (bvalN ab8) + Z.of_N tp8 * pw4 la8 = cB8 + ae8)%Z.
Proof. vm_compute. reflexivity. Qed.

Lemma ab8_len : length ab8 = 2 * la8.
Proof. vm_compute. reflexivity. Qed.

Lemma z_8 : z1_8 + z2_8 = 3 * la8 + 1.
Proof. vm_compute. reflexivity. Qed.

Definition Cw8 (n1 n2 n3 n4 n5 n6 : nat) : list bool :=
  den [Lit k8_0; Rep kk8_1 n1; Lit k8_1; Rep kk8_2 n2; Lit k8_2; Rep kk8_3 n3; Lit k8_3; Rep kk8_4 n4;
    Lit k8_4; Rep kk8_5 n5; Lit k8_5; Rep kk8_6 n6; Lit k8_6] ++ ab8.
Definition lc8 (n1 n2 n3 n4 n5 n6 : nat) : nat := segSh (segs8 n1 n2 n3 n4 n5 n6) + la8.

Lemma Cw8_len : forall n1 n2 n3 n4 n5 n6, length (Cw8 n1 n2 n3 n4 n5 n6) = 2 * lc8 n1 n2 n3 n4 n5 n6.
Proof.
  intros n1 n2 n3 n4 n5 n6.
  exact (proj1 (stageA st80 _ Se8 (segs8 n1 n2 n3 n4 n5 n6) 6000 Fw8 ae8 z1_8 z2_8 w9 _ cB8 ab8 la8
              (Z.of_N tp8) (runA8 n1 n2 n3 n4 n5 n6) ec8_ok (as8_ok n1 n2 n3 n4 n5 n6) cB8_nn ab8_val ab8_len z_8)).
Qed.

Lemma end8 : forall n1 n2 n3 n4 n5 n6 h k, (1 <= k)%nat -> exists n M',
  tickN 3 n (rep10 k ++ c1101 ++ repeat true (3 * h) ++ rep10 je8 ++ c1101 ++
             encb false (b8 (cc8_1 + (n1 * kq8_1 + jj8_1) + 1) (cc8_2 + (n2 * kq8_2 + jj8_2) + 1) (cc8_3 + (n3 *
               kq8_3 + jj8_3) + 1) (cc8_4 + (n4 * kq8_4 + jj8_4) + 1) (cc8_5 + (n5 * kq8_5 + jj8_5)
               + 1) (cc8_6 + (n6 * kq8_6 + jj8_6) + 1)) ++ w8) =
    Some (Slev M' (3 * (h + lc8 n1 n2 n3 n4 n5 n6) + 1) w9) /\
  Z.of_nat M' = (Z.of_nat k +
                 (Z.of_nat (bval (Cw8 n1 n2 n3 n4 n5 n6)) + Z.of_N tp8 * pw4 (lc8 n1 n2 n3 n4 n5 n6)) * pw4 h)%Z.
Proof.
  intros n1 n2 n3 n4 n5 n6 h k Hk.
  destruct (stageA st80 _ Se8 (segs8 n1 n2 n3 n4 n5 n6) 6000 Fw8 ae8 z1_8 z2_8 w9 _ cB8 ab8 la8
              (Z.of_N tp8) (runA8 n1 n2 n3 n4 n5 n6) ec8_ok (as8_ok n1 n2 n3 n4 n5 n6) cB8_nn ab8_val ab8_len z_8) as [_ H].
  destruct (H h k Hk) as [n [M' [E D]]]. exists n, M'. split; [| exact D].
  change (rep10 je8 ++ c1101 ++ encb false (b8 (cc8_1 + (n1 * kq8_1 + jj8_1) + 1) (cc8_2 + (n2 * kq8_2
    + jj8_2) + 1) (cc8_3 + (n3 * kq8_3 + jj8_3) + 1) (cc8_4 + (n4 * kq8_4 + jj8_4) + 1) (cc8_5 + (n5
    * kq8_5 + jj8_5) + 1) (cc8_6 + (n6 * kq8_6 + jj8_6) + 1)) ++ w8)
    with (cells8 (cc8_1 + (n1 * kq8_1 + jj8_1) + 1) (cc8_2 + (n2 * kq8_2 + jj8_2) + 1) (cc8_3 + (n3 * kq8_3 + jj8_3) + 1) (cc8_4 + (n4 * kq8_4 + jj8_4) + 1) (cc8_5 + (n5 * kq8_5 + jj8_5) + 1) (cc8_6 + (n6 * kq8_6 + jj8_6) + 1)).
  rewrite cells8_cut.
  cbv [st80 conc] in E. rewrite ?app_nil_r, <- ?app_assoc in E. rewrite ?app_nil_r, <- ?app_assoc.
  exact E.
Qed.

(** ** What the division needs: which blocks are tripled, and the residues of the counts *)

Definition cfg8_trip : list bool := Eval vm_compute in
  map (fun P => negb (N.eqb (bvalN P mod 3) 0)) [kk8_1; kk8_2; kk8_3; kk8_4; kk8_5; kk8_6].
Definition cfg8_rho : list N := Eval vm_compute in
  [(((rc8_1 + 1594323 - (N.of_nat cc8_1 + 1 + N.of_nat jj8_1)%N) * (N.of_nat kq8_1 mod 3)) mod 3)%N; (((rc8_2 + 1594323 - (N.of_nat cc8_2 + 1 + N.of_nat jj8_2)%N) * (N.of_nat kq8_2 mod 3)) mod 3)%N; (((rc8_3 + 1594323 - (N.of_nat cc8_3 + 1 + N.of_nat jj8_3)%N) * (N.of_nat kq8_3 mod 3)) mod 3)%N; (((rc8_4 + 1594323 - (N.of_nat cc8_4 + 1 + N.of_nat jj8_4)%N) * (N.of_nat kq8_4 mod 3)) mod 3)%N; (((rc8_5 + 1594323 - (N.of_nat cc8_5 + 1 + N.of_nat jj8_5)%N) * (N.of_nat kq8_5 mod 3)) mod 3)%N; (((rc8_6 + 1594323 - (N.of_nat cc8_6 + 1 + N.of_nat jj8_6)%N) * (N.of_nat kq8_6 mod 3)) mod 3)%N].
Definition cfg8_k : list nat := Eval vm_compute in [kq8_1; kq8_2; kq8_3; kq8_4; kq8_5; kq8_6].
Definition cfg8_j : list nat := Eval vm_compute in [jj8_1; jj8_2; jj8_3; jj8_4; jj8_5; jj8_6].
Definition cfg8_rhoT : Z := Eval vm_compute in ((2 * vT8) mod 3)%Z.

End L89a.

Module L89b.

(** * 1RB1LB_1RC0RD_0LA1RE_0RF1LC_1LA0RB_---1LC: from level 8 to level 9

    The division by 3 of [0100 (10)^(h-2) C] with the counts as variables, level 9 for the
    real counts, and the residues modulo 3^5 and lower bounds of the counts of level 9.
    Generated by a script. *)

Import Individual62.
Import T694_levels End694 Sym694 Lev694 Lvl1_694 Eng694 Cert694 Run694 Res694 Gen694.
Import L23 L34 L45 L56 L6i L67a L67b L78a L78b L89a.
Import Lia Arith PeanoNat Bool NArith ZArith.
Import Coq.Lists.List.
Import ListNotations.

(** ** The division *)

Lemma Zl8_den : forall G x1 x2 x3 x4 x5 x6,
  [false; false; true; false] ++ rep01 (G * 3 + 2) ++ Cw8 x1 x2 x3 x4 (x5 * 3 + 2) x6 =
  den [Lit [false; false; true; false]; Rep (rp [false; true] 3) G; Lit (rp [false; true] 2 ++ k8_0);
    Rep kk8_1 x1; Lit (k8_1); Rep kk8_2 x2; Lit (k8_2); Rep kk8_3 x3; Lit (k8_3); Rep kk8_4 x4; Lit
    (k8_4); Rep (rp kk8_5 3) x5; Lit (rp kk8_5 2 ++ k8_5); Rep kk8_6 x6; Lit (k8_6 ++ ab8)].
Proof.
  intros G x1 x2 x3 x4 x5 x6. unfold Cw8. cbn [den bden].
  change (rep01 (G * 3 + 2)) with (rp [false; true] (G * 3 + 2)).
  rewrite ?rp_add, ?rp_mul, ?app_nil_r, <- ?app_assoc. reflexivity.
Qed.

Definition dv8 := Eval vm_compute in
  dmB 3 [Lit [false; false; true; false]; Rep (rp [false; true] 3) O; Lit (rp [false; true] 2 ++
    k8_0); Rep kk8_1 O; Lit (k8_1); Rep kk8_2 O; Lit (k8_2); Rep kk8_3 O; Lit (k8_3); Rep kk8_4 O;
    Lit (k8_4); Rep (rp kk8_5 3) O; Lit (rp kk8_5 2 ++ k8_5); Rep kk8_6 O; Lit (k8_6 ++ ab8)] tp8.
Definition a9_0 : list bool := Eval vm_compute in
  match dv8 with Some ([Lit a; _; _; _; _; _; _; _; _; _; _; _; _; _; _], _) => a | _ => [] end.
Definition a9_1 : list bool := Eval vm_compute in
  match dv8 with Some ([_; _; Lit a; _; _; _; _; _; _; _; _; _; _; _; _], _) => a | _ => [] end.
Definition a9_2 : list bool := Eval vm_compute in
  match dv8 with Some ([_; _; _; _; Lit a; _; _; _; _; _; _; _; _; _; _], _) => a | _ => [] end.
Definition a9_3 : list bool := Eval vm_compute in
  match dv8 with Some ([_; _; _; _; _; _; Lit a; _; _; _; _; _; _; _; _], _) => a | _ => [] end.
Definition a9_4 : list bool := Eval vm_compute in
  match dv8 with Some ([_; _; _; _; _; _; _; _; Lit a; _; _; _; _; _; _], _) => a | _ => [] end.
Definition a9_5 : list bool := Eval vm_compute in
  match dv8 with Some ([_; _; _; _; _; _; _; _; _; _; Lit a; _; _; _; _], _) => a | _ => [] end.
Definition a9_6 : list bool := Eval vm_compute in
  match dv8 with Some ([_; _; _; _; _; _; _; _; _; _; _; _; Lit a; _; _], _) => a | _ => [] end.
Definition a9_7 : list bool := Eval vm_compute in
  match dv8 with Some ([_; _; _; _; _; _; _; _; _; _; _; _; _; _; Lit a], _) => a | _ => [] end.
Definition P9_1 : list bool := Eval vm_compute in
  match dv8 with Some ([_; Rep p _; _; _; _; _; _; _; _; _; _; _; _; _; _], _) => p | _ => [] end.
Definition P9_2 : list bool := Eval vm_compute in
  match dv8 with Some ([_; _; _; Rep p _; _; _; _; _; _; _; _; _; _; _; _], _) => p | _ => [] end.
Definition P9_3 : list bool := Eval vm_compute in
  match dv8 with Some ([_; _; _; _; _; Rep p _; _; _; _; _; _; _; _; _; _], _) => p | _ => [] end.
Definition P9_4 : list bool := Eval vm_compute in
  match dv8 with Some ([_; _; _; _; _; _; _; Rep p _; _; _; _; _; _; _; _], _) => p | _ => [] end.
Definition P9_5 : list bool := Eval vm_compute in
  match dv8 with Some ([_; _; _; _; _; _; _; _; _; Rep p _; _; _; _; _; _], _) => p | _ => [] end.
Definition P9_6 : list bool := Eval vm_compute in
  match dv8 with Some ([_; _; _; _; _; _; _; _; _; _; _; Rep p _; _; _; _], _) => p | _ => [] end.
Definition P9_7 : list bool := Eval vm_compute in
  match dv8 with Some ([_; _; _; _; _; _; _; _; _; _; _; _; _; Rep p _; _], _) => p | _ => [] end.
Definition r9 : N := Eval vm_compute in match dv8 with Some (_, r) => r | None => 9%N end.
Definition je9 : nat := Eval vm_compute in 3 + N.to_nat r9.

Lemma dv8_ok : forall G x1 x2 x3 x4 x5 x6,
  dmB 3 [Lit [false; false; true; false]; Rep (rp [false; true] 3) G; Lit (rp [false; true] 2 ++
    k8_0); Rep kk8_1 x1; Lit (k8_1); Rep kk8_2 x2; Lit (k8_2); Rep kk8_3 x3; Lit (k8_3); Rep kk8_4
    x4; Lit (k8_4); Rep (rp kk8_5 3) x5; Lit (rp kk8_5 2 ++ k8_5); Rep kk8_6 x6; Lit (k8_6 ++ ab8)]
    tp8 =
  Some ([Lit a9_0; Rep P9_1 G; Lit a9_1; Rep P9_2 x1; Lit a9_2; Rep P9_3 x2; Lit a9_3; Rep P9_4 x3;
    Lit a9_4; Rep P9_5 x4; Lit a9_5; Rep P9_6 x5; Lit a9_6; Rep P9_7 x6; Lit a9_7], r9).
Proof. intros G x1 x2 x3 x4 x5 x6. vm_compute. reflexivity. Qed.

Lemma tp8_lt : (tp8 < 3)%N.
Proof. reflexivity. Qed.

(** ** Level 9 *)

Definition b9 (d1 d2 d3 d4 d5 d6 d7 : nat) : list bool :=
  den [Lit a9_0; Rep P9_1 d1; Lit a9_1; Rep P9_2 d2; Lit a9_2; Rep P9_3 d3; Lit a9_3; Rep P9_4 d4; Lit
    a9_4; Rep P9_5 d5; Lit a9_5; Rep P9_6 d6; Lit a9_6; Rep P9_7 d7; Lit a9_7].

Definition c9_1 : nat := (2 * bval (b8 c8_1 c8_2 c8_3 c8_4 c8_5 c8_6)) / 3.
Definition c9_2 : nat := ((c8_1 - (cc8_1 + 1 + jj8_1)) / kq8_1).
Definition c9_3 : nat := ((c8_2 - (cc8_2 + 1 + jj8_2)) / kq8_2).
Definition c9_4 : nat := ((c8_3 - (cc8_3 + 1 + jj8_3)) / kq8_3).
Definition c9_5 : nat := ((c8_4 - (cc8_4 + 1 + jj8_4)) / kq8_4).
Definition c9_6 : nat := ((c8_5 - (cc8_5 + 1 + jj8_5)) / kq8_5) / 3.
Definition c9_7 : nat := ((c8_6 - (cc8_6 + 1 + jj8_6)) / kq8_6).

Lemma ET8 : 2 * bval (b8 c8_1 c8_2 c8_3 c8_4 c8_5 c8_6) = c9_1 * 3 + 2.
Proof. pose proof T8_res as H. unfold vT8 in H. unfold c9_1. gl (bval (b8 c8_1 c8_2 c8_3 c8_4 c8_5 c8_6)). Qed.

Lemma EC8_1 : c8_1 = cc8_1 + (c9_2 * kq8_1 + jj8_1) + 1.
Proof.
  pose proof c8_1_res as H. pose proof c8_1_res2 as H2. pose proof c8_1_lb as Hb.
  unfold rc8_1 in H. unfold rb8_1 in H2. unfold lb8_1 in Hb.
  unfold c9_2, cc8_1, kq8_1, jj8_1. cbn [Z.of_N] in H, H2, Hb. gl c8_1.
Qed.

Lemma EC8_2 : c8_2 = cc8_2 + (c9_3 * kq8_2 + jj8_2) + 1.
Proof.
  pose proof c8_2_res as H. pose proof c8_2_res2 as H2. pose proof c8_2_lb as Hb.
  unfold rc8_2 in H. unfold rb8_2 in H2. unfold lb8_2 in Hb.
  unfold c9_3, cc8_2, kq8_2, jj8_2. cbn [Z.of_N] in H, H2, Hb. gl c8_2.
Qed.

Lemma EC8_3 : c8_3 = cc8_3 + (c9_4 * kq8_3 + jj8_3) + 1.
Proof.
  pose proof c8_3_res as H. pose proof c8_3_res2 as H2. pose proof c8_3_lb as Hb.
  unfold rc8_3 in H. unfold rb8_3 in H2. unfold lb8_3 in Hb.
  unfold c9_4, cc8_3, kq8_3, jj8_3. cbn [Z.of_N] in H, H2, Hb. gl c8_3.
Qed.

Lemma EC8_4 : c8_4 = cc8_4 + (c9_5 * kq8_4 + jj8_4) + 1.
Proof.
  pose proof c8_4_res as H. pose proof c8_4_res2 as H2. pose proof c8_4_lb as Hb.
  unfold rc8_4 in H. unfold rb8_4 in H2. unfold lb8_4 in Hb.
  unfold c9_5, cc8_4, kq8_4, jj8_4. cbn [Z.of_N] in H, H2, Hb. gl c8_4.
Qed.

Lemma EC8_5 : c8_5 = cc8_5 + ((c9_6 * 3 + 2) * kq8_5 + jj8_5) + 1.
Proof.
  pose proof c8_5_res as H. pose proof c8_5_res2 as H2. pose proof c8_5_lb as Hb.
  unfold rc8_5 in H. unfold rb8_5 in H2. unfold lb8_5 in Hb.
  unfold c9_6, cc8_5, kq8_5, jj8_5. cbn [Z.of_N] in H, H2, Hb. gl c8_5.
Qed.

Lemma EC8_6 : c8_6 = cc8_6 + (c9_7 * kq8_6 + jj8_6) + 1.
Proof.
  pose proof c8_6_res as H. pose proof c8_6_res2 as H2. pose proof c8_6_lb as Hb.
  unfold rc8_6 in H. unfold rb8_6 in H2. unfold lb8_6 in Hb.
  unfold c9_7, cc8_6, kq8_6, jj8_6. cbn [Z.of_N] in H, H2, Hb. gl c8_6.
Qed.

Definition u9 : nat :=
  2 + 2 * bval (b8 (cc8_1 + (c9_2 * kq8_1 + jj8_1) + 1) (cc8_2 + (c9_3 * kq8_2 + jj8_2) + 1) (cc8_3 +
    (c9_4 * kq8_3 + jj8_3) + 1) (cc8_4 + (c9_5 * kq8_4 + jj8_4) + 1) (cc8_5 + ((c9_6 * 3 + 2) *
    kq8_5 + jj8_5) + 1) (cc8_6 + (c9_7 * kq8_6 + jj8_6) + 1)) + lc8 c9_2 c9_3 c9_4 c9_5 (c9_6 * 3 +
    2) c9_7.

Theorem lvl9 : Lvl je9 (b9 c9_1 c9_2 c9_3 c9_4 c9_5 c9_6 c9_7) u9 w9.
Proof.
  pose proof lvl8 as H. pose proof ET8 as HT.
  rewrite EC8_1 in H, HT.
  rewrite EC8_2 in H, HT.
  rewrite EC8_3 in H, HT.
  rewrite EC8_4 in H, HT.
  rewrite EC8_5 in H, HT.
  rewrite EC8_6 in H, HT.
  apply (level_next_top _ (b8 (cc8_1 + (c9_2 * kq8_1 + jj8_1) + 1) (cc8_2 + (c9_3 * kq8_2 + jj8_2) +
    1) (cc8_3 + (c9_4 * kq8_3 + jj8_3) + 1) (cc8_4 + (c9_5 * kq8_4 + jj8_4) + 1) (cc8_5 + ((c9_6 * 3
    + 2) * kq8_5 + jj8_5) + 1) (cc8_6 + (c9_7 * kq8_6 + jj8_6) + 1)) _ w8 (Cw8 c9_2 c9_3 c9_4 c9_5
    (c9_6 * 3 + 2) c9_7) (lc8 c9_2 c9_3 c9_4 c9_5 (c9_6 * 3 + 2) c9_7) tp8 (b9 c9_1 c9_2 c9_3 c9_4
    c9_5 c9_6 c9_7) r9 w9 H (Cw8_len _ _ _ _ _ _) tp8_lt (fun k Hk => end8 _ _ _ _ _ _ _ k Hk)).
  rewrite HT, Zl8_den. apply dmB_sound. apply dv8_ok.
Qed.

(** ** The counts of level 9 modulo 3^5, and lower bounds *)

Definition rc9_1 : N := Eval vm_compute in Z.to_N (((2 * vT8 - 2) / 3) mod 243).
Lemma c9_1_res : (Z.of_nat c9_1 mod Z.of_N 243 = Z.of_N rc9_1)%Z.
Proof.
  pose proof T8_res as H. unfold vT8 in H. unfold c9_1, rc9_1. cbn [Z.of_N].
  gl (bval (b8 c8_1 c8_2 c8_3 c8_4 c8_5 c8_6)).
Qed.
Definition lb9_1 : N := Eval vm_compute in ((2 * lbe8) / 3)%N.
Lemma c9_1_lb : (Z.of_N lb9_1 <= Z.of_nat c9_1)%Z.
Proof.
  pose proof (T8_lb c8_1 c8_2 c8_3 c8_4 c8_5 c8_6) as H. unfold lbe8 in H. unfold c9_1, lb9_1.
  cbn [Z.of_N] in *. gl (bval (b8 c8_1 c8_2 c8_3 c8_4 c8_5 c8_6)).
Qed.
Definition rb9_1 : N := Eval vm_compute in Z.to_N (((2 * Z.of_N t2_8 - 2) * 11) mod 32).
Lemma c9_1_res2 : (Z.of_nat c9_1 mod Z.of_N 32 = Z.of_N rb9_1)%Z.
Proof.
  pose proof T8_res as H. unfold vT8 in H.
  pose proof (T8_low c8_1 c8_2 c8_3 c8_4 c8_5 c8_6) as H2. unfold t2_8 in H2.
  unfold c9_1, rb9_1. cbn [Z.of_N] in *. gl (bval (b8 c8_1 c8_2 c8_3 c8_4 c8_5 c8_6)).
Qed.

Definition rc9_2 : N := Eval vm_compute in
  Z.to_N (((Z.of_N rc8_1 - (Z.of_nat cc8_1 + 1 + Z.of_nat jj8_1)) * 1) mod 243).
Definition lb9_2 : N := Eval vm_compute in ((lb8_1 - (N.of_nat cc8_1 + 1 + N.of_nat jj8_1)) / 1)%N.
Definition rb9_2 : N := Eval vm_compute in
  Z.to_N ((((Z.of_N rb8_1 - (Z.of_nat cc8_1 + 1 + Z.of_nat jj8_1)) mod 32) / 1) mod 32).
Lemma c9_2_res : (Z.of_nat c9_2 mod Z.of_N 243 = Z.of_N rc9_2)%Z.
Proof.
  pose proof c8_1_res as H. pose proof c8_1_res2 as H2. pose proof c8_1_lb as Hb.
  unfold rc8_1 in H. unfold rb8_1 in H2. unfold lb8_1 in Hb.
  unfold c9_2, rc9_2, cc8_1, kq8_1, jj8_1. cbn [Z.of_N] in *. gl c8_1.
Qed.
Lemma c9_2_res2 : (Z.of_nat c9_2 mod Z.of_N 32 = Z.of_N rb9_2)%Z.
Proof.
  pose proof c8_1_res as H. pose proof c8_1_res2 as H2. pose proof c8_1_lb as Hb.
  unfold rc8_1 in H. unfold rb8_1 in H2. unfold lb8_1 in Hb.
  unfold c9_2, rb9_2, cc8_1, kq8_1, jj8_1. cbn [Z.of_N] in *. gl c8_1.
Qed.
Lemma c9_2_lb : (Z.of_N lb9_2 <= Z.of_nat c9_2)%Z.
Proof.
  pose proof c8_1_res as H. pose proof c8_1_res2 as H2. pose proof c8_1_lb as Hb.
  unfold rc8_1 in H. unfold rb8_1 in H2. unfold lb8_1 in Hb.
  unfold c9_2, lb9_2, cc8_1, kq8_1, jj8_1. cbn [Z.of_N] in *. gl c8_1.
Qed.

Definition rc9_3 : N := Eval vm_compute in
  Z.to_N (((Z.of_N rc8_2 - (Z.of_nat cc8_2 + 1 + Z.of_nat jj8_2)) * 365) mod 243).
Definition lb9_3 : N := Eval vm_compute in ((lb8_2 - (N.of_nat cc8_2 + 1 + N.of_nat jj8_2)) / 2)%N.
Definition rb9_3 : N := Eval vm_compute in
  Z.to_N ((((Z.of_N rb8_2 - (Z.of_nat cc8_2 + 1 + Z.of_nat jj8_2)) mod 32) / 2) mod 16).
Lemma c9_3_res : (Z.of_nat c9_3 mod Z.of_N 243 = Z.of_N rc9_3)%Z.
Proof.
  pose proof c8_2_res as H. pose proof c8_2_res2 as H2. pose proof c8_2_lb as Hb.
  unfold rc8_2 in H. unfold rb8_2 in H2. unfold lb8_2 in Hb.
  unfold c9_3, rc9_3, cc8_2, kq8_2, jj8_2. cbn [Z.of_N] in *. gl c8_2.
Qed.
Lemma c9_3_res2 : (Z.of_nat c9_3 mod Z.of_N 16 = Z.of_N rb9_3)%Z.
Proof.
  pose proof c8_2_res as H. pose proof c8_2_res2 as H2. pose proof c8_2_lb as Hb.
  unfold rc8_2 in H. unfold rb8_2 in H2. unfold lb8_2 in Hb.
  unfold c9_3, rb9_3, cc8_2, kq8_2, jj8_2. cbn [Z.of_N] in *. gl c8_2.
Qed.
Lemma c9_3_lb : (Z.of_N lb9_3 <= Z.of_nat c9_3)%Z.
Proof.
  pose proof c8_2_res as H. pose proof c8_2_res2 as H2. pose proof c8_2_lb as Hb.
  unfold rc8_2 in H. unfold rb8_2 in H2. unfold lb8_2 in Hb.
  unfold c9_3, lb9_3, cc8_2, kq8_2, jj8_2. cbn [Z.of_N] in *. gl c8_2.
Qed.

Definition rc9_4 : N := Eval vm_compute in
  Z.to_N (((Z.of_N rc8_3 - (Z.of_nat cc8_3 + 1 + Z.of_nat jj8_3)) * 1) mod 243).
Definition lb9_4 : N := Eval vm_compute in ((lb8_3 - (N.of_nat cc8_3 + 1 + N.of_nat jj8_3)) / 1)%N.
Definition rb9_4 : N := Eval vm_compute in
  Z.to_N ((((Z.of_N rb8_3 - (Z.of_nat cc8_3 + 1 + Z.of_nat jj8_3)) mod 32) / 1) mod 32).
Lemma c9_4_res : (Z.of_nat c9_4 mod Z.of_N 243 = Z.of_N rc9_4)%Z.
Proof.
  pose proof c8_3_res as H. pose proof c8_3_res2 as H2. pose proof c8_3_lb as Hb.
  unfold rc8_3 in H. unfold rb8_3 in H2. unfold lb8_3 in Hb.
  unfold c9_4, rc9_4, cc8_3, kq8_3, jj8_3. cbn [Z.of_N] in *. gl c8_3.
Qed.
Lemma c9_4_res2 : (Z.of_nat c9_4 mod Z.of_N 32 = Z.of_N rb9_4)%Z.
Proof.
  pose proof c8_3_res as H. pose proof c8_3_res2 as H2. pose proof c8_3_lb as Hb.
  unfold rc8_3 in H. unfold rb8_3 in H2. unfold lb8_3 in Hb.
  unfold c9_4, rb9_4, cc8_3, kq8_3, jj8_3. cbn [Z.of_N] in *. gl c8_3.
Qed.
Lemma c9_4_lb : (Z.of_N lb9_4 <= Z.of_nat c9_4)%Z.
Proof.
  pose proof c8_3_res as H. pose proof c8_3_res2 as H2. pose proof c8_3_lb as Hb.
  unfold rc8_3 in H. unfold rb8_3 in H2. unfold lb8_3 in Hb.
  unfold c9_4, lb9_4, cc8_3, kq8_3, jj8_3. cbn [Z.of_N] in *. gl c8_3.
Qed.

Definition rc9_5 : N := Eval vm_compute in
  Z.to_N (((Z.of_N rc8_4 - (Z.of_nat cc8_4 + 1 + Z.of_nat jj8_4)) * 1) mod 243).
Definition lb9_5 : N := Eval vm_compute in ((lb8_4 - (N.of_nat cc8_4 + 1 + N.of_nat jj8_4)) / 1)%N.
Definition rb9_5 : N := Eval vm_compute in
  Z.to_N ((((Z.of_N rb8_4 - (Z.of_nat cc8_4 + 1 + Z.of_nat jj8_4)) mod 32) / 1) mod 32).
Lemma c9_5_res : (Z.of_nat c9_5 mod Z.of_N 243 = Z.of_N rc9_5)%Z.
Proof.
  pose proof c8_4_res as H. pose proof c8_4_res2 as H2. pose proof c8_4_lb as Hb.
  unfold rc8_4 in H. unfold rb8_4 in H2. unfold lb8_4 in Hb.
  unfold c9_5, rc9_5, cc8_4, kq8_4, jj8_4. cbn [Z.of_N] in *. gl c8_4.
Qed.
Lemma c9_5_res2 : (Z.of_nat c9_5 mod Z.of_N 32 = Z.of_N rb9_5)%Z.
Proof.
  pose proof c8_4_res as H. pose proof c8_4_res2 as H2. pose proof c8_4_lb as Hb.
  unfold rc8_4 in H. unfold rb8_4 in H2. unfold lb8_4 in Hb.
  unfold c9_5, rb9_5, cc8_4, kq8_4, jj8_4. cbn [Z.of_N] in *. gl c8_4.
Qed.
Lemma c9_5_lb : (Z.of_N lb9_5 <= Z.of_nat c9_5)%Z.
Proof.
  pose proof c8_4_res as H. pose proof c8_4_res2 as H2. pose proof c8_4_lb as Hb.
  unfold rc8_4 in H. unfold rb8_4 in H2. unfold lb8_4 in Hb.
  unfold c9_5, lb9_5, cc8_4, kq8_4, jj8_4. cbn [Z.of_N] in *. gl c8_4.
Qed.

Definition rc9_6 : N := Eval vm_compute in
  Z.to_N (((((Z.of_N rc8_5 - (Z.of_nat cc8_5 + 1 + Z.of_nat jj8_5)) * 1) mod 729) / 3) mod 243).
Definition lb9_6 : N := Eval vm_compute in (((lb8_5 - (N.of_nat cc8_5 + 1 + N.of_nat jj8_5)) / 1) / 3)%N.
Definition rb9_6 : N := Eval vm_compute in
  Z.to_N (((((Z.of_N rb8_5 - (Z.of_nat cc8_5 + 1 + Z.of_nat jj8_5)) mod 32) / 1 - 2) * 11) mod 32).
Lemma c9_6_res : (Z.of_nat c9_6 mod Z.of_N 243 = Z.of_N rc9_6)%Z.
Proof.
  pose proof c8_5_res as H. pose proof c8_5_res2 as H2. pose proof c8_5_lb as Hb.
  unfold rc8_5 in H. unfold rb8_5 in H2. unfold lb8_5 in Hb.
  unfold c9_6, rc9_6, cc8_5, kq8_5, jj8_5. cbn [Z.of_N] in *. gl c8_5.
Qed.
Lemma c9_6_res2 : (Z.of_nat c9_6 mod Z.of_N 32 = Z.of_N rb9_6)%Z.
Proof.
  pose proof c8_5_res as H. pose proof c8_5_res2 as H2. pose proof c8_5_lb as Hb.
  unfold rc8_5 in H. unfold rb8_5 in H2. unfold lb8_5 in Hb.
  unfold c9_6, rb9_6, cc8_5, kq8_5, jj8_5. cbn [Z.of_N] in *. gl c8_5.
Qed.
Lemma c9_6_lb : (Z.of_N lb9_6 <= Z.of_nat c9_6)%Z.
Proof.
  pose proof c8_5_res as H. pose proof c8_5_res2 as H2. pose proof c8_5_lb as Hb.
  unfold rc8_5 in H. unfold rb8_5 in H2. unfold lb8_5 in Hb.
  unfold c9_6, lb9_6, cc8_5, kq8_5, jj8_5. cbn [Z.of_N] in *. gl c8_5.
Qed.

Definition rc9_7 : N := Eval vm_compute in
  Z.to_N (((Z.of_N rc8_6 - (Z.of_nat cc8_6 + 1 + Z.of_nat jj8_6)) * 1) mod 243).
Definition lb9_7 : N := Eval vm_compute in ((lb8_6 - (N.of_nat cc8_6 + 1 + N.of_nat jj8_6)) / 1)%N.
Definition rb9_7 : N := Eval vm_compute in
  Z.to_N ((((Z.of_N rb8_6 - (Z.of_nat cc8_6 + 1 + Z.of_nat jj8_6)) mod 32) / 1) mod 32).
Lemma c9_7_res : (Z.of_nat c9_7 mod Z.of_N 243 = Z.of_N rc9_7)%Z.
Proof.
  pose proof c8_6_res as H. pose proof c8_6_res2 as H2. pose proof c8_6_lb as Hb.
  unfold rc8_6 in H. unfold rb8_6 in H2. unfold lb8_6 in Hb.
  unfold c9_7, rc9_7, cc8_6, kq8_6, jj8_6. cbn [Z.of_N] in *. gl c8_6.
Qed.
Lemma c9_7_res2 : (Z.of_nat c9_7 mod Z.of_N 32 = Z.of_N rb9_7)%Z.
Proof.
  pose proof c8_6_res as H. pose proof c8_6_res2 as H2. pose proof c8_6_lb as Hb.
  unfold rc8_6 in H. unfold rb8_6 in H2. unfold lb8_6 in Hb.
  unfold c9_7, rb9_7, cc8_6, kq8_6, jj8_6. cbn [Z.of_N] in *. gl c8_6.
Qed.
Lemma c9_7_lb : (Z.of_N lb9_7 <= Z.of_nat c9_7)%Z.
Proof.
  pose proof c8_6_res as H. pose proof c8_6_res2 as H2. pose proof c8_6_lb as Hb.
  unfold rc8_6 in H. unfold rb8_6 in H2. unfold lb8_6 in Hb.
  unfold c9_7, lb9_7, cc8_6, kq8_6, jj8_6. cbn [Z.of_N] in *. gl c8_6.
Qed.

(** ** The word of level 9 modulo 3^5 *)

Definition vT9 : Z := Eval vm_compute in
  gv (resW 243 [RL a9_0; RR P9_1 243 rc9_1; RL a9_1; RR P9_2 243 rc9_2; RL a9_2; RR P9_3 243 rc9_3; RL
    a9_3; RR P9_4 243 rc9_4; RL a9_4; RR P9_5 243 rc9_5; RL a9_5; RR P9_6 243 rc9_6; RL a9_6; RR
    P9_7 243 rc9_7; RL a9_7]).

Lemma T9_res : (Z.of_nat (bval (b9 c9_1 c9_2 c9_3 c9_4 c9_5 c9_6 c9_7)) mod 243 = vT9)%Z.
Proof.
  unfold b9.
  apply (resW_sound 243 [Lit a9_0; Rep P9_1 c9_1; Lit a9_1; Rep P9_2 c9_2; Lit a9_2; Rep P9_3 c9_3;
    Lit a9_3; Rep P9_4 c9_4; Lit a9_4; Rep P9_5 c9_5; Lit a9_5; Rep P9_6 c9_6; Lit a9_6; Rep P9_7
    c9_7; Lit a9_7]
           [RL a9_0; RR P9_1 243 rc9_1; RL a9_1; RR P9_2 243 rc9_2; RL a9_2; RR P9_3 243 rc9_3; RL a9_3; RR
            P9_4 243 rc9_4; RL a9_4; RR P9_5 243 rc9_5; RL a9_5; RR P9_6 243 rc9_6; RL a9_6; RR P9_7
            243 rc9_7; RL a9_7]);
    [lia | | vm_compute; reflexivity].
  exact (Forall2_cons _ _ (mL a9_0)
    (Forall2_cons _ _ (mR P9_1 c9_1 243%N rc9_1 c9_1_res)
    (Forall2_cons _ _ (mL a9_1)
    (Forall2_cons _ _ (mR P9_2 c9_2 243%N rc9_2 c9_2_res)
    (Forall2_cons _ _ (mL a9_2)
    (Forall2_cons _ _ (mR P9_3 c9_3 243%N rc9_3 c9_3_res)
    (Forall2_cons _ _ (mL a9_3)
    (Forall2_cons _ _ (mR P9_4 c9_4 243%N rc9_4 c9_4_res)
    (Forall2_cons _ _ (mL a9_4)
    (Forall2_cons _ _ (mR P9_5 c9_5 243%N rc9_5 c9_5_res)
    (Forall2_cons _ _ (mL a9_5)
    (Forall2_cons _ _ (mR P9_6 c9_6 243%N rc9_6 c9_6_res)
    (Forall2_cons _ _ (mL a9_6)
    (Forall2_cons _ _ (mR P9_7 c9_7 243%N rc9_7 c9_7_res)
    (Forall2_cons _ _ (mL a9_7) (Forall2_nil _)))))))))))))))).
Qed.

Definition lbe9 : N := Eval vm_compute in bvalN a9_7.

Lemma T9_lb : forall d1 d2 d3 d4 d5 d6 d7, (Z.of_N lbe9 <= Z.of_nat (bval (b9 d1 d2 d3 d4 d5 d6 d7)))%Z.
Proof.
  intros d1 d2 d3 d4 d5 d6 d7. unfold b9. change lbe9 with (bvalN a9_7).
  exact (lbZ [Lit a9_0; Rep P9_1 d1; Lit a9_1; Rep P9_2 d2; Lit a9_2; Rep P9_3 d3; Lit a9_3; Rep P9_4
    d4; Lit a9_4; Rep P9_5 d5; Lit a9_5; Rep P9_6 d6; Lit a9_6; Rep P9_7 d7] a9_7).
Qed.

Definition t2_9 : N := Eval vm_compute in bvalN a9_0.

Lemma T9_low : forall d1 d2 d3 d4 d5 d6 d7, (Z.of_nat (bval (b9 d1 d2 d3 d4 d5 d6 d7)) mod 16 = Z.of_N t2_9)%Z.
Proof.
  intros d1 d2 d3 d4 d5 d6 d7. unfold b9.
  exact (bval_low_den a9_0 [Rep P9_1 d1; Lit a9_1; Rep P9_2 d2; Lit a9_2; Rep P9_3 d3; Lit a9_3; Rep
    P9_4 d4; Lit a9_4; Rep P9_5 d5; Lit a9_5; Rep P9_6 d6; Lit a9_6; Rep P9_7 d7; Lit a9_7]).
Qed.

End L89b.

Module L910a.

(** * 1RB1LB_1RC0RD_0LA1RE_0RF1LC_1LA0RB_---1LC: the end phase of level 9

    Level 9 has class 4: the end phase is one computation on the low literal of the counter
    word ([c4cert]), and the word that is added is the complement of the rest of the counter
    word between two literals.  Generated by a script. *)

Import Individual62.
Import T694_levels End694 Sym694 Lev694 Lvl1_694 Eng694 Cert694 Run694 Res694 Gen694.
Import L23 L34 L45 L56 L6i L67a L67b L78a L78b L89a L89b.
Import Lia Arith PeanoNat Bool NArith ZArith.
Import Coq.Lists.List.
Import ListNotations.

Definition c4_9 := Eval vm_compute in c4cert 6000 6000 je9 a9_0 w9.
Definition s4_9 : nat := Eval vm_compute in match c4_9 with Some (x, _, _, _, _) => x | None => O end.
Definition la9 : nat := Eval vm_compute in match c4_9 with Some (_, x, _, _, _) => x | None => O end.
Definition k9_0 : list bool := Eval vm_compute in match c4_9 with Some (_, _, x, _, _) => x | None => [] end.
Definition ab4_9 : list bool := Eval vm_compute in match c4_9 with Some (_, _, _, x, _) => x | None => [] end.
Definition w10 : list bool := Eval vm_compute in match c4_9 with Some (_, _, _, _, x) => x | None => [] end.
Definition tp9 : N := 0%N.
Definition ab9 : list bool := [].

Lemma c4_9_ok : c4cert 6000 6000 je9 a9_0 w9 = Some (s4_9, la9, k9_0, ab4_9, w10).
Proof. vm_compute. reflexivity. Qed.

Definition rest9 (n1 n2 n3 n4 n5 n6 n7 : nat) : list blk :=
  [Rep P9_1 n1; Lit a9_1; Rep P9_2 n2; Lit a9_2; Rep P9_3 n3; Lit a9_3; Rep P9_4 n4; Lit a9_4; Rep
    P9_5 n5; Lit a9_5; Rep P9_6 n6; Lit a9_6; Rep P9_7 n7; Lit a9_7].

Lemma rest9_len : forall n1 n2 n3 n4 n5 n6 n7, length (den (rest9 n1 n2 n3 n4 n5 n6 n7)) = 2 * hlen (rest9 n1 n2 n3 n4 n5 n6 n7).
Proof. intros n1 n2 n3 n4 n5 n6 n7. apply den_len. vm_compute. reflexivity. Qed.

Definition kk9_1 : list bool := map negb P9_1.
Definition k9_1 : list bool := map negb a9_1.
Definition kk9_2 : list bool := map negb P9_2.
Definition k9_2 : list bool := map negb a9_2.
Definition kk9_3 : list bool := map negb P9_3.
Definition k9_3 : list bool := map negb a9_3.
Definition kk9_4 : list bool := map negb P9_4.
Definition k9_4 : list bool := map negb a9_4.
Definition kk9_5 : list bool := map negb P9_5.
Definition k9_5 : list bool := map negb a9_5.
Definition kk9_6 : list bool := map negb P9_6.
Definition k9_6 : list bool := map negb a9_6.
Definition kk9_7 : list bool := map negb P9_7.
Definition k9_7 : list bool := map negb a9_7 ++ ab4_9.

Definition Cw9 (n1 n2 n3 n4 n5 n6 n7 : nat) : list bool :=
  den [Lit k9_0; Rep kk9_1 n1; Lit k9_1; Rep kk9_2 n2; Lit k9_2; Rep kk9_3 n3; Lit k9_3; Rep kk9_4 n4;
    Lit k9_4; Rep kk9_5 n5; Lit k9_5; Rep kk9_6 n6; Lit k9_6; Rep kk9_7 n7; Lit k9_7] ++ ab9.
Definition lc9 (n1 n2 n3 n4 n5 n6 n7 : nat) : nat := s4_9 + hlen (rest9 n1 n2 n3 n4 n5 n6 n7) + la9.

Lemma Cw9_eq : forall n1 n2 n3 n4 n5 n6 n7,
  Cw9 n1 n2 n3 n4 n5 n6 n7 = k9_0 ++ map negb (den (rest9 n1 n2 n3 n4 n5 n6 n7)) ++ ab4_9.
Proof.
  intros n1 n2 n3 n4 n5 n6 n7. rewrite negb_den. unfold Cw9, rest9, ab9, kk9_1, kk9_2, kk9_3, kk9_4, kk9_5, kk9_6, kk9_7, k9_1, k9_2, k9_3, k9_4, k9_5, k9_6, k9_7.
  cbn [map nblk den bden]. rewrite ?app_nil_r, <- ?app_assoc. reflexivity.
Qed.

Lemma Cw9_len : forall n1 n2 n3 n4 n5 n6 n7, length (Cw9 n1 n2 n3 n4 n5 n6 n7) = 2 * lc9 n1 n2 n3 n4 n5 n6 n7.
Proof.
  intros n1 n2 n3 n4 n5 n6 n7. rewrite Cw9_eq, !length_app, length_map, rest9_len. unfold lc9.
  assert (H1 : length k9_0 = 2 * s4_9) by (vm_compute; reflexivity).
  assert (H2 : length ab4_9 = 2 * la9) by (vm_compute; reflexivity).
  rewrite H1, H2. lia.
Qed.

Lemma end9 : forall n1 n2 n3 n4 n5 n6 n7 h k, (1 <= h)%nat -> (1 <= k)%nat -> exists n M',
  tickN 3 n (rep10 k ++ c1101 ++ repeat true (3 * h) ++ rep10 je9 ++ c1101 ++
             encb false (b9 n1 n2 n3 n4 n5 n6 n7) ++ w9) =
    Some (Slev M' (3 * (h + lc9 n1 n2 n3 n4 n5 n6 n7) + 1) w10) /\
  Z.of_nat M' = (Z.of_nat k +
                 (Z.of_nat (bval (Cw9 n1 n2 n3 n4 n5 n6 n7)) + Z.of_N tp9 * pw4 (lc9 n1 n2 n3 n4 n5 n6 n7)) * pw4 h)%Z.
Proof.
  intros n1 n2 n3 n4 n5 n6 n7 h k Hh Hk.
  destruct (c4cert_sound _ _ _ _ _ _ _ _ _ _ c4_9_ok (den (rest9 n1 n2 n3 n4 n5 n6 n7)) (hlen (rest9 n1 n2 n3 n4 n5 n6 n7)) h
              (rest9_len n1 n2 n3 n4 n5 n6 n7) Hh k Hk) as [n [M' [E D]]].
  exists n, M'. split; [exact E |].
  rewrite D, (Cw9_eq n1 n2 n3 n4 n5 n6 n7). unfold tp9. cbn [Z.of_N]. ring.
Qed.

(** ** What the division needs: which blocks are tripled, and the residues of the counts *)

Definition cfg9_trip : list bool := Eval vm_compute in
  map (fun P => negb (N.eqb (bvalN P mod 3) 0)) [kk9_1; kk9_2; kk9_3; kk9_4; kk9_5; kk9_6; kk9_7].
Definition cfg9_rho : list N := Eval vm_compute in
  [(((rc9_1 + 1594323 - 0%N) * (N.of_nat 1%nat mod 3)) mod 3)%N; (((rc9_2 + 1594323 - 0%N) * (N.of_nat 1%nat mod 3)) mod 3)%N; (((rc9_3 + 1594323 - 0%N) * (N.of_nat 1%nat mod 3)) mod 3)%N; (((rc9_4 + 1594323 - 0%N) * (N.of_nat 1%nat mod 3)) mod 3)%N; (((rc9_5 + 1594323 - 0%N) * (N.of_nat 1%nat mod 3)) mod 3)%N; (((rc9_6 + 1594323 - 0%N) * (N.of_nat 1%nat mod 3)) mod 3)%N; (((rc9_7 + 1594323 - 0%N) * (N.of_nat 1%nat mod 3)) mod 3)%N].
Definition cfg9_k : list nat := Eval vm_compute in [1%nat; 1%nat; 1%nat; 1%nat; 1%nat; 1%nat; 1%nat].
Definition cfg9_j : list nat := Eval vm_compute in [0%nat; 0%nat; 0%nat; 0%nat; 0%nat; 0%nat; 0%nat].
Definition cfg9_rhoT : Z := Eval vm_compute in ((2 * vT9) mod 3)%Z.

End L910a.

Module L910b.

(** * 1RB1LB_1RC0RD_0LA1RE_0RF1LC_1LA0RB_---1LC: from level 9 to level 10

    The division by 3 of [0100 (10)^(h-2) C] with the counts as variables, level 10 for the
    real counts, and the residues modulo 3^4 and lower bounds of the counts of level 10.
    Generated by a script. *)

Import Individual62.
Import T694_levels End694 Sym694 Lev694 Lvl1_694 Eng694 Cert694 Run694 Res694 Gen694.
Import L23 L34 L45 L56 L6i L67a L67b L78a L78b L89a L89b L910a.
Import Lia Arith PeanoNat Bool NArith ZArith.
Import Coq.Lists.List.
Import ListNotations.

(** ** The division *)

Lemma Zl9_den : forall G x1 x2 x3 x4 x5 x6 x7,
  [false; false; true; false] ++ rep01 (G * 3 + 0) ++ Cw9 (x1 * 3 + 2) (x2 * 3 + 0) (x3 * 3 + 2) (x4 * 3 + 0) (x5 * 3 + 0) (x6 * 3 + 2) x7 =
  den [Lit [false; false; true; false]; Rep (rp [false; true] 3) G; Lit (rp [false; true] 0 ++ k9_0);
    Rep (rp kk9_1 3) x1; Lit (rp kk9_1 2 ++ k9_1); Rep (rp kk9_2 3) x2; Lit (rp kk9_2 0 ++ k9_2);
    Rep (rp kk9_3 3) x3; Lit (rp kk9_3 2 ++ k9_3); Rep (rp kk9_4 3) x4; Lit (rp kk9_4 0 ++ k9_4);
    Rep (rp kk9_5 3) x5; Lit (rp kk9_5 0 ++ k9_5); Rep (rp kk9_6 3) x6; Lit (rp kk9_6 2 ++ k9_6);
    Rep kk9_7 x7; Lit (k9_7 ++ ab9)].
Proof.
  intros G x1 x2 x3 x4 x5 x6 x7. unfold Cw9. cbn [den bden].
  change (rep01 (G * 3 + 0)) with (rp [false; true] (G * 3 + 0)).
  rewrite ?rp_add, ?rp_mul, ?app_nil_r, <- ?app_assoc. reflexivity.
Qed.

Definition dv9 := Eval vm_compute in
  dmB 3 [Lit [false; false; true; false]; Rep (rp [false; true] 3) O; Lit (rp [false; true] 0 ++
    k9_0); Rep (rp kk9_1 3) O; Lit (rp kk9_1 2 ++ k9_1); Rep (rp kk9_2 3) O; Lit (rp kk9_2 0 ++
    k9_2); Rep (rp kk9_3 3) O; Lit (rp kk9_3 2 ++ k9_3); Rep (rp kk9_4 3) O; Lit (rp kk9_4 0 ++
    k9_4); Rep (rp kk9_5 3) O; Lit (rp kk9_5 0 ++ k9_5); Rep (rp kk9_6 3) O; Lit (rp kk9_6 2 ++
    k9_6); Rep kk9_7 O; Lit (k9_7 ++ ab9)] tp9.
Definition a10_0 : list bool := Eval vm_compute in
  match dv9 with Some ([Lit a; _; _; _; _; _; _; _; _; _; _; _; _; _; _; _; _], _) => a | _ => [] end.
Definition a10_1 : list bool := Eval vm_compute in
  match dv9 with Some ([_; _; Lit a; _; _; _; _; _; _; _; _; _; _; _; _; _; _], _) => a | _ => [] end.
Definition a10_2 : list bool := Eval vm_compute in
  match dv9 with Some ([_; _; _; _; Lit a; _; _; _; _; _; _; _; _; _; _; _; _], _) => a | _ => [] end.
Definition a10_3 : list bool := Eval vm_compute in
  match dv9 with Some ([_; _; _; _; _; _; Lit a; _; _; _; _; _; _; _; _; _; _], _) => a | _ => [] end.
Definition a10_4 : list bool := Eval vm_compute in
  match dv9 with Some ([_; _; _; _; _; _; _; _; Lit a; _; _; _; _; _; _; _; _], _) => a | _ => [] end.
Definition a10_5 : list bool := Eval vm_compute in
  match dv9 with Some ([_; _; _; _; _; _; _; _; _; _; Lit a; _; _; _; _; _; _], _) => a | _ => [] end.
Definition a10_6 : list bool := Eval vm_compute in
  match dv9 with Some ([_; _; _; _; _; _; _; _; _; _; _; _; Lit a; _; _; _; _], _) => a | _ => [] end.
Definition a10_7 : list bool := Eval vm_compute in
  match dv9 with Some ([_; _; _; _; _; _; _; _; _; _; _; _; _; _; Lit a; _; _], _) => a | _ => [] end.
Definition a10_8 : list bool := Eval vm_compute in
  match dv9 with Some ([_; _; _; _; _; _; _; _; _; _; _; _; _; _; _; _; Lit a], _) => a | _ => [] end.
Definition P10_1 : list bool := Eval vm_compute in
  match dv9 with Some ([_; Rep p _; _; _; _; _; _; _; _; _; _; _; _; _; _; _; _], _) => p | _ => [] end.
Definition P10_2 : list bool := Eval vm_compute in
  match dv9 with Some ([_; _; _; Rep p _; _; _; _; _; _; _; _; _; _; _; _; _; _], _) => p | _ => [] end.
Definition P10_3 : list bool := Eval vm_compute in
  match dv9 with Some ([_; _; _; _; _; Rep p _; _; _; _; _; _; _; _; _; _; _; _], _) => p | _ => [] end.
Definition P10_4 : list bool := Eval vm_compute in
  match dv9 with Some ([_; _; _; _; _; _; _; Rep p _; _; _; _; _; _; _; _; _; _], _) => p | _ => [] end.
Definition P10_5 : list bool := Eval vm_compute in
  match dv9 with Some ([_; _; _; _; _; _; _; _; _; Rep p _; _; _; _; _; _; _; _], _) => p | _ => [] end.
Definition P10_6 : list bool := Eval vm_compute in
  match dv9 with Some ([_; _; _; _; _; _; _; _; _; _; _; Rep p _; _; _; _; _; _], _) => p | _ => [] end.
Definition P10_7 : list bool := Eval vm_compute in
  match dv9 with Some ([_; _; _; _; _; _; _; _; _; _; _; _; _; Rep p _; _; _; _], _) => p | _ => [] end.
Definition P10_8 : list bool := Eval vm_compute in
  match dv9 with Some ([_; _; _; _; _; _; _; _; _; _; _; _; _; _; _; Rep p _; _], _) => p | _ => [] end.
Definition r10 : N := Eval vm_compute in match dv9 with Some (_, r) => r | None => 9%N end.
Definition je10 : nat := Eval vm_compute in 3 + N.to_nat r10.

Lemma dv9_ok : forall G x1 x2 x3 x4 x5 x6 x7,
  dmB 3 [Lit [false; false; true; false]; Rep (rp [false; true] 3) G; Lit (rp [false; true] 0 ++
    k9_0); Rep (rp kk9_1 3) x1; Lit (rp kk9_1 2 ++ k9_1); Rep (rp kk9_2 3) x2; Lit (rp kk9_2 0 ++
    k9_2); Rep (rp kk9_3 3) x3; Lit (rp kk9_3 2 ++ k9_3); Rep (rp kk9_4 3) x4; Lit (rp kk9_4 0 ++
    k9_4); Rep (rp kk9_5 3) x5; Lit (rp kk9_5 0 ++ k9_5); Rep (rp kk9_6 3) x6; Lit (rp kk9_6 2 ++
    k9_6); Rep kk9_7 x7; Lit (k9_7 ++ ab9)] tp9 =
  Some ([Lit a10_0; Rep P10_1 G; Lit a10_1; Rep P10_2 x1; Lit a10_2; Rep P10_3 x2; Lit a10_3; Rep
    P10_4 x3; Lit a10_4; Rep P10_5 x4; Lit a10_5; Rep P10_6 x5; Lit a10_6; Rep P10_7 x6; Lit a10_7;
    Rep P10_8 x7; Lit a10_8], r10).
Proof. intros G x1 x2 x3 x4 x5 x6 x7. vm_compute. reflexivity. Qed.

Lemma tp9_lt : (tp9 < 3)%N.
Proof. reflexivity. Qed.

(** ** Level 10 *)

Definition b10 (d1 d2 d3 d4 d5 d6 d7 d8 : nat) : list bool :=
  den [Lit a10_0; Rep P10_1 d1; Lit a10_1; Rep P10_2 d2; Lit a10_2; Rep P10_3 d3; Lit a10_3; Rep P10_4
    d4; Lit a10_4; Rep P10_5 d5; Lit a10_5; Rep P10_6 d6; Lit a10_6; Rep P10_7 d7; Lit a10_7; Rep
    P10_8 d8; Lit a10_8].

Definition c10_1 : nat := (2 * bval (b9 c9_1 c9_2 c9_3 c9_4 c9_5 c9_6 c9_7)) / 3.
Definition c10_2 : nat := c9_1 / 3.
Definition c10_3 : nat := c9_2 / 3.
Definition c10_4 : nat := c9_3 / 3.
Definition c10_5 : nat := c9_4 / 3.
Definition c10_6 : nat := c9_5 / 3.
Definition c10_7 : nat := c9_6 / 3.
Definition c10_8 : nat := c9_7.

Lemma ET9 : 2 * bval (b9 c9_1 c9_2 c9_3 c9_4 c9_5 c9_6 c9_7) = c10_1 * 3 + 0.
Proof. pose proof T9_res as H. unfold vT9 in H. unfold c10_1. gl (bval (b9 c9_1 c9_2 c9_3 c9_4 c9_5 c9_6 c9_7)). Qed.

Lemma EC9_1 : c9_1 = c10_2 * 3 + 2.
Proof.
  pose proof c9_1_res as H. pose proof c9_1_res2 as H2. pose proof c9_1_lb as Hb.
  unfold rc9_1 in H. unfold rb9_1 in H2. unfold lb9_1 in Hb.
  unfold c10_2. cbn [Z.of_N] in H, H2, Hb. gl c9_1.
Qed.

Lemma EC9_2 : c9_2 = c10_3 * 3 + 0.
Proof.
  pose proof c9_2_res as H. pose proof c9_2_res2 as H2. pose proof c9_2_lb as Hb.
  unfold rc9_2 in H. unfold rb9_2 in H2. unfold lb9_2 in Hb.
  unfold c10_3. cbn [Z.of_N] in H, H2, Hb. gl c9_2.
Qed.

Lemma EC9_3 : c9_3 = c10_4 * 3 + 2.
Proof.
  pose proof c9_3_res as H. pose proof c9_3_res2 as H2. pose proof c9_3_lb as Hb.
  unfold rc9_3 in H. unfold rb9_3 in H2. unfold lb9_3 in Hb.
  unfold c10_4. cbn [Z.of_N] in H, H2, Hb. gl c9_3.
Qed.

Lemma EC9_4 : c9_4 = c10_5 * 3 + 0.
Proof.
  pose proof c9_4_res as H. pose proof c9_4_res2 as H2. pose proof c9_4_lb as Hb.
  unfold rc9_4 in H. unfold rb9_4 in H2. unfold lb9_4 in Hb.
  unfold c10_5. cbn [Z.of_N] in H, H2, Hb. gl c9_4.
Qed.

Lemma EC9_5 : c9_5 = c10_6 * 3 + 0.
Proof.
  pose proof c9_5_res as H. pose proof c9_5_res2 as H2. pose proof c9_5_lb as Hb.
  unfold rc9_5 in H. unfold rb9_5 in H2. unfold lb9_5 in Hb.
  unfold c10_6. cbn [Z.of_N] in H, H2, Hb. gl c9_5.
Qed.

Lemma EC9_6 : c9_6 = c10_7 * 3 + 2.
Proof.
  pose proof c9_6_res as H. pose proof c9_6_res2 as H2. pose proof c9_6_lb as Hb.
  unfold rc9_6 in H. unfold rb9_6 in H2. unfold lb9_6 in Hb.
  unfold c10_7. cbn [Z.of_N] in H, H2, Hb. gl c9_6.
Qed.

Lemma EC9_7 : c9_7 = c10_8.
Proof.
  pose proof c9_7_res as H. pose proof c9_7_res2 as H2. pose proof c9_7_lb as Hb.
  unfold rc9_7 in H. unfold rb9_7 in H2. unfold lb9_7 in Hb.
  unfold c10_8. cbn [Z.of_N] in H, H2, Hb. gl c9_7.
Qed.

Definition u10 : nat :=
  2 + 2 * bval (b9 (c10_2 * 3 + 2) (c10_3 * 3 + 0) (c10_4 * 3 + 2) (c10_5 * 3 + 0) (c10_6 * 3 + 0)
    (c10_7 * 3 + 2) c10_8) + lc9 (c10_2 * 3 + 2) (c10_3 * 3 + 0) (c10_4 * 3 + 2) (c10_5 * 3 + 0)
    (c10_6 * 3 + 0) (c10_7 * 3 + 2) c10_8.

Theorem lvl10 : Lvl je10 (b10 c10_1 c10_2 c10_3 c10_4 c10_5 c10_6 c10_7 c10_8) u10 w10.
Proof.
  pose proof lvl9 as H. pose proof ET9 as HT.
  rewrite EC9_1 in H, HT.
  rewrite EC9_2 in H, HT.
  rewrite EC9_3 in H, HT.
  rewrite EC9_4 in H, HT.
  rewrite EC9_5 in H, HT.
  rewrite EC9_6 in H, HT.
  rewrite EC9_7 in H, HT.
  apply (level_next_top _ (b9 (c10_2 * 3 + 2) (c10_3 * 3 + 0) (c10_4 * 3 + 2) (c10_5 * 3 + 0) (c10_6 *
    3 + 0) (c10_7 * 3 + 2) c10_8) _ w9 (Cw9 (c10_2 * 3 + 2) (c10_3 * 3 + 0) (c10_4 * 3 + 2) (c10_5 *
    3 + 0) (c10_6 * 3 + 0) (c10_7 * 3 + 2) c10_8) (lc9 (c10_2 * 3 + 2) (c10_3 * 3 + 0) (c10_4 * 3 +
    2) (c10_5 * 3 + 0) (c10_6 * 3 + 0) (c10_7 * 3 + 2) c10_8) tp9 (b10 c10_1 c10_2 c10_3 c10_4 c10_5
    c10_6 c10_7 c10_8) r10 w10 H (Cw9_len _ _ _ _ _ _ _) tp9_lt (fun k Hk => end9 _ _ _ _ _ _ _ _ k
    (h_pos _) Hk)).
  rewrite HT, Zl9_den. apply dmB_sound. apply dv9_ok.
Qed.

(** ** The counts of level 10 modulo 3^4, and lower bounds *)

Definition rc10_1 : N := Eval vm_compute in Z.to_N (((2 * vT9 - 0) / 3) mod 81).
Lemma c10_1_res : (Z.of_nat c10_1 mod Z.of_N 81 = Z.of_N rc10_1)%Z.
Proof.
  pose proof T9_res as H. unfold vT9 in H. unfold c10_1, rc10_1. cbn [Z.of_N].
  gl (bval (b9 c9_1 c9_2 c9_3 c9_4 c9_5 c9_6 c9_7)).
Qed.
Definition lb10_1 : N := Eval vm_compute in ((2 * lbe9) / 3)%N.
Lemma c10_1_lb : (Z.of_N lb10_1 <= Z.of_nat c10_1)%Z.
Proof.
  pose proof (T9_lb c9_1 c9_2 c9_3 c9_4 c9_5 c9_6 c9_7) as H. unfold lbe9 in H. unfold c10_1, lb10_1.
  cbn [Z.of_N] in *. gl (bval (b9 c9_1 c9_2 c9_3 c9_4 c9_5 c9_6 c9_7)).
Qed.
Definition rb10_1 : N := Eval vm_compute in Z.to_N (((2 * Z.of_N t2_9 - 0) * 11) mod 32).
Lemma c10_1_res2 : (Z.of_nat c10_1 mod Z.of_N 32 = Z.of_N rb10_1)%Z.
Proof.
  pose proof T9_res as H. unfold vT9 in H.
  pose proof (T9_low c9_1 c9_2 c9_3 c9_4 c9_5 c9_6 c9_7) as H2. unfold t2_9 in H2.
  unfold c10_1, rb10_1. cbn [Z.of_N] in *. gl (bval (b9 c9_1 c9_2 c9_3 c9_4 c9_5 c9_6 c9_7)).
Qed.

Definition rc10_2 : N := Eval vm_compute in
  Z.to_N (((((Z.of_N rc9_1 - 0) * 1) mod 243) / 3) mod 81).
Definition lb10_2 : N := Eval vm_compute in (((lb9_1 - 0) / 1) / 3)%N.
Definition rb10_2 : N := Eval vm_compute in
  Z.to_N (((((Z.of_N rb9_1 - 0) mod 32) / 1 - 2) * 11) mod 32).
Lemma c10_2_res : (Z.of_nat c10_2 mod Z.of_N 81 = Z.of_N rc10_2)%Z.
Proof.
  pose proof c9_1_res as H. pose proof c9_1_res2 as H2. pose proof c9_1_lb as Hb.
  unfold rc9_1 in H. unfold rb9_1 in H2. unfold lb9_1 in Hb.
  unfold c10_2, rc10_2. cbn [Z.of_N] in *. gl c9_1.
Qed.
Lemma c10_2_res2 : (Z.of_nat c10_2 mod Z.of_N 32 = Z.of_N rb10_2)%Z.
Proof.
  pose proof c9_1_res as H. pose proof c9_1_res2 as H2. pose proof c9_1_lb as Hb.
  unfold rc9_1 in H. unfold rb9_1 in H2. unfold lb9_1 in Hb.
  unfold c10_2, rb10_2. cbn [Z.of_N] in *. gl c9_1.
Qed.
Lemma c10_2_lb : (Z.of_N lb10_2 <= Z.of_nat c10_2)%Z.
Proof.
  pose proof c9_1_res as H. pose proof c9_1_res2 as H2. pose proof c9_1_lb as Hb.
  unfold rc9_1 in H. unfold rb9_1 in H2. unfold lb9_1 in Hb.
  unfold c10_2, lb10_2. cbn [Z.of_N] in *. gl c9_1.
Qed.

Definition rc10_3 : N := Eval vm_compute in
  Z.to_N (((((Z.of_N rc9_2 - 0) * 1) mod 243) / 3) mod 81).
Definition lb10_3 : N := Eval vm_compute in (((lb9_2 - 0) / 1) / 3)%N.
Definition rb10_3 : N := Eval vm_compute in
  Z.to_N (((((Z.of_N rb9_2 - 0) mod 32) / 1 - 0) * 11) mod 32).
Lemma c10_3_res : (Z.of_nat c10_3 mod Z.of_N 81 = Z.of_N rc10_3)%Z.
Proof.
  pose proof c9_2_res as H. pose proof c9_2_res2 as H2. pose proof c9_2_lb as Hb.
  unfold rc9_2 in H. unfold rb9_2 in H2. unfold lb9_2 in Hb.
  unfold c10_3, rc10_3. cbn [Z.of_N] in *. gl c9_2.
Qed.
Lemma c10_3_res2 : (Z.of_nat c10_3 mod Z.of_N 32 = Z.of_N rb10_3)%Z.
Proof.
  pose proof c9_2_res as H. pose proof c9_2_res2 as H2. pose proof c9_2_lb as Hb.
  unfold rc9_2 in H. unfold rb9_2 in H2. unfold lb9_2 in Hb.
  unfold c10_3, rb10_3. cbn [Z.of_N] in *. gl c9_2.
Qed.
Lemma c10_3_lb : (Z.of_N lb10_3 <= Z.of_nat c10_3)%Z.
Proof.
  pose proof c9_2_res as H. pose proof c9_2_res2 as H2. pose proof c9_2_lb as Hb.
  unfold rc9_2 in H. unfold rb9_2 in H2. unfold lb9_2 in Hb.
  unfold c10_3, lb10_3. cbn [Z.of_N] in *. gl c9_2.
Qed.

Definition rc10_4 : N := Eval vm_compute in
  Z.to_N (((((Z.of_N rc9_3 - 0) * 1) mod 243) / 3) mod 81).
Definition lb10_4 : N := Eval vm_compute in (((lb9_3 - 0) / 1) / 3)%N.
Definition rb10_4 : N := Eval vm_compute in
  Z.to_N (((((Z.of_N rb9_3 - 0) mod 16) / 1 - 2) * 11) mod 16).
Lemma c10_4_res : (Z.of_nat c10_4 mod Z.of_N 81 = Z.of_N rc10_4)%Z.
Proof.
  pose proof c9_3_res as H. pose proof c9_3_res2 as H2. pose proof c9_3_lb as Hb.
  unfold rc9_3 in H. unfold rb9_3 in H2. unfold lb9_3 in Hb.
  unfold c10_4, rc10_4. cbn [Z.of_N] in *. gl c9_3.
Qed.
Lemma c10_4_res2 : (Z.of_nat c10_4 mod Z.of_N 16 = Z.of_N rb10_4)%Z.
Proof.
  pose proof c9_3_res as H. pose proof c9_3_res2 as H2. pose proof c9_3_lb as Hb.
  unfold rc9_3 in H. unfold rb9_3 in H2. unfold lb9_3 in Hb.
  unfold c10_4, rb10_4. cbn [Z.of_N] in *. gl c9_3.
Qed.
Lemma c10_4_lb : (Z.of_N lb10_4 <= Z.of_nat c10_4)%Z.
Proof.
  pose proof c9_3_res as H. pose proof c9_3_res2 as H2. pose proof c9_3_lb as Hb.
  unfold rc9_3 in H. unfold rb9_3 in H2. unfold lb9_3 in Hb.
  unfold c10_4, lb10_4. cbn [Z.of_N] in *. gl c9_3.
Qed.

Definition rc10_5 : N := Eval vm_compute in
  Z.to_N (((((Z.of_N rc9_4 - 0) * 1) mod 243) / 3) mod 81).
Definition lb10_5 : N := Eval vm_compute in (((lb9_4 - 0) / 1) / 3)%N.
Definition rb10_5 : N := Eval vm_compute in
  Z.to_N (((((Z.of_N rb9_4 - 0) mod 32) / 1 - 0) * 11) mod 32).
Lemma c10_5_res : (Z.of_nat c10_5 mod Z.of_N 81 = Z.of_N rc10_5)%Z.
Proof.
  pose proof c9_4_res as H. pose proof c9_4_res2 as H2. pose proof c9_4_lb as Hb.
  unfold rc9_4 in H. unfold rb9_4 in H2. unfold lb9_4 in Hb.
  unfold c10_5, rc10_5. cbn [Z.of_N] in *. gl c9_4.
Qed.
Lemma c10_5_res2 : (Z.of_nat c10_5 mod Z.of_N 32 = Z.of_N rb10_5)%Z.
Proof.
  pose proof c9_4_res as H. pose proof c9_4_res2 as H2. pose proof c9_4_lb as Hb.
  unfold rc9_4 in H. unfold rb9_4 in H2. unfold lb9_4 in Hb.
  unfold c10_5, rb10_5. cbn [Z.of_N] in *. gl c9_4.
Qed.
Lemma c10_5_lb : (Z.of_N lb10_5 <= Z.of_nat c10_5)%Z.
Proof.
  pose proof c9_4_res as H. pose proof c9_4_res2 as H2. pose proof c9_4_lb as Hb.
  unfold rc9_4 in H. unfold rb9_4 in H2. unfold lb9_4 in Hb.
  unfold c10_5, lb10_5. cbn [Z.of_N] in *. gl c9_4.
Qed.

Definition rc10_6 : N := Eval vm_compute in
  Z.to_N (((((Z.of_N rc9_5 - 0) * 1) mod 243) / 3) mod 81).
Definition lb10_6 : N := Eval vm_compute in (((lb9_5 - 0) / 1) / 3)%N.
Definition rb10_6 : N := Eval vm_compute in
  Z.to_N (((((Z.of_N rb9_5 - 0) mod 32) / 1 - 0) * 11) mod 32).
Lemma c10_6_res : (Z.of_nat c10_6 mod Z.of_N 81 = Z.of_N rc10_6)%Z.
Proof.
  pose proof c9_5_res as H. pose proof c9_5_res2 as H2. pose proof c9_5_lb as Hb.
  unfold rc9_5 in H. unfold rb9_5 in H2. unfold lb9_5 in Hb.
  unfold c10_6, rc10_6. cbn [Z.of_N] in *. gl c9_5.
Qed.
Lemma c10_6_res2 : (Z.of_nat c10_6 mod Z.of_N 32 = Z.of_N rb10_6)%Z.
Proof.
  pose proof c9_5_res as H. pose proof c9_5_res2 as H2. pose proof c9_5_lb as Hb.
  unfold rc9_5 in H. unfold rb9_5 in H2. unfold lb9_5 in Hb.
  unfold c10_6, rb10_6. cbn [Z.of_N] in *. gl c9_5.
Qed.
Lemma c10_6_lb : (Z.of_N lb10_6 <= Z.of_nat c10_6)%Z.
Proof.
  pose proof c9_5_res as H. pose proof c9_5_res2 as H2. pose proof c9_5_lb as Hb.
  unfold rc9_5 in H. unfold rb9_5 in H2. unfold lb9_5 in Hb.
  unfold c10_6, lb10_6. cbn [Z.of_N] in *. gl c9_5.
Qed.

Definition rc10_7 : N := Eval vm_compute in
  Z.to_N (((((Z.of_N rc9_6 - 0) * 1) mod 243) / 3) mod 81).
Definition lb10_7 : N := Eval vm_compute in (((lb9_6 - 0) / 1) / 3)%N.
Definition rb10_7 : N := Eval vm_compute in
  Z.to_N (((((Z.of_N rb9_6 - 0) mod 32) / 1 - 2) * 11) mod 32).
Lemma c10_7_res : (Z.of_nat c10_7 mod Z.of_N 81 = Z.of_N rc10_7)%Z.
Proof.
  pose proof c9_6_res as H. pose proof c9_6_res2 as H2. pose proof c9_6_lb as Hb.
  unfold rc9_6 in H. unfold rb9_6 in H2. unfold lb9_6 in Hb.
  unfold c10_7, rc10_7. cbn [Z.of_N] in *. gl c9_6.
Qed.
Lemma c10_7_res2 : (Z.of_nat c10_7 mod Z.of_N 32 = Z.of_N rb10_7)%Z.
Proof.
  pose proof c9_6_res as H. pose proof c9_6_res2 as H2. pose proof c9_6_lb as Hb.
  unfold rc9_6 in H. unfold rb9_6 in H2. unfold lb9_6 in Hb.
  unfold c10_7, rb10_7. cbn [Z.of_N] in *. gl c9_6.
Qed.
Lemma c10_7_lb : (Z.of_N lb10_7 <= Z.of_nat c10_7)%Z.
Proof.
  pose proof c9_6_res as H. pose proof c9_6_res2 as H2. pose proof c9_6_lb as Hb.
  unfold rc9_6 in H. unfold rb9_6 in H2. unfold lb9_6 in Hb.
  unfold c10_7, lb10_7. cbn [Z.of_N] in *. gl c9_6.
Qed.

Definition rc10_8 : N := Eval vm_compute in
  Z.to_N (((Z.of_N rc9_7 - 0) * 1) mod 81).
Definition lb10_8 : N := Eval vm_compute in ((lb9_7 - 0) / 1)%N.
Definition rb10_8 : N := Eval vm_compute in
  Z.to_N ((((Z.of_N rb9_7 - 0) mod 32) / 1) mod 32).
Lemma c10_8_res : (Z.of_nat c10_8 mod Z.of_N 81 = Z.of_N rc10_8)%Z.
Proof.
  pose proof c9_7_res as H. pose proof c9_7_res2 as H2. pose proof c9_7_lb as Hb.
  unfold rc9_7 in H. unfold rb9_7 in H2. unfold lb9_7 in Hb.
  unfold c10_8, rc10_8. cbn [Z.of_N] in *. gl c9_7.
Qed.
Lemma c10_8_res2 : (Z.of_nat c10_8 mod Z.of_N 32 = Z.of_N rb10_8)%Z.
Proof.
  pose proof c9_7_res as H. pose proof c9_7_res2 as H2. pose proof c9_7_lb as Hb.
  unfold rc9_7 in H. unfold rb9_7 in H2. unfold lb9_7 in Hb.
  unfold c10_8, rb10_8. cbn [Z.of_N] in *. gl c9_7.
Qed.
Lemma c10_8_lb : (Z.of_N lb10_8 <= Z.of_nat c10_8)%Z.
Proof.
  pose proof c9_7_res as H. pose proof c9_7_res2 as H2. pose proof c9_7_lb as Hb.
  unfold rc9_7 in H. unfold rb9_7 in H2. unfold lb9_7 in Hb.
  unfold c10_8, lb10_8. cbn [Z.of_N] in *. gl c9_7.
Qed.

(** ** The word of level 10 modulo 3^4 *)

Definition vT10 : Z := Eval vm_compute in
  gv (resW 81 [RL a10_0; RR P10_1 81 rc10_1; RL a10_1; RR P10_2 81 rc10_2; RL a10_2; RR P10_3 81
    rc10_3; RL a10_3; RR P10_4 81 rc10_4; RL a10_4; RR P10_5 81 rc10_5; RL a10_5; RR P10_6 81
    rc10_6; RL a10_6; RR P10_7 81 rc10_7; RL a10_7; RR P10_8 81 rc10_8; RL a10_8]).

Lemma T10_res : (Z.of_nat (bval (b10 c10_1 c10_2 c10_3 c10_4 c10_5 c10_6 c10_7 c10_8)) mod 81 = vT10)%Z.
Proof.
  unfold b10.
  apply (resW_sound 81 [Lit a10_0; Rep P10_1 c10_1; Lit a10_1; Rep P10_2 c10_2; Lit a10_2; Rep P10_3
    c10_3; Lit a10_3; Rep P10_4 c10_4; Lit a10_4; Rep P10_5 c10_5; Lit a10_5; Rep P10_6 c10_6; Lit
    a10_6; Rep P10_7 c10_7; Lit a10_7; Rep P10_8 c10_8; Lit a10_8]
           [RL a10_0; RR P10_1 81 rc10_1; RL a10_1; RR P10_2 81 rc10_2; RL a10_2; RR P10_3 81 rc10_3; RL a10_3;
            RR P10_4 81 rc10_4; RL a10_4; RR P10_5 81 rc10_5; RL a10_5; RR P10_6 81 rc10_6; RL
            a10_6; RR P10_7 81 rc10_7; RL a10_7; RR P10_8 81 rc10_8; RL a10_8]);
    [lia | | vm_compute; reflexivity].
  exact (Forall2_cons _ _ (mL a10_0)
    (Forall2_cons _ _ (mR P10_1 c10_1 81%N rc10_1 c10_1_res)
    (Forall2_cons _ _ (mL a10_1)
    (Forall2_cons _ _ (mR P10_2 c10_2 81%N rc10_2 c10_2_res)
    (Forall2_cons _ _ (mL a10_2)
    (Forall2_cons _ _ (mR P10_3 c10_3 81%N rc10_3 c10_3_res)
    (Forall2_cons _ _ (mL a10_3)
    (Forall2_cons _ _ (mR P10_4 c10_4 81%N rc10_4 c10_4_res)
    (Forall2_cons _ _ (mL a10_4)
    (Forall2_cons _ _ (mR P10_5 c10_5 81%N rc10_5 c10_5_res)
    (Forall2_cons _ _ (mL a10_5)
    (Forall2_cons _ _ (mR P10_6 c10_6 81%N rc10_6 c10_6_res)
    (Forall2_cons _ _ (mL a10_6)
    (Forall2_cons _ _ (mR P10_7 c10_7 81%N rc10_7 c10_7_res)
    (Forall2_cons _ _ (mL a10_7)
    (Forall2_cons _ _ (mR P10_8 c10_8 81%N rc10_8 c10_8_res)
    (Forall2_cons _ _ (mL a10_8) (Forall2_nil _)))))))))))))))))).
Qed.

Definition lbe10 : N := Eval vm_compute in bvalN a10_8.

Lemma T10_lb : forall d1 d2 d3 d4 d5 d6 d7 d8, (Z.of_N lbe10 <= Z.of_nat (bval (b10 d1 d2 d3 d4 d5 d6 d7 d8)))%Z.
Proof.
  intros d1 d2 d3 d4 d5 d6 d7 d8. unfold b10. change lbe10 with (bvalN a10_8).
  exact (lbZ [Lit a10_0; Rep P10_1 d1; Lit a10_1; Rep P10_2 d2; Lit a10_2; Rep P10_3 d3; Lit a10_3;
    Rep P10_4 d4; Lit a10_4; Rep P10_5 d5; Lit a10_5; Rep P10_6 d6; Lit a10_6; Rep P10_7 d7; Lit
    a10_7; Rep P10_8 d8] a10_8).
Qed.

Definition t2_10 : N := Eval vm_compute in bvalN a10_0.

Lemma T10_low : forall d1 d2 d3 d4 d5 d6 d7 d8, (Z.of_nat (bval (b10 d1 d2 d3 d4 d5 d6 d7 d8)) mod 16 = Z.of_N t2_10)%Z.
Proof.
  intros d1 d2 d3 d4 d5 d6 d7 d8. unfold b10.
  exact (bval_low_den a10_0 [Rep P10_1 d1; Lit a10_1; Rep P10_2 d2; Lit a10_2; Rep P10_3 d3; Lit
    a10_3; Rep P10_4 d4; Lit a10_4; Rep P10_5 d5; Lit a10_5; Rep P10_6 d6; Lit a10_6; Rep P10_7 d7;
    Lit a10_7; Rep P10_8 d8; Lit a10_8]).
Qed.

End L910b.

Module L1011a.

(** * 1RB1LB_1RC0RD_0LA1RE_0RF1LC_1LA0RB_---1LC: the end phase of level 10

    Level 10 has class 5 and a counter word with 8 repeated blocks.  The end phase is
    certified round by round ([crun_run]): a run to the first block, then for each block a
    cycle per copy and a run across the next junction, and a closing computation.  The cuts
    are computed from the rounds of one instance.  Generated by a script. *)

Import Individual62.
Import T694_levels End694 Sym694 Lev694 Lvl1_694 Eng694 Cert694 Run694 Res694 Gen694.
Import L23 L34 L45 L56 L6i L67a L67b L78a L78b L89a L89b L910a L910b.
Import Lia Arith PeanoNat Bool NArith ZArith.
Import Coq.Lists.List.
Import ListNotations.

(** ** The cells of the counter word *)

Definition pa10_0 : bool := Eval vm_compute in par false a10_0.
Lemma pa10_0_eq : par false a10_0 = pa10_0.
Proof. vm_compute. reflexivity. Qed.
Definition pa10_1 : bool := Eval vm_compute in par pa10_0 a10_1.
Lemma pa10_1_eq : par pa10_0 a10_1 = pa10_1.
Proof. vm_compute. reflexivity. Qed.
Definition pa10_2 : bool := Eval vm_compute in par pa10_1 a10_2.
Lemma pa10_2_eq : par pa10_1 a10_2 = pa10_2.
Proof. vm_compute. reflexivity. Qed.
Definition pa10_3 : bool := Eval vm_compute in par pa10_2 a10_3.
Lemma pa10_3_eq : par pa10_2 a10_3 = pa10_3.
Proof. vm_compute. reflexivity. Qed.
Definition pa10_4 : bool := Eval vm_compute in par pa10_3 a10_4.
Lemma pa10_4_eq : par pa10_3 a10_4 = pa10_4.
Proof. vm_compute. reflexivity. Qed.
Definition pa10_5 : bool := Eval vm_compute in par pa10_4 a10_5.
Lemma pa10_5_eq : par pa10_4 a10_5 = pa10_5.
Proof. vm_compute. reflexivity. Qed.
Definition pa10_6 : bool := Eval vm_compute in par pa10_5 a10_6.
Lemma pa10_6_eq : par pa10_5 a10_6 = pa10_6.
Proof. vm_compute. reflexivity. Qed.
Definition pa10_7 : bool := Eval vm_compute in par pa10_6 a10_7.
Lemma pa10_7_eq : par pa10_6 a10_7 = pa10_7.
Proof. vm_compute. reflexivity. Qed.
Lemma pp10_1 : par pa10_0 P10_1 = pa10_0.
Proof. vm_compute. reflexivity. Qed.
Lemma pp10_2 : par pa10_1 P10_2 = pa10_1.
Proof. vm_compute. reflexivity. Qed.
Lemma pp10_3 : par pa10_2 P10_3 = pa10_2.
Proof. vm_compute. reflexivity. Qed.
Lemma pp10_4 : par pa10_3 P10_4 = pa10_3.
Proof. vm_compute. reflexivity. Qed.
Lemma pp10_5 : par pa10_4 P10_5 = pa10_4.
Proof. vm_compute. reflexivity. Qed.
Lemma pp10_6 : par pa10_5 P10_6 = pa10_5.
Proof. vm_compute. reflexivity. Qed.
Lemma pp10_7 : par pa10_6 P10_7 = pa10_6.
Proof. vm_compute. reflexivity. Qed.
Lemma pp10_8 : par pa10_7 P10_8 = pa10_7.
Proof. vm_compute. reflexivity. Qed.

Definition Hd10 : list bool := rep10 je10 ++ c1101 ++ encb false a10_0.
Definition E10_1 : list bool := encb pa10_0 P10_1.
Definition J10_1 : list bool := encb pa10_0 a10_1.
Definition E10_2 : list bool := encb pa10_1 P10_2.
Definition J10_2 : list bool := encb pa10_1 a10_2.
Definition E10_3 : list bool := encb pa10_2 P10_3.
Definition J10_3 : list bool := encb pa10_2 a10_3.
Definition E10_4 : list bool := encb pa10_3 P10_4.
Definition J10_4 : list bool := encb pa10_3 a10_4.
Definition E10_5 : list bool := encb pa10_4 P10_5.
Definition J10_5 : list bool := encb pa10_4 a10_5.
Definition E10_6 : list bool := encb pa10_5 P10_6.
Definition J10_6 : list bool := encb pa10_5 a10_6.
Definition E10_7 : list bool := encb pa10_6 P10_7.
Definition J10_7 : list bool := encb pa10_6 a10_7.
Definition E10_8 : list bool := encb pa10_7 P10_8.
Definition J10_8 : list bool := encb pa10_7 a10_8.

Definition cells10 (c1 c2 c3 c4 c5 c6 c7 c8 : nat) : list bool :=
  rep10 je10 ++ c1101 ++ encb false (b10 c1 c2 c3 c4 c5 c6 c7 c8) ++ w10.

Lemma cells10_eq : forall c1 c2 c3 c4 c5 c6 c7 c8,
  cells10 c1 c2 c3 c4 c5 c6 c7 c8 = Hd10 ++ rp E10_1 c1 ++ J10_1 ++ rp E10_2 c2 ++ J10_2 ++ rp E10_3
    c3 ++ J10_3 ++ rp E10_4 c4 ++ J10_4 ++ rp E10_5 c5 ++ J10_5 ++ rp E10_6 c6 ++ J10_6 ++ rp E10_7
    c7 ++ J10_7 ++ rp E10_8 c8 ++ J10_8 ++ w10.
Proof.
  intros c1 c2 c3 c4 c5 c6 c7 c8. unfold cells10, b10, Hd10, E10_1, J10_1, E10_2, J10_2, E10_3, J10_3, E10_4, J10_4, E10_5, J10_5, E10_6, J10_6, E10_7, J10_7, E10_8, J10_8.
  cbn [den bden]. rewrite app_nil_r.
  rewrite (encb_app a10_0), pa10_0_eq.
  rewrite (encb_rp P10_1 pa10_0 pp10_1), (encb_app a10_1), pa10_1_eq.
  rewrite (encb_rp P10_2 pa10_1 pp10_2), (encb_app a10_2), pa10_2_eq.
  rewrite (encb_rp P10_3 pa10_2 pp10_3), (encb_app a10_3), pa10_3_eq.
  rewrite (encb_rp P10_4 pa10_3 pp10_4), (encb_app a10_4), pa10_4_eq.
  rewrite (encb_rp P10_5 pa10_4 pp10_5), (encb_app a10_5), pa10_5_eq.
  rewrite (encb_rp P10_6 pa10_5 pp10_6), (encb_app a10_6), pa10_6_eq.
  rewrite (encb_rp P10_7 pa10_6 pp10_7), (encb_app a10_7), pa10_7_eq.
  rewrite (encb_rp P10_8 pa10_7 pp10_8).
  rewrite <- ?app_assoc. reflexivity.
Qed.

(** ** Boundaries, computed from the rounds of one instance *)

Definition look10_1 : nat := 36.
Definition dep10_1 : nat := 1.
Definition p10_1 : nat := Eval vm_compute in length E10_1.
Definition N10_1 : nat := Eval vm_compute in
  let b0 := (look10_1 / p10_1 + dep10_1 + 14)%nat in
  (b0 + N.to_nat ((rb10_1 + 4 * 1024 - N.of_nat b0) mod 4)%N)%nat.
Definition look10_2 : nat := 36.
Definition dep10_2 : nat := 1.
Definition p10_2 : nat := Eval vm_compute in length E10_2.
Definition N10_2 : nat := Eval vm_compute in
  let b0 := (look10_2 / p10_2 + dep10_2 + 14)%nat in
  (b0 + N.to_nat ((rb10_2 + 4 * 1024 - N.of_nat b0) mod 4)%N)%nat.
Definition look10_3 : nat := 36.
Definition dep10_3 : nat := 1.
Definition p10_3 : nat := Eval vm_compute in length E10_3.
Definition N10_3 : nat := Eval vm_compute in
  let b0 := (look10_3 / p10_3 + dep10_3 + 14)%nat in
  (b0 + N.to_nat ((rb10_3 + 4 * 1024 - N.of_nat b0) mod 4)%N)%nat.
Definition look10_4 : nat := 36.
Definition dep10_4 : nat := 1.
Definition p10_4 : nat := Eval vm_compute in length E10_4.
Definition N10_4 : nat := Eval vm_compute in
  let b0 := (look10_4 / p10_4 + dep10_4 + 14)%nat in
  (b0 + N.to_nat ((rb10_4 + 4 * 1024 - N.of_nat b0) mod 4)%N)%nat.
Definition look10_5 : nat := 36.
Definition dep10_5 : nat := 1.
Definition p10_5 : nat := Eval vm_compute in length E10_5.
Definition N10_5 : nat := Eval vm_compute in
  let b0 := (look10_5 / p10_5 + dep10_5 + 14)%nat in
  (b0 + N.to_nat ((rb10_5 + 4 * 1024 - N.of_nat b0) mod 4)%N)%nat.
Definition look10_6 : nat := 36.
Definition dep10_6 : nat := 1.
Definition p10_6 : nat := Eval vm_compute in length E10_6.
Definition N10_6 : nat := Eval vm_compute in
  let b0 := (look10_6 / p10_6 + dep10_6 + 14)%nat in
  (b0 + N.to_nat ((rb10_6 + 4 * 1024 - N.of_nat b0) mod 4)%N)%nat.
Definition look10_7 : nat := 36.
Definition dep10_7 : nat := 1.
Definition p10_7 : nat := Eval vm_compute in length E10_7.
Definition N10_7 : nat := Eval vm_compute in
  let b0 := (look10_7 / p10_7 + dep10_7 + 14)%nat in
  (b0 + N.to_nat ((rb10_7 + 4 * 1024 - N.of_nat b0) mod 4)%N)%nat.
Definition look10_8 : nat := 36.
Definition dep10_8 : nat := 1.
Definition p10_8 : nat := Eval vm_compute in length E10_8.
Definition N10_8 : nat := Eval vm_compute in
  let b0 := (look10_8 / p10_8 + dep10_8 + 14)%nat in
  (b0 + N.to_nat ((rb10_8 + 4 * 1024 - N.of_nat b0) mod 4)%N)%nat.
Definition looke10 : nat := 36.
Definition inst10 : list bool := cells10 N10_1 N10_2 N10_3 N10_4 N10_5 N10_6 N10_7 N10_8.
Definition s10_1 : N := Eval vm_compute in N.of_nat (length Hd10).
Definition s10_2 : N := Eval vm_compute in
  (s10_1 + N.of_nat (N10_1 * p10_1 + length J10_1))%N.
Definition s10_3 : N := Eval vm_compute in
  (s10_2 + N.of_nat (N10_2 * p10_2 + length J10_2))%N.
Definition s10_4 : N := Eval vm_compute in
  (s10_3 + N.of_nat (N10_3 * p10_3 + length J10_3))%N.
Definition s10_5 : N := Eval vm_compute in
  (s10_4 + N.of_nat (N10_4 * p10_4 + length J10_4))%N.
Definition s10_6 : N := Eval vm_compute in
  (s10_5 + N.of_nat (N10_5 * p10_5 + length J10_5))%N.
Definition s10_7 : N := Eval vm_compute in
  (s10_6 + N.of_nat (N10_6 * p10_6 + length J10_6))%N.
Definition s10_8 : N := Eval vm_compute in
  (s10_7 + N.of_nat (N10_7 * p10_7 + length J10_7))%N.
Definition s10_9 : N := Eval vm_compute in
  (s10_8 + N.of_nat (N10_8 * p10_8 + length J10_8))%N.
Definition tr10 : list (N * N * N) := Eval vm_compute in
  gtrace 36 (length inst10) 0 0 0 (c1101, true, inst10).
Definition f10_1 : N * N * N * N := Eval vm_compute in
  gfindk (N.of_nat p10_1) (s10_1 + N.of_nat (dep10_1 * p10_1))
         (s10_1 + N.of_nat (N10_1 * p10_1) - N.of_nat look10_1) (1%N :: 2%N :: 4%N :: nil) tr10.
Definition rr10_1 : nat := Eval vm_compute in N.to_nat (fst (fst (fst f10_1))).
Definition R10_1 : nat := Eval vm_compute in N.to_nat (snd (fst f10_1)).
Definition kq10_1 : nat := Eval vm_compute in N.to_nat (snd f10_1).
Definition cc10_1 : nat := Eval vm_compute in N.to_nat ((snd (fst (fst f10_1)) + N.of_nat look10_1 - s10_1) / N.of_nat p10_1).
Definition uu10_1 : nat := Eval vm_compute in N.to_nat ((snd (fst (fst f10_1)) + N.of_nat look10_1 - s10_1) mod N.of_nat p10_1).
Definition jj10_1 : nat := Eval vm_compute in (N10_1 - cc10_1 - 1) mod kq10_1.
Definition S10_1 : sst := Eval vm_compute in
  gcut look10_1 (grst rr10_1 (c1101, true, inst10)).
Definition f10_2 : N * N * N * N := Eval vm_compute in
  gfindk (N.of_nat p10_2) (s10_2 + N.of_nat (dep10_2 * p10_2))
         (s10_2 + N.of_nat (N10_2 * p10_2) - N.of_nat look10_2) (1%N :: 2%N :: 4%N :: nil) tr10.
Definition rr10_2 : nat := Eval vm_compute in N.to_nat (fst (fst (fst f10_2))).
Definition R10_2 : nat := Eval vm_compute in N.to_nat (snd (fst f10_2)).
Definition kq10_2 : nat := Eval vm_compute in N.to_nat (snd f10_2).
Definition cc10_2 : nat := Eval vm_compute in N.to_nat ((snd (fst (fst f10_2)) + N.of_nat look10_2 - s10_2) / N.of_nat p10_2).
Definition uu10_2 : nat := Eval vm_compute in N.to_nat ((snd (fst (fst f10_2)) + N.of_nat look10_2 - s10_2) mod N.of_nat p10_2).
Definition jj10_2 : nat := Eval vm_compute in (N10_2 - cc10_2 - 1) mod kq10_2.
Definition S10_2 : sst := Eval vm_compute in
  gcut look10_2 (grst rr10_2 (c1101, true, inst10)).
Definition f10_3 : N * N * N * N := Eval vm_compute in
  gfindk (N.of_nat p10_3) (s10_3 + N.of_nat (dep10_3 * p10_3))
         (s10_3 + N.of_nat (N10_3 * p10_3) - N.of_nat look10_3) (1%N :: 2%N :: 4%N :: nil) tr10.
Definition rr10_3 : nat := Eval vm_compute in N.to_nat (fst (fst (fst f10_3))).
Definition R10_3 : nat := Eval vm_compute in N.to_nat (snd (fst f10_3)).
Definition kq10_3 : nat := Eval vm_compute in N.to_nat (snd f10_3).
Definition cc10_3 : nat := Eval vm_compute in N.to_nat ((snd (fst (fst f10_3)) + N.of_nat look10_3 - s10_3) / N.of_nat p10_3).
Definition uu10_3 : nat := Eval vm_compute in N.to_nat ((snd (fst (fst f10_3)) + N.of_nat look10_3 - s10_3) mod N.of_nat p10_3).
Definition jj10_3 : nat := Eval vm_compute in (N10_3 - cc10_3 - 1) mod kq10_3.
Definition S10_3 : sst := Eval vm_compute in
  gcut look10_3 (grst rr10_3 (c1101, true, inst10)).
Definition f10_4 : N * N * N * N := Eval vm_compute in
  gfindk (N.of_nat p10_4) (s10_4 + N.of_nat (dep10_4 * p10_4))
         (s10_4 + N.of_nat (N10_4 * p10_4) - N.of_nat look10_4) (1%N :: 2%N :: 4%N :: nil) tr10.
Definition rr10_4 : nat := Eval vm_compute in N.to_nat (fst (fst (fst f10_4))).
Definition R10_4 : nat := Eval vm_compute in N.to_nat (snd (fst f10_4)).
Definition kq10_4 : nat := Eval vm_compute in N.to_nat (snd f10_4).
Definition cc10_4 : nat := Eval vm_compute in N.to_nat ((snd (fst (fst f10_4)) + N.of_nat look10_4 - s10_4) / N.of_nat p10_4).
Definition uu10_4 : nat := Eval vm_compute in N.to_nat ((snd (fst (fst f10_4)) + N.of_nat look10_4 - s10_4) mod N.of_nat p10_4).
Definition jj10_4 : nat := Eval vm_compute in (N10_4 - cc10_4 - 1) mod kq10_4.
Definition S10_4 : sst := Eval vm_compute in
  gcut look10_4 (grst rr10_4 (c1101, true, inst10)).
Definition f10_5 : N * N * N * N := Eval vm_compute in
  gfindk (N.of_nat p10_5) (s10_5 + N.of_nat (dep10_5 * p10_5))
         (s10_5 + N.of_nat (N10_5 * p10_5) - N.of_nat look10_5) (1%N :: 2%N :: 4%N :: nil) tr10.
Definition rr10_5 : nat := Eval vm_compute in N.to_nat (fst (fst (fst f10_5))).
Definition R10_5 : nat := Eval vm_compute in N.to_nat (snd (fst f10_5)).
Definition kq10_5 : nat := Eval vm_compute in N.to_nat (snd f10_5).
Definition cc10_5 : nat := Eval vm_compute in N.to_nat ((snd (fst (fst f10_5)) + N.of_nat look10_5 - s10_5) / N.of_nat p10_5).
Definition uu10_5 : nat := Eval vm_compute in N.to_nat ((snd (fst (fst f10_5)) + N.of_nat look10_5 - s10_5) mod N.of_nat p10_5).
Definition jj10_5 : nat := Eval vm_compute in (N10_5 - cc10_5 - 1) mod kq10_5.
Definition S10_5 : sst := Eval vm_compute in
  gcut look10_5 (grst rr10_5 (c1101, true, inst10)).
Definition f10_6 : N * N * N * N := Eval vm_compute in
  gfindk (N.of_nat p10_6) (s10_6 + N.of_nat (dep10_6 * p10_6))
         (s10_6 + N.of_nat (N10_6 * p10_6) - N.of_nat look10_6) (1%N :: 2%N :: 4%N :: nil) tr10.
Definition rr10_6 : nat := Eval vm_compute in N.to_nat (fst (fst (fst f10_6))).
Definition R10_6 : nat := Eval vm_compute in N.to_nat (snd (fst f10_6)).
Definition kq10_6 : nat := Eval vm_compute in N.to_nat (snd f10_6).
Definition cc10_6 : nat := Eval vm_compute in N.to_nat ((snd (fst (fst f10_6)) + N.of_nat look10_6 - s10_6) / N.of_nat p10_6).
Definition uu10_6 : nat := Eval vm_compute in N.to_nat ((snd (fst (fst f10_6)) + N.of_nat look10_6 - s10_6) mod N.of_nat p10_6).
Definition jj10_6 : nat := Eval vm_compute in (N10_6 - cc10_6 - 1) mod kq10_6.
Definition S10_6 : sst := Eval vm_compute in
  gcut look10_6 (grst rr10_6 (c1101, true, inst10)).
Definition f10_7 : N * N * N * N := Eval vm_compute in
  gfindk (N.of_nat p10_7) (s10_7 + N.of_nat (dep10_7 * p10_7))
         (s10_7 + N.of_nat (N10_7 * p10_7) - N.of_nat look10_7) (1%N :: 2%N :: 4%N :: nil) tr10.
Definition rr10_7 : nat := Eval vm_compute in N.to_nat (fst (fst (fst f10_7))).
Definition R10_7 : nat := Eval vm_compute in N.to_nat (snd (fst f10_7)).
Definition kq10_7 : nat := Eval vm_compute in N.to_nat (snd f10_7).
Definition cc10_7 : nat := Eval vm_compute in N.to_nat ((snd (fst (fst f10_7)) + N.of_nat look10_7 - s10_7) / N.of_nat p10_7).
Definition uu10_7 : nat := Eval vm_compute in N.to_nat ((snd (fst (fst f10_7)) + N.of_nat look10_7 - s10_7) mod N.of_nat p10_7).
Definition jj10_7 : nat := Eval vm_compute in (N10_7 - cc10_7 - 1) mod kq10_7.
Definition S10_7 : sst := Eval vm_compute in
  gcut look10_7 (grst rr10_7 (c1101, true, inst10)).
Definition f10_8 : N * N * N * N := Eval vm_compute in
  gfindk (N.of_nat p10_8) (s10_8 + N.of_nat (dep10_8 * p10_8))
         (s10_8 + N.of_nat (N10_8 * p10_8) - N.of_nat look10_8) (1%N :: 2%N :: 4%N :: nil) tr10.
Definition rr10_8 : nat := Eval vm_compute in N.to_nat (fst (fst (fst f10_8))).
Definition R10_8 : nat := Eval vm_compute in N.to_nat (snd (fst f10_8)).
Definition kq10_8 : nat := Eval vm_compute in N.to_nat (snd f10_8).
Definition cc10_8 : nat := Eval vm_compute in N.to_nat ((snd (fst (fst f10_8)) + N.of_nat look10_8 - s10_8) / N.of_nat p10_8).
Definition uu10_8 : nat := Eval vm_compute in N.to_nat ((snd (fst (fst f10_8)) + N.of_nat look10_8 - s10_8) mod N.of_nat p10_8).
Definition jj10_8 : nat := Eval vm_compute in (N10_8 - cc10_8 - 1) mod kq10_8.
Definition S10_8 : sst := Eval vm_compute in
  gcut look10_8 (grst rr10_8 (c1101, true, inst10)).
Definition fe10 : N * N := Eval vm_compute in
  glast (s10_9 - N.of_nat (looke10 + 60)) tr10 (0, 0)%N.
Definition rre10 : nat := Eval vm_compute in N.to_nat (fst fe10).
Definition ue10 : nat := Eval vm_compute in
  N.to_nat (snd fe10 + N.of_nat looke10 - (s10_8 + N.of_nat (N10_8 * p10_8))).
Definition Se10 : sst := Eval vm_compute in gcut looke10 (grst rre10 (c1101, true, inst10)).
Definition Rj10_0 : nat := rr10_1.
Definition Rj10_1 : nat := Eval vm_compute in
  rr10_2 - rr10_1 - R10_1 * ((N10_1 - cc10_1 - 1 - jj10_1) / kq10_1).
Definition Rj10_2 : nat := Eval vm_compute in
  rr10_3 - rr10_2 - R10_2 * ((N10_2 - cc10_2 - 1 - jj10_2) / kq10_2).
Definition Rj10_3 : nat := Eval vm_compute in
  rr10_4 - rr10_3 - R10_3 * ((N10_3 - cc10_3 - 1 - jj10_3) / kq10_3).
Definition Rj10_4 : nat := Eval vm_compute in
  rr10_5 - rr10_4 - R10_4 * ((N10_4 - cc10_4 - 1 - jj10_4) / kq10_4).
Definition Rj10_5 : nat := Eval vm_compute in
  rr10_6 - rr10_5 - R10_5 * ((N10_5 - cc10_5 - 1 - jj10_5) / kq10_5).
Definition Rj10_6 : nat := Eval vm_compute in
  rr10_7 - rr10_6 - R10_6 * ((N10_6 - cc10_6 - 1 - jj10_6) / kq10_6).
Definition Rj10_7 : nat := Eval vm_compute in
  rr10_8 - rr10_7 - R10_7 * ((N10_7 - cc10_7 - 1 - jj10_7) / kq10_7).
Definition Rj10_8 : nat := Eval vm_compute in
  rre10 - rr10_8 - R10_8 * ((N10_8 - cc10_8 - 1 - jj10_8) / kq10_8).

(** ** The cuts *)

Definition u10_1 : list bool := firstn uu10_1 E10_1.
Definition v10_1 : list bool := skipn uu10_1 E10_1.
Definition u10_2 : list bool := firstn uu10_2 E10_2.
Definition v10_2 : list bool := skipn uu10_2 E10_2.
Definition u10_3 : list bool := firstn uu10_3 E10_3.
Definition v10_3 : list bool := skipn uu10_3 E10_3.
Definition u10_4 : list bool := firstn uu10_4 E10_4.
Definition v10_4 : list bool := skipn uu10_4 E10_4.
Definition u10_5 : list bool := firstn uu10_5 E10_5.
Definition v10_5 : list bool := skipn uu10_5 E10_5.
Definition u10_6 : list bool := firstn uu10_6 E10_6.
Definition v10_6 : list bool := skipn uu10_6 E10_6.
Definition u10_7 : list bool := firstn uu10_7 E10_7.
Definition v10_7 : list bool := skipn uu10_7 E10_7.
Definition u10_8 : list bool := firstn uu10_8 E10_8.
Definition v10_8 : list bool := skipn uu10_8 E10_8.
Definition F10_0 : list bool := Hd10 ++ rp E10_1 cc10_1 ++ u10_1.
Definition C10_1 : list bool := v10_1 ++ u10_1.
Definition K10_1 : list bool := rp C10_1 kq10_1.
Lemma tl10_1 : rp E10_1 (jj10_1 + 1) = u10_1 ++ rp C10_1 jj10_1 ++ v10_1.
Proof. vm_compute. reflexivity. Qed.
Definition F10_1 : list bool :=
  (rp C10_1 jj10_1 ++ v10_1) ++ J10_1 ++ rp E10_2 cc10_2 ++ u10_2.
Definition C10_2 : list bool := v10_2 ++ u10_2.
Definition K10_2 : list bool := rp C10_2 kq10_2.
Lemma tl10_2 : rp E10_2 (jj10_2 + 1) = u10_2 ++ rp C10_2 jj10_2 ++ v10_2.
Proof. vm_compute. reflexivity. Qed.
Definition F10_2 : list bool :=
  (rp C10_2 jj10_2 ++ v10_2) ++ J10_2 ++ rp E10_3 cc10_3 ++ u10_3.
Definition C10_3 : list bool := v10_3 ++ u10_3.
Definition K10_3 : list bool := rp C10_3 kq10_3.
Lemma tl10_3 : rp E10_3 (jj10_3 + 1) = u10_3 ++ rp C10_3 jj10_3 ++ v10_3.
Proof. vm_compute. reflexivity. Qed.
Definition F10_3 : list bool :=
  (rp C10_3 jj10_3 ++ v10_3) ++ J10_3 ++ rp E10_4 cc10_4 ++ u10_4.
Definition C10_4 : list bool := v10_4 ++ u10_4.
Definition K10_4 : list bool := rp C10_4 kq10_4.
Lemma tl10_4 : rp E10_4 (jj10_4 + 1) = u10_4 ++ rp C10_4 jj10_4 ++ v10_4.
Proof. vm_compute. reflexivity. Qed.
Definition F10_4 : list bool :=
  (rp C10_4 jj10_4 ++ v10_4) ++ J10_4 ++ rp E10_5 cc10_5 ++ u10_5.
Definition C10_5 : list bool := v10_5 ++ u10_5.
Definition K10_5 : list bool := rp C10_5 kq10_5.
Lemma tl10_5 : rp E10_5 (jj10_5 + 1) = u10_5 ++ rp C10_5 jj10_5 ++ v10_5.
Proof. vm_compute. reflexivity. Qed.
Definition F10_5 : list bool :=
  (rp C10_5 jj10_5 ++ v10_5) ++ J10_5 ++ rp E10_6 cc10_6 ++ u10_6.
Definition C10_6 : list bool := v10_6 ++ u10_6.
Definition K10_6 : list bool := rp C10_6 kq10_6.
Lemma tl10_6 : rp E10_6 (jj10_6 + 1) = u10_6 ++ rp C10_6 jj10_6 ++ v10_6.
Proof. vm_compute. reflexivity. Qed.
Definition F10_6 : list bool :=
  (rp C10_6 jj10_6 ++ v10_6) ++ J10_6 ++ rp E10_7 cc10_7 ++ u10_7.
Definition C10_7 : list bool := v10_7 ++ u10_7.
Definition K10_7 : list bool := rp C10_7 kq10_7.
Lemma tl10_7 : rp E10_7 (jj10_7 + 1) = u10_7 ++ rp C10_7 jj10_7 ++ v10_7.
Proof. vm_compute. reflexivity. Qed.
Definition F10_7 : list bool :=
  (rp C10_7 jj10_7 ++ v10_7) ++ J10_7 ++ rp E10_8 cc10_8 ++ u10_8.
Definition C10_8 : list bool := v10_8 ++ u10_8.
Definition K10_8 : list bool := rp C10_8 kq10_8.
Lemma tl10_8 : rp E10_8 (jj10_8 + 1) = u10_8 ++ rp C10_8 jj10_8 ++ v10_8.
Proof. vm_compute. reflexivity. Qed.
Definition F10_8 : list bool := (rp C10_8 jj10_8 ++ v10_8) ++ firstn ue10 J10_8.
Definition Fw10 : list bool := skipn ue10 J10_8 ++ w10.

Lemma cells10_cut : forall n1 n2 n3 n4 n5 n6 n7 n8,
  cells10 (cc10_1 + (n1 * kq10_1 + jj10_1) + 1) (cc10_2 + (n2 * kq10_2 + jj10_2) + 1) (cc10_3 + (n3 *
    kq10_3 + jj10_3) + 1) (cc10_4 + (n4 * kq10_4 + jj10_4) + 1) (cc10_5 + (n5 * kq10_5 + jj10_5) +
    1) (cc10_6 + (n6 * kq10_6 + jj10_6) + 1) (cc10_7 + (n7 * kq10_7 + jj10_7) + 1) (cc10_8 + (n8 *
    kq10_8 + jj10_8) + 1) = (F10_0 ++ rp K10_1 n1 ++ F10_1 ++ rp K10_2 n2 ++ F10_2 ++ rp K10_3 n3 ++
    F10_3 ++ rp K10_4 n4 ++ F10_4 ++ rp K10_5 n5 ++ F10_5 ++ rp K10_6 n6 ++ F10_6 ++ rp K10_7 n7 ++
    F10_7 ++ rp K10_8 n8 ++ F10_8 ++ []) ++ Fw10.
Proof.
  intros n1 n2 n3 n4 n5 n6 n7 n8. rewrite cells10_eq.
  replace (cc10_1 + (n1 * kq10_1 + jj10_1) + 1) with (cc10_1 + n1 * kq10_1 + (jj10_1 + 1)) by lia.
  rewrite (rp_recut E10_1 u10_1 v10_1 (n1 * kq10_1) cc10_1 (jj10_1 + 1) (rp C10_1 jj10_1 ++ v10_1)
             (eq_sym (firstn_skipn uu10_1 E10_1)) tl10_1).
  rewrite (rp_mul (v10_1 ++ u10_1) kq10_1 n1).
  replace (cc10_2 + (n2 * kq10_2 + jj10_2) + 1) with (cc10_2 + n2 * kq10_2 + (jj10_2 + 1)) by lia.
  rewrite (rp_recut E10_2 u10_2 v10_2 (n2 * kq10_2) cc10_2 (jj10_2 + 1) (rp C10_2 jj10_2 ++ v10_2)
             (eq_sym (firstn_skipn uu10_2 E10_2)) tl10_2).
  rewrite (rp_mul (v10_2 ++ u10_2) kq10_2 n2).
  replace (cc10_3 + (n3 * kq10_3 + jj10_3) + 1) with (cc10_3 + n3 * kq10_3 + (jj10_3 + 1)) by lia.
  rewrite (rp_recut E10_3 u10_3 v10_3 (n3 * kq10_3) cc10_3 (jj10_3 + 1) (rp C10_3 jj10_3 ++ v10_3)
             (eq_sym (firstn_skipn uu10_3 E10_3)) tl10_3).
  rewrite (rp_mul (v10_3 ++ u10_3) kq10_3 n3).
  replace (cc10_4 + (n4 * kq10_4 + jj10_4) + 1) with (cc10_4 + n4 * kq10_4 + (jj10_4 + 1)) by lia.
  rewrite (rp_recut E10_4 u10_4 v10_4 (n4 * kq10_4) cc10_4 (jj10_4 + 1) (rp C10_4 jj10_4 ++ v10_4)
             (eq_sym (firstn_skipn uu10_4 E10_4)) tl10_4).
  rewrite (rp_mul (v10_4 ++ u10_4) kq10_4 n4).
  replace (cc10_5 + (n5 * kq10_5 + jj10_5) + 1) with (cc10_5 + n5 * kq10_5 + (jj10_5 + 1)) by lia.
  rewrite (rp_recut E10_5 u10_5 v10_5 (n5 * kq10_5) cc10_5 (jj10_5 + 1) (rp C10_5 jj10_5 ++ v10_5)
             (eq_sym (firstn_skipn uu10_5 E10_5)) tl10_5).
  rewrite (rp_mul (v10_5 ++ u10_5) kq10_5 n5).
  replace (cc10_6 + (n6 * kq10_6 + jj10_6) + 1) with (cc10_6 + n6 * kq10_6 + (jj10_6 + 1)) by lia.
  rewrite (rp_recut E10_6 u10_6 v10_6 (n6 * kq10_6) cc10_6 (jj10_6 + 1) (rp C10_6 jj10_6 ++ v10_6)
             (eq_sym (firstn_skipn uu10_6 E10_6)) tl10_6).
  rewrite (rp_mul (v10_6 ++ u10_6) kq10_6 n6).
  replace (cc10_7 + (n7 * kq10_7 + jj10_7) + 1) with (cc10_7 + n7 * kq10_7 + (jj10_7 + 1)) by lia.
  rewrite (rp_recut E10_7 u10_7 v10_7 (n7 * kq10_7) cc10_7 (jj10_7 + 1) (rp C10_7 jj10_7 ++ v10_7)
             (eq_sym (firstn_skipn uu10_7 E10_7)) tl10_7).
  rewrite (rp_mul (v10_7 ++ u10_7) kq10_7 n7).
  replace (cc10_8 + (n8 * kq10_8 + jj10_8) + 1) with (cc10_8 + n8 * kq10_8 + (jj10_8 + 1)) by lia.
  rewrite (rp_recut E10_8 u10_8 v10_8 (n8 * kq10_8) cc10_8 (jj10_8 + 1) (rp C10_8 jj10_8 ++ v10_8)
             (eq_sym (firstn_skipn uu10_8 E10_8)) tl10_8).
  rewrite (rp_mul (v10_8 ++ u10_8) kq10_8 n8).
  rewrite <- (firstn_skipn ue10 J10_8) at 1.
  unfold F10_0, K10_1, F10_1, C10_1, K10_2, F10_2, C10_2, K10_3, F10_3, C10_3, K10_4, F10_4, C10_4, K10_5, F10_5, C10_5, K10_6, F10_6, C10_6, K10_7, F10_7, C10_7, K10_8, F10_8, C10_8, Fw10.
  rewrite ?app_nil_r, <- ?app_assoc. reflexivity.
Qed.

(** ** Runs and cycles, round by round *)

Definition st100 : sst := (c1101, true, []).
Definition lF10_0 : list (Z * nat) := Eval vm_compute in grl Rj10_0 st100 F10_0.
Lemma RF10_0 : Run st100 F10_0 S10_1 (pSh lF10_0) (pV lF10_0).
Proof. apply (crun_run Rj10_0 4). vm_compute. reflexivity. Qed.
Definition lC10_1 : list (Z * nat) := Eval vm_compute in grl R10_1 S10_1 K10_1.
Lemma RC10_1 : Run S10_1 K10_1 S10_1 (pSh lC10_1) (pV lC10_1).
Proof. apply (crun_run R10_1 4). vm_compute. reflexivity. Qed.
Definition lF10_1 : list (Z * nat) := Eval vm_compute in grl Rj10_1 S10_1 F10_1.
Lemma RF10_1 : Run S10_1 F10_1 S10_2 (pSh lF10_1) (pV lF10_1).
Proof. apply (crun_run Rj10_1 4). vm_compute. reflexivity. Qed.
Definition lC10_2 : list (Z * nat) := Eval vm_compute in grl R10_2 S10_2 K10_2.
Lemma RC10_2 : Run S10_2 K10_2 S10_2 (pSh lC10_2) (pV lC10_2).
Proof. apply (crun_run R10_2 4). vm_compute. reflexivity. Qed.
Definition lF10_2 : list (Z * nat) := Eval vm_compute in grl Rj10_2 S10_2 F10_2.
Lemma RF10_2 : Run S10_2 F10_2 S10_3 (pSh lF10_2) (pV lF10_2).
Proof. apply (crun_run Rj10_2 4). vm_compute. reflexivity. Qed.
Definition lC10_3 : list (Z * nat) := Eval vm_compute in grl R10_3 S10_3 K10_3.
Lemma RC10_3 : Run S10_3 K10_3 S10_3 (pSh lC10_3) (pV lC10_3).
Proof. apply (crun_run R10_3 4). vm_compute. reflexivity. Qed.
Definition lF10_3 : list (Z * nat) := Eval vm_compute in grl Rj10_3 S10_3 F10_3.
Lemma RF10_3 : Run S10_3 F10_3 S10_4 (pSh lF10_3) (pV lF10_3).
Proof. apply (crun_run Rj10_3 4). vm_compute. reflexivity. Qed.
Definition lC10_4 : list (Z * nat) := Eval vm_compute in grl R10_4 S10_4 K10_4.
Lemma RC10_4 : Run S10_4 K10_4 S10_4 (pSh lC10_4) (pV lC10_4).
Proof. apply (crun_run R10_4 4). vm_compute. reflexivity. Qed.
Definition lF10_4 : list (Z * nat) := Eval vm_compute in grl Rj10_4 S10_4 F10_4.
Lemma RF10_4 : Run S10_4 F10_4 S10_5 (pSh lF10_4) (pV lF10_4).
Proof. apply (crun_run Rj10_4 4). vm_compute. reflexivity. Qed.
Definition lC10_5 : list (Z * nat) := Eval vm_compute in grl R10_5 S10_5 K10_5.
Lemma RC10_5 : Run S10_5 K10_5 S10_5 (pSh lC10_5) (pV lC10_5).
Proof. apply (crun_run R10_5 4). vm_compute. reflexivity. Qed.
Definition lF10_5 : list (Z * nat) := Eval vm_compute in grl Rj10_5 S10_5 F10_5.
Lemma RF10_5 : Run S10_5 F10_5 S10_6 (pSh lF10_5) (pV lF10_5).
Proof. apply (crun_run Rj10_5 4). vm_compute. reflexivity. Qed.
Definition lC10_6 : list (Z * nat) := Eval vm_compute in grl R10_6 S10_6 K10_6.
Lemma RC10_6 : Run S10_6 K10_6 S10_6 (pSh lC10_6) (pV lC10_6).
Proof. apply (crun_run R10_6 4). vm_compute. reflexivity. Qed.
Definition lF10_6 : list (Z * nat) := Eval vm_compute in grl Rj10_6 S10_6 F10_6.
Lemma RF10_6 : Run S10_6 F10_6 S10_7 (pSh lF10_6) (pV lF10_6).
Proof. apply (crun_run Rj10_6 4). vm_compute. reflexivity. Qed.
Definition lC10_7 : list (Z * nat) := Eval vm_compute in grl R10_7 S10_7 K10_7.
Lemma RC10_7 : Run S10_7 K10_7 S10_7 (pSh lC10_7) (pV lC10_7).
Proof. apply (crun_run R10_7 4). vm_compute. reflexivity. Qed.
Definition lF10_7 : list (Z * nat) := Eval vm_compute in grl Rj10_7 S10_7 F10_7.
Lemma RF10_7 : Run S10_7 F10_7 S10_8 (pSh lF10_7) (pV lF10_7).
Proof. apply (crun_run Rj10_7 4). vm_compute. reflexivity. Qed.
Definition lC10_8 : list (Z * nat) := Eval vm_compute in grl R10_8 S10_8 K10_8.
Lemma RC10_8 : Run S10_8 K10_8 S10_8 (pSh lC10_8) (pV lC10_8).
Proof. apply (crun_run R10_8 4). vm_compute. reflexivity. Qed.
Definition lF10_8 : list (Z * nat) := Eval vm_compute in grl Rj10_8 S10_8 F10_8.
Lemma RF10_8 : Run S10_8 F10_8 Se10 (pSh lF10_8) (pV lF10_8).
Proof. apply (crun_run Rj10_8 4). vm_compute. reflexivity. Qed.

Definition segs10 (n1 n2 n3 n4 n5 n6 n7 n8 : nat) : list seg :=
  [SP lF10_0; SK lC10_1 n1; SP lF10_1; SK lC10_2 n2; SP lF10_2; SK lC10_3 n3; SP lF10_3; SK lC10_4 n4;
    SP lF10_4; SK lC10_5 n5; SP lF10_5; SK lC10_6 n6; SP lF10_6; SK lC10_7 n7; SP lF10_7; SK lC10_8
    n8; SP lF10_8].

Lemma runA10 : forall n1 n2 n3 n4 n5 n6 n7 n8,
  Run st100 (F10_0 ++ rp K10_1 n1 ++ F10_1 ++ rp K10_2 n2 ++ F10_2 ++ rp K10_3 n3 ++ F10_3 ++ rp K10_4
    n4 ++ F10_4 ++ rp K10_5 n5 ++ F10_5 ++ rp K10_6 n6 ++ F10_6 ++ rp K10_7 n7 ++ F10_7 ++ rp K10_8
    n8 ++ F10_8 ++ []) Se10
      (segSh (segs10 n1 n2 n3 n4 n5 n6 n7 n8)) (segV (segs10 n1 n2 n3 n4 n5 n6 n7 n8)).
Proof.
  intros n1 n2 n3 n4 n5 n6 n7 n8. unfold segs10.
  exact (run_SP _ _ _ _ _ _ _ RF10_0
    (run_SK _ _ _ _ _ _ _ RC10_1
    (run_SP _ _ _ _ _ _ _ RF10_1 (run_SK _ _ _ _ _ _ _ RC10_2
    (run_SP _ _ _ _ _ _ _ RF10_2 (run_SK _ _ _ _ _ _ _ RC10_3
    (run_SP _ _ _ _ _ _ _ RF10_3 (run_SK _ _ _ _ _ _ _ RC10_4
    (run_SP _ _ _ _ _ _ _ RF10_4 (run_SK _ _ _ _ _ _ _ RC10_5
    (run_SP _ _ _ _ _ _ _ RF10_5 (run_SK _ _ _ _ _ _ _ RC10_6
    (run_SP _ _ _ _ _ _ _ RF10_6 (run_SK _ _ _ _ _ _ _ RC10_7
    (run_SP _ _ _ _ _ _ _ RF10_7 (run_SK _ _ _ _ _ _ _ RC10_8
    (run_SP _ _ _ _ _ _ _ RF10_8 (run_end _)))))))))))))))))).
Qed.

(** ** The carry chain *)

Definition as10 := Eval vm_compute in asm 0 (segs10 O O O O O O O O).
Definition k10_0 : list bool := Eval vm_compute in
  match as10 with Some ([Lit a; _; _; _; _; _; _; _; _; _; _; _; _; _; _; _; _], _) => a | _ => [] end.
Definition k10_1 : list bool := Eval vm_compute in
  match as10 with Some ([_; _; Lit a; _; _; _; _; _; _; _; _; _; _; _; _; _; _], _) => a | _ => [] end.
Definition k10_2 : list bool := Eval vm_compute in
  match as10 with Some ([_; _; _; _; Lit a; _; _; _; _; _; _; _; _; _; _; _; _], _) => a | _ => [] end.
Definition k10_3 : list bool := Eval vm_compute in
  match as10 with Some ([_; _; _; _; _; _; Lit a; _; _; _; _; _; _; _; _; _; _], _) => a | _ => [] end.
Definition k10_4 : list bool := Eval vm_compute in
  match as10 with Some ([_; _; _; _; _; _; _; _; Lit a; _; _; _; _; _; _; _; _], _) => a | _ => [] end.
Definition k10_5 : list bool := Eval vm_compute in
  match as10 with Some ([_; _; _; _; _; _; _; _; _; _; Lit a; _; _; _; _; _; _], _) => a | _ => [] end.
Definition k10_6 : list bool := Eval vm_compute in
  match as10 with Some ([_; _; _; _; _; _; _; _; _; _; _; _; Lit a; _; _; _; _], _) => a | _ => [] end.
Definition k10_7 : list bool := Eval vm_compute in
  match as10 with Some ([_; _; _; _; _; _; _; _; _; _; _; _; _; _; Lit a; _; _], _) => a | _ => [] end.
Definition k10_8 : list bool := Eval vm_compute in
  match as10 with Some ([_; _; _; _; _; _; _; _; _; _; _; _; _; _; _; _; Lit a], _) => a | _ => [] end.
Definition kk10_1 : list bool := Eval vm_compute in
  match as10 with Some ([_; Rep p _; _; _; _; _; _; _; _; _; _; _; _; _; _; _; _], _) => p | _ => [] end.
Definition kk10_2 : list bool := Eval vm_compute in
  match as10 with Some ([_; _; _; Rep p _; _; _; _; _; _; _; _; _; _; _; _; _; _], _) => p | _ => [] end.
Definition kk10_3 : list bool := Eval vm_compute in
  match as10 with Some ([_; _; _; _; _; Rep p _; _; _; _; _; _; _; _; _; _; _; _], _) => p | _ => [] end.
Definition kk10_4 : list bool := Eval vm_compute in
  match as10 with Some ([_; _; _; _; _; _; _; Rep p _; _; _; _; _; _; _; _; _; _], _) => p | _ => [] end.
Definition kk10_5 : list bool := Eval vm_compute in
  match as10 with Some ([_; _; _; _; _; _; _; _; _; Rep p _; _; _; _; _; _; _; _], _) => p | _ => [] end.
Definition kk10_6 : list bool := Eval vm_compute in
  match as10 with Some ([_; _; _; _; _; _; _; _; _; _; _; Rep p _; _; _; _; _; _], _) => p | _ => [] end.
Definition kk10_7 : list bool := Eval vm_compute in
  match as10 with Some ([_; _; _; _; _; _; _; _; _; _; _; _; _; Rep p _; _; _; _], _) => p | _ => [] end.
Definition kk10_8 : list bool := Eval vm_compute in
  match as10 with Some ([_; _; _; _; _; _; _; _; _; _; _; _; _; _; _; Rep p _; _], _) => p | _ => [] end.
Definition cB10 : Z := Eval vm_compute in match as10 with Some (_, c) => c | None => (-1)%Z end.

Lemma as10_ok : forall n1 n2 n3 n4 n5 n6 n7 n8,
  asm 0 (segs10 n1 n2 n3 n4 n5 n6 n7 n8) = Some ([Lit k10_0; Rep kk10_1 n1; Lit k10_1; Rep kk10_2 n2;
    Lit k10_2; Rep kk10_3 n3; Lit k10_3; Rep kk10_4 n4; Lit k10_4; Rep kk10_5 n5; Lit k10_5; Rep
    kk10_6 n6; Lit k10_6; Rep kk10_7 n7; Lit k10_7; Rep kk10_8 n8; Lit k10_8], cB10).
Proof. intros n1 n2 n3 n4 n5 n6 n7 n8. vm_compute. reflexivity. Qed.

(** ** The closing computation *)

Definition ec10 := Eval vm_compute in endcert 6000 (addpost Se10 Fw10).
Definition ae10 : Z := Eval vm_compute in match ec10 with Some (a, _, _, _) => a | None => 0%Z end.
Definition z1_10 : nat := Eval vm_compute in match ec10 with Some (_, z, _, _) => z | None => O end.
Definition z2_10 : nat := Eval vm_compute in match ec10 with Some (_, _, z, _) => z | None => O end.
Definition w11 : list bool := Eval vm_compute in match ec10 with Some (_, _, _, x) => x | None => [] end.
Definition la10 : nat := Eval vm_compute in (z1_10 + z2_10 - 1) / 3.
Definition tp10 : N := Eval vm_compute in Z.to_N ((cB10 + ae10) / 4 ^ Z.of_nat la10).
Definition ab10 : list bool := Eval vm_compute in
  zbits ((cB10 + ae10) mod 4 ^ Z.of_nat la10) (2 * la10).

Lemma ec10_ok : endcert 6000 (addpost Se10 Fw10) = Some (ae10, z1_10, z2_10, w11).
Proof. vm_compute. reflexivity. Qed.

Lemma cB10_nn : (0 <= cB10)%Z.
Proof. apply Z.leb_le. vm_compute. reflexivity. Qed.

Lemma ab10_val : (Z.of_N (bvalN ab10) + Z.of_N tp10 * pw4 la10 = cB10 + ae10)%Z.
Proof. vm_compute. reflexivity. Qed.

Lemma ab10_len : length ab10 = 2 * la10.
Proof. vm_compute. reflexivity. Qed.

Lemma z_10 : z1_10 + z2_10 = 3 * la10 + 1.
Proof. vm_compute. reflexivity. Qed.

Definition Cw10 (n1 n2 n3 n4 n5 n6 n7 n8 : nat) : list bool :=
  den [Lit k10_0; Rep kk10_1 n1; Lit k10_1; Rep kk10_2 n2; Lit k10_2; Rep kk10_3 n3; Lit k10_3; Rep
    kk10_4 n4; Lit k10_4; Rep kk10_5 n5; Lit k10_5; Rep kk10_6 n6; Lit k10_6; Rep kk10_7 n7; Lit
    k10_7; Rep kk10_8 n8; Lit k10_8] ++ ab10.
Definition lc10 (n1 n2 n3 n4 n5 n6 n7 n8 : nat) : nat := segSh (segs10 n1 n2 n3 n4 n5 n6 n7 n8) + la10.

Lemma Cw10_len : forall n1 n2 n3 n4 n5 n6 n7 n8, length (Cw10 n1 n2 n3 n4 n5 n6 n7 n8) = 2 * lc10 n1 n2 n3 n4 n5 n6 n7 n8.
Proof.
  intros n1 n2 n3 n4 n5 n6 n7 n8.
  exact (proj1 (stageA st100 _ Se10 (segs10 n1 n2 n3 n4 n5 n6 n7 n8) 6000 Fw10 ae10 z1_10 z2_10 w11 _ cB10 ab10 la10
              (Z.of_N tp10) (runA10 n1 n2 n3 n4 n5 n6 n7 n8) ec10_ok (as10_ok n1 n2 n3 n4 n5 n6 n7 n8) cB10_nn ab10_val ab10_len z_10)).
Qed.

Lemma end10 : forall n1 n2 n3 n4 n5 n6 n7 n8 h k, (1 <= k)%nat -> exists n M',
  tickN 3 n (rep10 k ++ c1101 ++ repeat true (3 * h) ++ rep10 je10 ++ c1101 ++
             encb false (b10 (cc10_1 + (n1 * kq10_1 + jj10_1) + 1) (cc10_2 + (n2 * kq10_2 + jj10_2) + 1) (cc10_3
               + (n3 * kq10_3 + jj10_3) + 1) (cc10_4 + (n4 * kq10_4 + jj10_4) + 1) (cc10_5 + (n5 *
               kq10_5 + jj10_5) + 1) (cc10_6 + (n6 * kq10_6 + jj10_6) + 1) (cc10_7 + (n7 * kq10_7 +
               jj10_7) + 1) (cc10_8 + (n8 * kq10_8 + jj10_8) + 1)) ++ w10) =
    Some (Slev M' (3 * (h + lc10 n1 n2 n3 n4 n5 n6 n7 n8) + 1) w11) /\
  Z.of_nat M' = (Z.of_nat k +
                 (Z.of_nat (bval (Cw10 n1 n2 n3 n4 n5 n6 n7 n8)) + Z.of_N tp10 * pw4 (lc10 n1 n2 n3 n4 n5 n6 n7 n8)) * pw4 h)%Z.
Proof.
  intros n1 n2 n3 n4 n5 n6 n7 n8 h k Hk.
  destruct (stageA st100 _ Se10 (segs10 n1 n2 n3 n4 n5 n6 n7 n8) 6000 Fw10 ae10 z1_10 z2_10 w11 _ cB10 ab10 la10
              (Z.of_N tp10) (runA10 n1 n2 n3 n4 n5 n6 n7 n8) ec10_ok (as10_ok n1 n2 n3 n4 n5 n6 n7 n8) cB10_nn ab10_val ab10_len z_10) as [_ H].
  destruct (H h k Hk) as [n [M' [E D]]]. exists n, M'. split; [| exact D].
  change (rep10 je10 ++ c1101 ++ encb false (b10 (cc10_1 + (n1 * kq10_1 + jj10_1) + 1) (cc10_2 + (n2 *
    kq10_2 + jj10_2) + 1) (cc10_3 + (n3 * kq10_3 + jj10_3) + 1) (cc10_4 + (n4 * kq10_4 + jj10_4) +
    1) (cc10_5 + (n5 * kq10_5 + jj10_5) + 1) (cc10_6 + (n6 * kq10_6 + jj10_6) + 1) (cc10_7 + (n7 *
    kq10_7 + jj10_7) + 1) (cc10_8 + (n8 * kq10_8 + jj10_8) + 1)) ++ w10)
    with (cells10 (cc10_1 + (n1 * kq10_1 + jj10_1) + 1) (cc10_2 + (n2 * kq10_2 + jj10_2) + 1) (cc10_3 + (n3 * kq10_3 + jj10_3) + 1) (cc10_4 + (n4 * kq10_4 + jj10_4) + 1) (cc10_5 + (n5 * kq10_5 + jj10_5) + 1) (cc10_6 + (n6 * kq10_6 + jj10_6) + 1) (cc10_7 + (n7 * kq10_7 + jj10_7) + 1) (cc10_8 + (n8 * kq10_8 + jj10_8) + 1)).
  rewrite cells10_cut.
  cbv [st100 conc] in E. rewrite ?app_nil_r, <- ?app_assoc in E. rewrite ?app_nil_r, <- ?app_assoc.
  exact E.
Qed.

(** ** What the division needs: which blocks are tripled, and the residues of the counts *)

Definition cfg10_trip : list bool := Eval vm_compute in
  map (fun P => negb (N.eqb (bvalN P mod 3) 0)) [kk10_1; kk10_2; kk10_3; kk10_4; kk10_5; kk10_6; kk10_7; kk10_8].
Definition cfg10_rho : list N := Eval vm_compute in
  [(((rc10_1 + 1594323 - (N.of_nat cc10_1 + 1 + N.of_nat jj10_1)%N) * (N.of_nat kq10_1 mod 3)) mod 3)%N; (((rc10_2 + 1594323 - (N.of_nat cc10_2 + 1 + N.of_nat jj10_2)%N) * (N.of_nat kq10_2 mod 3)) mod 3)%N; (((rc10_3 + 1594323 - (N.of_nat cc10_3 + 1 + N.of_nat jj10_3)%N) * (N.of_nat kq10_3 mod 3)) mod 3)%N; (((rc10_4 + 1594323 - (N.of_nat cc10_4 + 1 + N.of_nat jj10_4)%N) * (N.of_nat kq10_4 mod 3)) mod 3)%N; (((rc10_5 + 1594323 - (N.of_nat cc10_5 + 1 + N.of_nat jj10_5)%N) * (N.of_nat kq10_5 mod 3)) mod 3)%N; (((rc10_6 + 1594323 - (N.of_nat cc10_6 + 1 + N.of_nat jj10_6)%N) * (N.of_nat kq10_6 mod 3)) mod 3)%N; (((rc10_7 + 1594323 - (N.of_nat cc10_7 + 1 + N.of_nat jj10_7)%N) * (N.of_nat kq10_7 mod 3)) mod 3)%N; (((rc10_8 + 1594323 - (N.of_nat cc10_8 + 1 + N.of_nat jj10_8)%N) * (N.of_nat kq10_8 mod 3)) mod 3)%N].
Definition cfg10_k : list nat := Eval vm_compute in [kq10_1; kq10_2; kq10_3; kq10_4; kq10_5; kq10_6; kq10_7; kq10_8].
Definition cfg10_j : list nat := Eval vm_compute in [jj10_1; jj10_2; jj10_3; jj10_4; jj10_5; jj10_6; jj10_7; jj10_8].
Definition cfg10_rhoT : Z := Eval vm_compute in ((2 * vT10) mod 3)%Z.

End L1011a.

Module L1011b.

(** * 1RB1LB_1RC0RD_0LA1RE_0RF1LC_1LA0RB_---1LC: from level 10 to level 11

    The division by 3 of [0100 (10)^(h-2) C] with the counts as variables, level 11 for the
    real counts, and the residues modulo 3^3 and lower bounds of the counts of level 11.
    Generated by a script. *)

Import Individual62.
Import T694_levels End694 Sym694 Lev694 Lvl1_694 Eng694 Cert694 Run694 Res694 Gen694.
Import L23 L34 L45 L56 L6i L67a L67b L78a L78b L89a L89b L910a L910b L1011a.
Import Lia Arith PeanoNat Bool NArith ZArith.
Import Coq.Lists.List.
Import ListNotations.

(** ** The division *)

Lemma Zl10_den : forall G x1 x2 x3 x4 x5 x6 x7 x8,
  [false; false; true; false] ++ rep01 (G * 3 + 1) ++ Cw10 (x1 * 3 + 2) (x2 * 3 + 0) (x3 * 3 + 1) (x4 * 3 + 0) (x5 * 3 + 0) (x6 * 3 + 0) (x7 * 3 + 2) (x8 * 3 + 1) =
  den [Lit [false; false; true; false]; Rep (rp [false; true] 3) G; Lit (rp [false; true] 1 ++ k10_0);
    Rep (rp kk10_1 3) x1; Lit (rp kk10_1 2 ++ k10_1); Rep (rp kk10_2 3) x2; Lit (rp kk10_2 0 ++
    k10_2); Rep (rp kk10_3 3) x3; Lit (rp kk10_3 1 ++ k10_3); Rep (rp kk10_4 3) x4; Lit (rp kk10_4 0
    ++ k10_4); Rep (rp kk10_5 3) x5; Lit (rp kk10_5 0 ++ k10_5); Rep (rp kk10_6 3) x6; Lit (rp
    kk10_6 0 ++ k10_6); Rep (rp kk10_7 3) x7; Lit (rp kk10_7 2 ++ k10_7); Rep (rp kk10_8 3) x8; Lit
    (rp kk10_8 1 ++ k10_8 ++ ab10)].
Proof.
  intros G x1 x2 x3 x4 x5 x6 x7 x8. unfold Cw10. cbn [den bden].
  change (rep01 (G * 3 + 1)) with (rp [false; true] (G * 3 + 1)).
  rewrite ?rp_add, ?rp_mul, ?app_nil_r, <- ?app_assoc. reflexivity.
Qed.

Definition dv10 := Eval vm_compute in
  dmB 3 [Lit [false; false; true; false]; Rep (rp [false; true] 3) O; Lit (rp [false; true] 1 ++
    k10_0); Rep (rp kk10_1 3) O; Lit (rp kk10_1 2 ++ k10_1); Rep (rp kk10_2 3) O; Lit (rp kk10_2 0
    ++ k10_2); Rep (rp kk10_3 3) O; Lit (rp kk10_3 1 ++ k10_3); Rep (rp kk10_4 3) O; Lit (rp kk10_4
    0 ++ k10_4); Rep (rp kk10_5 3) O; Lit (rp kk10_5 0 ++ k10_5); Rep (rp kk10_6 3) O; Lit (rp
    kk10_6 0 ++ k10_6); Rep (rp kk10_7 3) O; Lit (rp kk10_7 2 ++ k10_7); Rep (rp kk10_8 3) O; Lit
    (rp kk10_8 1 ++ k10_8 ++ ab10)] tp10.
Definition a11_0 : list bool := Eval vm_compute in
  match dv10 with Some ([Lit a; _; _; _; _; _; _; _; _; _; _; _; _; _; _; _; _; _; _], _) => a | _ => [] end.
Definition a11_1 : list bool := Eval vm_compute in
  match dv10 with Some ([_; _; Lit a; _; _; _; _; _; _; _; _; _; _; _; _; _; _; _; _], _) => a | _ => [] end.
Definition a11_2 : list bool := Eval vm_compute in
  match dv10 with Some ([_; _; _; _; Lit a; _; _; _; _; _; _; _; _; _; _; _; _; _; _], _) => a | _ => [] end.
Definition a11_3 : list bool := Eval vm_compute in
  match dv10 with Some ([_; _; _; _; _; _; Lit a; _; _; _; _; _; _; _; _; _; _; _; _], _) => a | _ => [] end.
Definition a11_4 : list bool := Eval vm_compute in
  match dv10 with Some ([_; _; _; _; _; _; _; _; Lit a; _; _; _; _; _; _; _; _; _; _], _) => a | _ => [] end.
Definition a11_5 : list bool := Eval vm_compute in
  match dv10 with Some ([_; _; _; _; _; _; _; _; _; _; Lit a; _; _; _; _; _; _; _; _], _) => a | _ => [] end.
Definition a11_6 : list bool := Eval vm_compute in
  match dv10 with Some ([_; _; _; _; _; _; _; _; _; _; _; _; Lit a; _; _; _; _; _; _], _) => a | _ => [] end.
Definition a11_7 : list bool := Eval vm_compute in
  match dv10 with Some ([_; _; _; _; _; _; _; _; _; _; _; _; _; _; Lit a; _; _; _; _], _) => a | _ => [] end.
Definition a11_8 : list bool := Eval vm_compute in
  match dv10 with Some ([_; _; _; _; _; _; _; _; _; _; _; _; _; _; _; _; Lit a; _; _], _) => a | _ => [] end.
Definition a11_9 : list bool := Eval vm_compute in
  match dv10 with Some ([_; _; _; _; _; _; _; _; _; _; _; _; _; _; _; _; _; _; Lit a], _) => a | _ => [] end.
Definition P11_1 : list bool := Eval vm_compute in
  match dv10 with Some ([_; Rep p _; _; _; _; _; _; _; _; _; _; _; _; _; _; _; _; _; _], _) => p | _ => [] end.
Definition P11_2 : list bool := Eval vm_compute in
  match dv10 with Some ([_; _; _; Rep p _; _; _; _; _; _; _; _; _; _; _; _; _; _; _; _], _) => p | _ => [] end.
Definition P11_3 : list bool := Eval vm_compute in
  match dv10 with Some ([_; _; _; _; _; Rep p _; _; _; _; _; _; _; _; _; _; _; _; _; _], _) => p | _ => [] end.
Definition P11_4 : list bool := Eval vm_compute in
  match dv10 with Some ([_; _; _; _; _; _; _; Rep p _; _; _; _; _; _; _; _; _; _; _; _], _) => p | _ => [] end.
Definition P11_5 : list bool := Eval vm_compute in
  match dv10 with Some ([_; _; _; _; _; _; _; _; _; Rep p _; _; _; _; _; _; _; _; _; _], _) => p | _ => [] end.
Definition P11_6 : list bool := Eval vm_compute in
  match dv10 with Some ([_; _; _; _; _; _; _; _; _; _; _; Rep p _; _; _; _; _; _; _; _], _) => p | _ => [] end.
Definition P11_7 : list bool := Eval vm_compute in
  match dv10 with Some ([_; _; _; _; _; _; _; _; _; _; _; _; _; Rep p _; _; _; _; _; _], _) => p | _ => [] end.
Definition P11_8 : list bool := Eval vm_compute in
  match dv10 with Some ([_; _; _; _; _; _; _; _; _; _; _; _; _; _; _; Rep p _; _; _; _], _) => p | _ => [] end.
Definition P11_9 : list bool := Eval vm_compute in
  match dv10 with Some ([_; _; _; _; _; _; _; _; _; _; _; _; _; _; _; _; _; Rep p _; _], _) => p | _ => [] end.
Definition r11 : N := Eval vm_compute in match dv10 with Some (_, r) => r | None => 9%N end.
Definition je11 : nat := Eval vm_compute in 3 + N.to_nat r11.

Lemma dv10_ok : forall G x1 x2 x3 x4 x5 x6 x7 x8,
  dmB 3 [Lit [false; false; true; false]; Rep (rp [false; true] 3) G; Lit (rp [false; true] 1 ++
    k10_0); Rep (rp kk10_1 3) x1; Lit (rp kk10_1 2 ++ k10_1); Rep (rp kk10_2 3) x2; Lit (rp kk10_2 0
    ++ k10_2); Rep (rp kk10_3 3) x3; Lit (rp kk10_3 1 ++ k10_3); Rep (rp kk10_4 3) x4; Lit (rp
    kk10_4 0 ++ k10_4); Rep (rp kk10_5 3) x5; Lit (rp kk10_5 0 ++ k10_5); Rep (rp kk10_6 3) x6; Lit
    (rp kk10_6 0 ++ k10_6); Rep (rp kk10_7 3) x7; Lit (rp kk10_7 2 ++ k10_7); Rep (rp kk10_8 3) x8;
    Lit (rp kk10_8 1 ++ k10_8 ++ ab10)] tp10 =
  Some ([Lit a11_0; Rep P11_1 G; Lit a11_1; Rep P11_2 x1; Lit a11_2; Rep P11_3 x2; Lit a11_3; Rep
    P11_4 x3; Lit a11_4; Rep P11_5 x4; Lit a11_5; Rep P11_6 x5; Lit a11_6; Rep P11_7 x6; Lit a11_7;
    Rep P11_8 x7; Lit a11_8; Rep P11_9 x8; Lit a11_9], r11).
Proof. intros G x1 x2 x3 x4 x5 x6 x7 x8. vm_compute. reflexivity. Qed.

Lemma tp10_lt : (tp10 < 3)%N.
Proof. reflexivity. Qed.

(** ** Level 11 *)

Definition b11 (d1 d2 d3 d4 d5 d6 d7 d8 d9 : nat) : list bool :=
  den [Lit a11_0; Rep P11_1 d1; Lit a11_1; Rep P11_2 d2; Lit a11_2; Rep P11_3 d3; Lit a11_3; Rep P11_4
    d4; Lit a11_4; Rep P11_5 d5; Lit a11_5; Rep P11_6 d6; Lit a11_6; Rep P11_7 d7; Lit a11_7; Rep
    P11_8 d8; Lit a11_8; Rep P11_9 d9; Lit a11_9].

Definition c11_1 : nat := (2 * bval (b10 c10_1 c10_2 c10_3 c10_4 c10_5 c10_6 c10_7 c10_8)) / 3.
Definition c11_2 : nat := ((c10_1 - (cc10_1 + 1 + jj10_1)) / kq10_1) / 3.
Definition c11_3 : nat := ((c10_2 - (cc10_2 + 1 + jj10_2)) / kq10_2) / 3.
Definition c11_4 : nat := ((c10_3 - (cc10_3 + 1 + jj10_3)) / kq10_3) / 3.
Definition c11_5 : nat := ((c10_4 - (cc10_4 + 1 + jj10_4)) / kq10_4) / 3.
Definition c11_6 : nat := ((c10_5 - (cc10_5 + 1 + jj10_5)) / kq10_5) / 3.
Definition c11_7 : nat := ((c10_6 - (cc10_6 + 1 + jj10_6)) / kq10_6) / 3.
Definition c11_8 : nat := ((c10_7 - (cc10_7 + 1 + jj10_7)) / kq10_7) / 3.
Definition c11_9 : nat := ((c10_8 - (cc10_8 + 1 + jj10_8)) / kq10_8) / 3.

Lemma ET10 : 2 * bval (b10 c10_1 c10_2 c10_3 c10_4 c10_5 c10_6 c10_7 c10_8) = c11_1 * 3 + 1.
Proof. pose proof T10_res as H. unfold vT10 in H. unfold c11_1. gl (bval (b10 c10_1 c10_2 c10_3 c10_4 c10_5 c10_6 c10_7 c10_8)). Qed.

Lemma EC10_1 : c10_1 = cc10_1 + ((c11_2 * 3 + 2) * kq10_1 + jj10_1) + 1.
Proof.
  pose proof c10_1_res as H. pose proof c10_1_res2 as H2. pose proof c10_1_lb as Hb.
  unfold rc10_1 in H. unfold rb10_1 in H2. unfold lb10_1 in Hb.
  unfold c11_2, cc10_1, kq10_1, jj10_1. cbn [Z.of_N] in H, H2, Hb. gl c10_1.
Qed.

Lemma EC10_2 : c10_2 = cc10_2 + ((c11_3 * 3 + 0) * kq10_2 + jj10_2) + 1.
Proof.
  pose proof c10_2_res as H. pose proof c10_2_res2 as H2. pose proof c10_2_lb as Hb.
  unfold rc10_2 in H. unfold rb10_2 in H2. unfold lb10_2 in Hb.
  unfold c11_3, cc10_2, kq10_2, jj10_2. cbn [Z.of_N] in H, H2, Hb. gl c10_2.
Qed.

Lemma EC10_3 : c10_3 = cc10_3 + ((c11_4 * 3 + 1) * kq10_3 + jj10_3) + 1.
Proof.
  pose proof c10_3_res as H. pose proof c10_3_res2 as H2. pose proof c10_3_lb as Hb.
  unfold rc10_3 in H. unfold rb10_3 in H2. unfold lb10_3 in Hb.
  unfold c11_4, cc10_3, kq10_3, jj10_3. cbn [Z.of_N] in H, H2, Hb. gl c10_3.
Qed.

Lemma EC10_4 : c10_4 = cc10_4 + ((c11_5 * 3 + 0) * kq10_4 + jj10_4) + 1.
Proof.
  pose proof c10_4_res as H. pose proof c10_4_res2 as H2. pose proof c10_4_lb as Hb.
  unfold rc10_4 in H. unfold rb10_4 in H2. unfold lb10_4 in Hb.
  unfold c11_5, cc10_4, kq10_4, jj10_4. cbn [Z.of_N] in H, H2, Hb. gl c10_4.
Qed.

Lemma EC10_5 : c10_5 = cc10_5 + ((c11_6 * 3 + 0) * kq10_5 + jj10_5) + 1.
Proof.
  pose proof c10_5_res as H. pose proof c10_5_res2 as H2. pose proof c10_5_lb as Hb.
  unfold rc10_5 in H. unfold rb10_5 in H2. unfold lb10_5 in Hb.
  unfold c11_6, cc10_5, kq10_5, jj10_5. cbn [Z.of_N] in H, H2, Hb. gl c10_5.
Qed.

Lemma EC10_6 : c10_6 = cc10_6 + ((c11_7 * 3 + 0) * kq10_6 + jj10_6) + 1.
Proof.
  pose proof c10_6_res as H. pose proof c10_6_res2 as H2. pose proof c10_6_lb as Hb.
  unfold rc10_6 in H. unfold rb10_6 in H2. unfold lb10_6 in Hb.
  unfold c11_7, cc10_6, kq10_6, jj10_6. cbn [Z.of_N] in H, H2, Hb. gl c10_6.
Qed.

Lemma EC10_7 : c10_7 = cc10_7 + ((c11_8 * 3 + 2) * kq10_7 + jj10_7) + 1.
Proof.
  pose proof c10_7_res as H. pose proof c10_7_res2 as H2. pose proof c10_7_lb as Hb.
  unfold rc10_7 in H. unfold rb10_7 in H2. unfold lb10_7 in Hb.
  unfold c11_8, cc10_7, kq10_7, jj10_7. cbn [Z.of_N] in H, H2, Hb. gl c10_7.
Qed.

Lemma EC10_8 : c10_8 = cc10_8 + ((c11_9 * 3 + 1) * kq10_8 + jj10_8) + 1.
Proof.
  pose proof c10_8_res as H. pose proof c10_8_res2 as H2. pose proof c10_8_lb as Hb.
  unfold rc10_8 in H. unfold rb10_8 in H2. unfold lb10_8 in Hb.
  unfold c11_9, cc10_8, kq10_8, jj10_8. cbn [Z.of_N] in H, H2, Hb. gl c10_8.
Qed.

Definition u11 : nat :=
  2 + 2 * bval (b10 (cc10_1 + ((c11_2 * 3 + 2) * kq10_1 + jj10_1) + 1) (cc10_2 + ((c11_3 * 3 + 0) *
    kq10_2 + jj10_2) + 1) (cc10_3 + ((c11_4 * 3 + 1) * kq10_3 + jj10_3) + 1) (cc10_4 + ((c11_5 * 3 +
    0) * kq10_4 + jj10_4) + 1) (cc10_5 + ((c11_6 * 3 + 0) * kq10_5 + jj10_5) + 1) (cc10_6 + ((c11_7
    * 3 + 0) * kq10_6 + jj10_6) + 1) (cc10_7 + ((c11_8 * 3 + 2) * kq10_7 + jj10_7) + 1) (cc10_8 +
    ((c11_9 * 3 + 1) * kq10_8 + jj10_8) + 1)) + lc10 (c11_2 * 3 + 2) (c11_3 * 3 + 0) (c11_4 * 3 + 1)
    (c11_5 * 3 + 0) (c11_6 * 3 + 0) (c11_7 * 3 + 0) (c11_8 * 3 + 2) (c11_9 * 3 + 1).

Theorem lvl11 : Lvl je11 (b11 c11_1 c11_2 c11_3 c11_4 c11_5 c11_6 c11_7 c11_8 c11_9) u11 w11.
Proof.
  pose proof lvl10 as H. pose proof ET10 as HT.
  rewrite EC10_1 in H, HT.
  rewrite EC10_2 in H, HT.
  rewrite EC10_3 in H, HT.
  rewrite EC10_4 in H, HT.
  rewrite EC10_5 in H, HT.
  rewrite EC10_6 in H, HT.
  rewrite EC10_7 in H, HT.
  rewrite EC10_8 in H, HT.
  apply (level_next_top _ (b10 (cc10_1 + ((c11_2 * 3 + 2) * kq10_1 + jj10_1) + 1) (cc10_2 + ((c11_3 *
    3 + 0) * kq10_2 + jj10_2) + 1) (cc10_3 + ((c11_4 * 3 + 1) * kq10_3 + jj10_3) + 1) (cc10_4 +
    ((c11_5 * 3 + 0) * kq10_4 + jj10_4) + 1) (cc10_5 + ((c11_6 * 3 + 0) * kq10_5 + jj10_5) + 1)
    (cc10_6 + ((c11_7 * 3 + 0) * kq10_6 + jj10_6) + 1) (cc10_7 + ((c11_8 * 3 + 2) * kq10_7 + jj10_7)
    + 1) (cc10_8 + ((c11_9 * 3 + 1) * kq10_8 + jj10_8) + 1)) _ w10 (Cw10 (c11_2 * 3 + 2) (c11_3 * 3
    + 0) (c11_4 * 3 + 1) (c11_5 * 3 + 0) (c11_6 * 3 + 0) (c11_7 * 3 + 0) (c11_8 * 3 + 2) (c11_9 * 3
    + 1)) (lc10 (c11_2 * 3 + 2) (c11_3 * 3 + 0) (c11_4 * 3 + 1) (c11_5 * 3 + 0) (c11_6 * 3 + 0)
    (c11_7 * 3 + 0) (c11_8 * 3 + 2) (c11_9 * 3 + 1)) tp10 (b11 c11_1 c11_2 c11_3 c11_4 c11_5 c11_6
    c11_7 c11_8 c11_9) r11 w11 H (Cw10_len _ _ _ _ _ _ _ _) tp10_lt (fun k Hk => end10 _ _ _ _ _ _ _
    _ _ k Hk)).
  rewrite HT, Zl10_den. apply dmB_sound. apply dv10_ok.
Qed.

(** ** The counts of level 11 modulo 3^3, and lower bounds *)

Definition rc11_1 : N := Eval vm_compute in Z.to_N (((2 * vT10 - 1) / 3) mod 27).
Lemma c11_1_res : (Z.of_nat c11_1 mod Z.of_N 27 = Z.of_N rc11_1)%Z.
Proof.
  pose proof T10_res as H. unfold vT10 in H. unfold c11_1, rc11_1. cbn [Z.of_N].
  gl (bval (b10 c10_1 c10_2 c10_3 c10_4 c10_5 c10_6 c10_7 c10_8)).
Qed.
Definition lb11_1 : N := Eval vm_compute in ((2 * lbe10) / 3)%N.
Lemma c11_1_lb : (Z.of_N lb11_1 <= Z.of_nat c11_1)%Z.
Proof.
  pose proof (T10_lb c10_1 c10_2 c10_3 c10_4 c10_5 c10_6 c10_7 c10_8) as H. unfold lbe10 in H. unfold c11_1, lb11_1.
  cbn [Z.of_N] in *. gl (bval (b10 c10_1 c10_2 c10_3 c10_4 c10_5 c10_6 c10_7 c10_8)).
Qed.
Definition rb11_1 : N := Eval vm_compute in Z.to_N (((2 * Z.of_N t2_10 - 1) * 11) mod 32).
Lemma c11_1_res2 : (Z.of_nat c11_1 mod Z.of_N 32 = Z.of_N rb11_1)%Z.
Proof.
  pose proof T10_res as H. unfold vT10 in H.
  pose proof (T10_low c10_1 c10_2 c10_3 c10_4 c10_5 c10_6 c10_7 c10_8) as H2. unfold t2_10 in H2.
  unfold c11_1, rb11_1. cbn [Z.of_N] in *. gl (bval (b10 c10_1 c10_2 c10_3 c10_4 c10_5 c10_6 c10_7 c10_8)).
Qed.

Definition rc11_2 : N := Eval vm_compute in
  Z.to_N (((((Z.of_N rc10_1 - (Z.of_nat cc10_1 + 1 + Z.of_nat jj10_1)) * 1) mod 81) / 3) mod 27).
Definition lb11_2 : N := Eval vm_compute in (((lb10_1 - (N.of_nat cc10_1 + 1 + N.of_nat jj10_1)) / 1) / 3)%N.
Definition rb11_2 : N := Eval vm_compute in
  Z.to_N (((((Z.of_N rb10_1 - (Z.of_nat cc10_1 + 1 + Z.of_nat jj10_1)) mod 32) / 1 - 2) * 11) mod 32).
Lemma c11_2_res : (Z.of_nat c11_2 mod Z.of_N 27 = Z.of_N rc11_2)%Z.
Proof.
  pose proof c10_1_res as H. pose proof c10_1_res2 as H2. pose proof c10_1_lb as Hb.
  unfold rc10_1 in H. unfold rb10_1 in H2. unfold lb10_1 in Hb.
  unfold c11_2, rc11_2, cc10_1, kq10_1, jj10_1. cbn [Z.of_N] in *. gl c10_1.
Qed.
Lemma c11_2_res2 : (Z.of_nat c11_2 mod Z.of_N 32 = Z.of_N rb11_2)%Z.
Proof.
  pose proof c10_1_res as H. pose proof c10_1_res2 as H2. pose proof c10_1_lb as Hb.
  unfold rc10_1 in H. unfold rb10_1 in H2. unfold lb10_1 in Hb.
  unfold c11_2, rb11_2, cc10_1, kq10_1, jj10_1. cbn [Z.of_N] in *. gl c10_1.
Qed.
Lemma c11_2_lb : (Z.of_N lb11_2 <= Z.of_nat c11_2)%Z.
Proof.
  pose proof c10_1_res as H. pose proof c10_1_res2 as H2. pose proof c10_1_lb as Hb.
  unfold rc10_1 in H. unfold rb10_1 in H2. unfold lb10_1 in Hb.
  unfold c11_2, lb11_2, cc10_1, kq10_1, jj10_1. cbn [Z.of_N] in *. gl c10_1.
Qed.

Definition rc11_3 : N := Eval vm_compute in
  Z.to_N (((((Z.of_N rc10_2 - (Z.of_nat cc10_2 + 1 + Z.of_nat jj10_2)) * 1) mod 81) / 3) mod 27).
Definition lb11_3 : N := Eval vm_compute in (((lb10_2 - (N.of_nat cc10_2 + 1 + N.of_nat jj10_2)) / 1) / 3)%N.
Definition rb11_3 : N := Eval vm_compute in
  Z.to_N (((((Z.of_N rb10_2 - (Z.of_nat cc10_2 + 1 + Z.of_nat jj10_2)) mod 32) / 1 - 0) * 11) mod 32).
Lemma c11_3_res : (Z.of_nat c11_3 mod Z.of_N 27 = Z.of_N rc11_3)%Z.
Proof.
  pose proof c10_2_res as H. pose proof c10_2_res2 as H2. pose proof c10_2_lb as Hb.
  unfold rc10_2 in H. unfold rb10_2 in H2. unfold lb10_2 in Hb.
  unfold c11_3, rc11_3, cc10_2, kq10_2, jj10_2. cbn [Z.of_N] in *. gl c10_2.
Qed.
Lemma c11_3_res2 : (Z.of_nat c11_3 mod Z.of_N 32 = Z.of_N rb11_3)%Z.
Proof.
  pose proof c10_2_res as H. pose proof c10_2_res2 as H2. pose proof c10_2_lb as Hb.
  unfold rc10_2 in H. unfold rb10_2 in H2. unfold lb10_2 in Hb.
  unfold c11_3, rb11_3, cc10_2, kq10_2, jj10_2. cbn [Z.of_N] in *. gl c10_2.
Qed.
Lemma c11_3_lb : (Z.of_N lb11_3 <= Z.of_nat c11_3)%Z.
Proof.
  pose proof c10_2_res as H. pose proof c10_2_res2 as H2. pose proof c10_2_lb as Hb.
  unfold rc10_2 in H. unfold rb10_2 in H2. unfold lb10_2 in Hb.
  unfold c11_3, lb11_3, cc10_2, kq10_2, jj10_2. cbn [Z.of_N] in *. gl c10_2.
Qed.

Definition rc11_4 : N := Eval vm_compute in
  Z.to_N (((((Z.of_N rc10_3 - (Z.of_nat cc10_3 + 1 + Z.of_nat jj10_3)) * 1) mod 81) / 3) mod 27).
Definition lb11_4 : N := Eval vm_compute in (((lb10_3 - (N.of_nat cc10_3 + 1 + N.of_nat jj10_3)) / 1) / 3)%N.
Definition rb11_4 : N := Eval vm_compute in
  Z.to_N (((((Z.of_N rb10_3 - (Z.of_nat cc10_3 + 1 + Z.of_nat jj10_3)) mod 32) / 1 - 1) * 11) mod 32).
Lemma c11_4_res : (Z.of_nat c11_4 mod Z.of_N 27 = Z.of_N rc11_4)%Z.
Proof.
  pose proof c10_3_res as H. pose proof c10_3_res2 as H2. pose proof c10_3_lb as Hb.
  unfold rc10_3 in H. unfold rb10_3 in H2. unfold lb10_3 in Hb.
  unfold c11_4, rc11_4, cc10_3, kq10_3, jj10_3. cbn [Z.of_N] in *. gl c10_3.
Qed.
Lemma c11_4_res2 : (Z.of_nat c11_4 mod Z.of_N 32 = Z.of_N rb11_4)%Z.
Proof.
  pose proof c10_3_res as H. pose proof c10_3_res2 as H2. pose proof c10_3_lb as Hb.
  unfold rc10_3 in H. unfold rb10_3 in H2. unfold lb10_3 in Hb.
  unfold c11_4, rb11_4, cc10_3, kq10_3, jj10_3. cbn [Z.of_N] in *. gl c10_3.
Qed.
Lemma c11_4_lb : (Z.of_N lb11_4 <= Z.of_nat c11_4)%Z.
Proof.
  pose proof c10_3_res as H. pose proof c10_3_res2 as H2. pose proof c10_3_lb as Hb.
  unfold rc10_3 in H. unfold rb10_3 in H2. unfold lb10_3 in Hb.
  unfold c11_4, lb11_4, cc10_3, kq10_3, jj10_3. cbn [Z.of_N] in *. gl c10_3.
Qed.

Definition rc11_5 : N := Eval vm_compute in
  Z.to_N (((((Z.of_N rc10_4 - (Z.of_nat cc10_4 + 1 + Z.of_nat jj10_4)) * 1) mod 81) / 3) mod 27).
Definition lb11_5 : N := Eval vm_compute in (((lb10_4 - (N.of_nat cc10_4 + 1 + N.of_nat jj10_4)) / 1) / 3)%N.
Definition rb11_5 : N := Eval vm_compute in
  Z.to_N (((((Z.of_N rb10_4 - (Z.of_nat cc10_4 + 1 + Z.of_nat jj10_4)) mod 16) / 1 - 0) * 11) mod 16).
Lemma c11_5_res : (Z.of_nat c11_5 mod Z.of_N 27 = Z.of_N rc11_5)%Z.
Proof.
  pose proof c10_4_res as H. pose proof c10_4_res2 as H2. pose proof c10_4_lb as Hb.
  unfold rc10_4 in H. unfold rb10_4 in H2. unfold lb10_4 in Hb.
  unfold c11_5, rc11_5, cc10_4, kq10_4, jj10_4. cbn [Z.of_N] in *. gl c10_4.
Qed.
Lemma c11_5_res2 : (Z.of_nat c11_5 mod Z.of_N 16 = Z.of_N rb11_5)%Z.
Proof.
  pose proof c10_4_res as H. pose proof c10_4_res2 as H2. pose proof c10_4_lb as Hb.
  unfold rc10_4 in H. unfold rb10_4 in H2. unfold lb10_4 in Hb.
  unfold c11_5, rb11_5, cc10_4, kq10_4, jj10_4. cbn [Z.of_N] in *. gl c10_4.
Qed.
Lemma c11_5_lb : (Z.of_N lb11_5 <= Z.of_nat c11_5)%Z.
Proof.
  pose proof c10_4_res as H. pose proof c10_4_res2 as H2. pose proof c10_4_lb as Hb.
  unfold rc10_4 in H. unfold rb10_4 in H2. unfold lb10_4 in Hb.
  unfold c11_5, lb11_5, cc10_4, kq10_4, jj10_4. cbn [Z.of_N] in *. gl c10_4.
Qed.

Definition rc11_6 : N := Eval vm_compute in
  Z.to_N (((((Z.of_N rc10_5 - (Z.of_nat cc10_5 + 1 + Z.of_nat jj10_5)) * 1) mod 81) / 3) mod 27).
Definition lb11_6 : N := Eval vm_compute in (((lb10_5 - (N.of_nat cc10_5 + 1 + N.of_nat jj10_5)) / 1) / 3)%N.
Definition rb11_6 : N := Eval vm_compute in
  Z.to_N (((((Z.of_N rb10_5 - (Z.of_nat cc10_5 + 1 + Z.of_nat jj10_5)) mod 32) / 1 - 0) * 11) mod 32).
Lemma c11_6_res : (Z.of_nat c11_6 mod Z.of_N 27 = Z.of_N rc11_6)%Z.
Proof.
  pose proof c10_5_res as H. pose proof c10_5_res2 as H2. pose proof c10_5_lb as Hb.
  unfold rc10_5 in H. unfold rb10_5 in H2. unfold lb10_5 in Hb.
  unfold c11_6, rc11_6, cc10_5, kq10_5, jj10_5. cbn [Z.of_N] in *. gl c10_5.
Qed.
Lemma c11_6_res2 : (Z.of_nat c11_6 mod Z.of_N 32 = Z.of_N rb11_6)%Z.
Proof.
  pose proof c10_5_res as H. pose proof c10_5_res2 as H2. pose proof c10_5_lb as Hb.
  unfold rc10_5 in H. unfold rb10_5 in H2. unfold lb10_5 in Hb.
  unfold c11_6, rb11_6, cc10_5, kq10_5, jj10_5. cbn [Z.of_N] in *. gl c10_5.
Qed.
Lemma c11_6_lb : (Z.of_N lb11_6 <= Z.of_nat c11_6)%Z.
Proof.
  pose proof c10_5_res as H. pose proof c10_5_res2 as H2. pose proof c10_5_lb as Hb.
  unfold rc10_5 in H. unfold rb10_5 in H2. unfold lb10_5 in Hb.
  unfold c11_6, lb11_6, cc10_5, kq10_5, jj10_5. cbn [Z.of_N] in *. gl c10_5.
Qed.

Definition rc11_7 : N := Eval vm_compute in
  Z.to_N (((((Z.of_N rc10_6 - (Z.of_nat cc10_6 + 1 + Z.of_nat jj10_6)) * 1) mod 81) / 3) mod 27).
Definition lb11_7 : N := Eval vm_compute in (((lb10_6 - (N.of_nat cc10_6 + 1 + N.of_nat jj10_6)) / 1) / 3)%N.
Definition rb11_7 : N := Eval vm_compute in
  Z.to_N (((((Z.of_N rb10_6 - (Z.of_nat cc10_6 + 1 + Z.of_nat jj10_6)) mod 32) / 1 - 0) * 11) mod 32).
Lemma c11_7_res : (Z.of_nat c11_7 mod Z.of_N 27 = Z.of_N rc11_7)%Z.
Proof.
  pose proof c10_6_res as H. pose proof c10_6_res2 as H2. pose proof c10_6_lb as Hb.
  unfold rc10_6 in H. unfold rb10_6 in H2. unfold lb10_6 in Hb.
  unfold c11_7, rc11_7, cc10_6, kq10_6, jj10_6. cbn [Z.of_N] in *. gl c10_6.
Qed.
Lemma c11_7_res2 : (Z.of_nat c11_7 mod Z.of_N 32 = Z.of_N rb11_7)%Z.
Proof.
  pose proof c10_6_res as H. pose proof c10_6_res2 as H2. pose proof c10_6_lb as Hb.
  unfold rc10_6 in H. unfold rb10_6 in H2. unfold lb10_6 in Hb.
  unfold c11_7, rb11_7, cc10_6, kq10_6, jj10_6. cbn [Z.of_N] in *. gl c10_6.
Qed.
Lemma c11_7_lb : (Z.of_N lb11_7 <= Z.of_nat c11_7)%Z.
Proof.
  pose proof c10_6_res as H. pose proof c10_6_res2 as H2. pose proof c10_6_lb as Hb.
  unfold rc10_6 in H. unfold rb10_6 in H2. unfold lb10_6 in Hb.
  unfold c11_7, lb11_7, cc10_6, kq10_6, jj10_6. cbn [Z.of_N] in *. gl c10_6.
Qed.

Definition rc11_8 : N := Eval vm_compute in
  Z.to_N (((((Z.of_N rc10_7 - (Z.of_nat cc10_7 + 1 + Z.of_nat jj10_7)) * 1) mod 81) / 3) mod 27).
Definition lb11_8 : N := Eval vm_compute in (((lb10_7 - (N.of_nat cc10_7 + 1 + N.of_nat jj10_7)) / 1) / 3)%N.
Definition rb11_8 : N := Eval vm_compute in
  Z.to_N (((((Z.of_N rb10_7 - (Z.of_nat cc10_7 + 1 + Z.of_nat jj10_7)) mod 32) / 1 - 2) * 11) mod 32).
Lemma c11_8_res : (Z.of_nat c11_8 mod Z.of_N 27 = Z.of_N rc11_8)%Z.
Proof.
  pose proof c10_7_res as H. pose proof c10_7_res2 as H2. pose proof c10_7_lb as Hb.
  unfold rc10_7 in H. unfold rb10_7 in H2. unfold lb10_7 in Hb.
  unfold c11_8, rc11_8, cc10_7, kq10_7, jj10_7. cbn [Z.of_N] in *. gl c10_7.
Qed.
Lemma c11_8_res2 : (Z.of_nat c11_8 mod Z.of_N 32 = Z.of_N rb11_8)%Z.
Proof.
  pose proof c10_7_res as H. pose proof c10_7_res2 as H2. pose proof c10_7_lb as Hb.
  unfold rc10_7 in H. unfold rb10_7 in H2. unfold lb10_7 in Hb.
  unfold c11_8, rb11_8, cc10_7, kq10_7, jj10_7. cbn [Z.of_N] in *. gl c10_7.
Qed.
Lemma c11_8_lb : (Z.of_N lb11_8 <= Z.of_nat c11_8)%Z.
Proof.
  pose proof c10_7_res as H. pose proof c10_7_res2 as H2. pose proof c10_7_lb as Hb.
  unfold rc10_7 in H. unfold rb10_7 in H2. unfold lb10_7 in Hb.
  unfold c11_8, lb11_8, cc10_7, kq10_7, jj10_7. cbn [Z.of_N] in *. gl c10_7.
Qed.

Definition rc11_9 : N := Eval vm_compute in
  Z.to_N (((((Z.of_N rc10_8 - (Z.of_nat cc10_8 + 1 + Z.of_nat jj10_8)) * 1) mod 81) / 3) mod 27).
Definition lb11_9 : N := Eval vm_compute in (((lb10_8 - (N.of_nat cc10_8 + 1 + N.of_nat jj10_8)) / 1) / 3)%N.
Definition rb11_9 : N := Eval vm_compute in
  Z.to_N (((((Z.of_N rb10_8 - (Z.of_nat cc10_8 + 1 + Z.of_nat jj10_8)) mod 32) / 1 - 1) * 11) mod 32).
Lemma c11_9_res : (Z.of_nat c11_9 mod Z.of_N 27 = Z.of_N rc11_9)%Z.
Proof.
  pose proof c10_8_res as H. pose proof c10_8_res2 as H2. pose proof c10_8_lb as Hb.
  unfold rc10_8 in H. unfold rb10_8 in H2. unfold lb10_8 in Hb.
  unfold c11_9, rc11_9, cc10_8, kq10_8, jj10_8. cbn [Z.of_N] in *. gl c10_8.
Qed.
Lemma c11_9_res2 : (Z.of_nat c11_9 mod Z.of_N 32 = Z.of_N rb11_9)%Z.
Proof.
  pose proof c10_8_res as H. pose proof c10_8_res2 as H2. pose proof c10_8_lb as Hb.
  unfold rc10_8 in H. unfold rb10_8 in H2. unfold lb10_8 in Hb.
  unfold c11_9, rb11_9, cc10_8, kq10_8, jj10_8. cbn [Z.of_N] in *. gl c10_8.
Qed.
Lemma c11_9_lb : (Z.of_N lb11_9 <= Z.of_nat c11_9)%Z.
Proof.
  pose proof c10_8_res as H. pose proof c10_8_res2 as H2. pose proof c10_8_lb as Hb.
  unfold rc10_8 in H. unfold rb10_8 in H2. unfold lb10_8 in Hb.
  unfold c11_9, lb11_9, cc10_8, kq10_8, jj10_8. cbn [Z.of_N] in *. gl c10_8.
Qed.

(** ** The word of level 11 modulo 3^3 *)

Definition vT11 : Z := Eval vm_compute in
  gv (resW 27 [RL a11_0; RR P11_1 27 rc11_1; RL a11_1; RR P11_2 27 rc11_2; RL a11_2; RR P11_3 27
    rc11_3; RL a11_3; RR P11_4 27 rc11_4; RL a11_4; RR P11_5 27 rc11_5; RL a11_5; RR P11_6 27
    rc11_6; RL a11_6; RR P11_7 27 rc11_7; RL a11_7; RR P11_8 27 rc11_8; RL a11_8; RR P11_9 27
    rc11_9; RL a11_9]).

Lemma T11_res : (Z.of_nat (bval (b11 c11_1 c11_2 c11_3 c11_4 c11_5 c11_6 c11_7 c11_8 c11_9)) mod 27 = vT11)%Z.
Proof.
  unfold b11.
  apply (resW_sound 27 [Lit a11_0; Rep P11_1 c11_1; Lit a11_1; Rep P11_2 c11_2; Lit a11_2; Rep P11_3
    c11_3; Lit a11_3; Rep P11_4 c11_4; Lit a11_4; Rep P11_5 c11_5; Lit a11_5; Rep P11_6 c11_6; Lit
    a11_6; Rep P11_7 c11_7; Lit a11_7; Rep P11_8 c11_8; Lit a11_8; Rep P11_9 c11_9; Lit a11_9]
           [RL a11_0; RR P11_1 27 rc11_1; RL a11_1; RR P11_2 27 rc11_2; RL a11_2; RR P11_3 27 rc11_3; RL a11_3;
            RR P11_4 27 rc11_4; RL a11_4; RR P11_5 27 rc11_5; RL a11_5; RR P11_6 27 rc11_6; RL
            a11_6; RR P11_7 27 rc11_7; RL a11_7; RR P11_8 27 rc11_8; RL a11_8; RR P11_9 27 rc11_9;
            RL a11_9]);
    [lia | | vm_compute; reflexivity].
  exact (Forall2_cons _ _ (mL a11_0)
    (Forall2_cons _ _ (mR P11_1 c11_1 27%N rc11_1 c11_1_res)
    (Forall2_cons _ _ (mL a11_1)
    (Forall2_cons _ _ (mR P11_2 c11_2 27%N rc11_2 c11_2_res)
    (Forall2_cons _ _ (mL a11_2)
    (Forall2_cons _ _ (mR P11_3 c11_3 27%N rc11_3 c11_3_res)
    (Forall2_cons _ _ (mL a11_3)
    (Forall2_cons _ _ (mR P11_4 c11_4 27%N rc11_4 c11_4_res)
    (Forall2_cons _ _ (mL a11_4)
    (Forall2_cons _ _ (mR P11_5 c11_5 27%N rc11_5 c11_5_res)
    (Forall2_cons _ _ (mL a11_5)
    (Forall2_cons _ _ (mR P11_6 c11_6 27%N rc11_6 c11_6_res)
    (Forall2_cons _ _ (mL a11_6)
    (Forall2_cons _ _ (mR P11_7 c11_7 27%N rc11_7 c11_7_res)
    (Forall2_cons _ _ (mL a11_7)
    (Forall2_cons _ _ (mR P11_8 c11_8 27%N rc11_8 c11_8_res)
    (Forall2_cons _ _ (mL a11_8)
    (Forall2_cons _ _ (mR P11_9 c11_9 27%N rc11_9 c11_9_res)
    (Forall2_cons _ _ (mL a11_9) (Forall2_nil _)))))))))))))))))))).
Qed.

Definition lbe11 : N := Eval vm_compute in bvalN a11_9.

Lemma T11_lb : forall d1 d2 d3 d4 d5 d6 d7 d8 d9, (Z.of_N lbe11 <= Z.of_nat (bval (b11 d1 d2 d3 d4 d5 d6 d7 d8 d9)))%Z.
Proof.
  intros d1 d2 d3 d4 d5 d6 d7 d8 d9. unfold b11. change lbe11 with (bvalN a11_9).
  exact (lbZ [Lit a11_0; Rep P11_1 d1; Lit a11_1; Rep P11_2 d2; Lit a11_2; Rep P11_3 d3; Lit a11_3;
    Rep P11_4 d4; Lit a11_4; Rep P11_5 d5; Lit a11_5; Rep P11_6 d6; Lit a11_6; Rep P11_7 d7; Lit
    a11_7; Rep P11_8 d8; Lit a11_8; Rep P11_9 d9] a11_9).
Qed.

Definition t2_11 : N := Eval vm_compute in bvalN a11_0.

Lemma T11_low : forall d1 d2 d3 d4 d5 d6 d7 d8 d9, (Z.of_nat (bval (b11 d1 d2 d3 d4 d5 d6 d7 d8 d9)) mod 16 = Z.of_N t2_11)%Z.
Proof.
  intros d1 d2 d3 d4 d5 d6 d7 d8 d9. unfold b11.
  exact (bval_low_den a11_0 [Rep P11_1 d1; Lit a11_1; Rep P11_2 d2; Lit a11_2; Rep P11_3 d3; Lit
    a11_3; Rep P11_4 d4; Lit a11_4; Rep P11_5 d5; Lit a11_5; Rep P11_6 d6; Lit a11_6; Rep P11_7 d7;
    Lit a11_7; Rep P11_8 d8; Lit a11_8; Rep P11_9 d9; Lit a11_9]).
Qed.

End L1011b.

Module L1112a.

(** * 1RB1LB_1RC0RD_0LA1RE_0RF1LC_1LA0RB_---1LC: the end phase of level 11

    Level 11 has class 5 and a counter word with 9 repeated blocks.  The end phase is
    certified round by round ([crun_run]): a run to the first block, then for each block a
    cycle per copy and a run across the next junction, and a closing computation.  The cuts
    are computed from the rounds of one instance.  Generated by a script. *)

Import Individual62.
Import T694_levels End694 Sym694 Lev694 Lvl1_694 Eng694 Cert694 Run694 Res694 Gen694.
Import L23 L34 L45 L56 L6i L67a L67b L78a L78b L89a L89b L910a L910b L1011a L1011b.
Import Lia Arith PeanoNat Bool NArith ZArith.
Import Coq.Lists.List.
Import ListNotations.

(** ** The cells of the counter word *)

Definition pa11_0 : bool := Eval vm_compute in par false a11_0.
Lemma pa11_0_eq : par false a11_0 = pa11_0.
Proof. vm_compute. reflexivity. Qed.
Definition pa11_1 : bool := Eval vm_compute in par pa11_0 a11_1.
Lemma pa11_1_eq : par pa11_0 a11_1 = pa11_1.
Proof. vm_compute. reflexivity. Qed.
Definition pa11_2 : bool := Eval vm_compute in par pa11_1 a11_2.
Lemma pa11_2_eq : par pa11_1 a11_2 = pa11_2.
Proof. vm_compute. reflexivity. Qed.
Definition pa11_3 : bool := Eval vm_compute in par pa11_2 a11_3.
Lemma pa11_3_eq : par pa11_2 a11_3 = pa11_3.
Proof. vm_compute. reflexivity. Qed.
Definition pa11_4 : bool := Eval vm_compute in par pa11_3 a11_4.
Lemma pa11_4_eq : par pa11_3 a11_4 = pa11_4.
Proof. vm_compute. reflexivity. Qed.
Definition pa11_5 : bool := Eval vm_compute in par pa11_4 a11_5.
Lemma pa11_5_eq : par pa11_4 a11_5 = pa11_5.
Proof. vm_compute. reflexivity. Qed.
Definition pa11_6 : bool := Eval vm_compute in par pa11_5 a11_6.
Lemma pa11_6_eq : par pa11_5 a11_6 = pa11_6.
Proof. vm_compute. reflexivity. Qed.
Definition pa11_7 : bool := Eval vm_compute in par pa11_6 a11_7.
Lemma pa11_7_eq : par pa11_6 a11_7 = pa11_7.
Proof. vm_compute. reflexivity. Qed.
Definition pa11_8 : bool := Eval vm_compute in par pa11_7 a11_8.
Lemma pa11_8_eq : par pa11_7 a11_8 = pa11_8.
Proof. vm_compute. reflexivity. Qed.
Lemma pp11_1 : par pa11_0 P11_1 = pa11_0.
Proof. vm_compute. reflexivity. Qed.
Lemma pp11_2 : par pa11_1 P11_2 = pa11_1.
Proof. vm_compute. reflexivity. Qed.
Lemma pp11_3 : par pa11_2 P11_3 = pa11_2.
Proof. vm_compute. reflexivity. Qed.
Lemma pp11_4 : par pa11_3 P11_4 = pa11_3.
Proof. vm_compute. reflexivity. Qed.
Lemma pp11_5 : par pa11_4 P11_5 = pa11_4.
Proof. vm_compute. reflexivity. Qed.
Lemma pp11_6 : par pa11_5 P11_6 = pa11_5.
Proof. vm_compute. reflexivity. Qed.
Lemma pp11_7 : par pa11_6 P11_7 = pa11_6.
Proof. vm_compute. reflexivity. Qed.
Lemma pp11_8 : par pa11_7 P11_8 = pa11_7.
Proof. vm_compute. reflexivity. Qed.
Lemma pp11_9 : par pa11_8 P11_9 = pa11_8.
Proof. vm_compute. reflexivity. Qed.

Definition Hd11 : list bool := rep10 je11 ++ c1101 ++ encb false a11_0.
Definition E11_1 : list bool := encb pa11_0 P11_1.
Definition J11_1 : list bool := encb pa11_0 a11_1.
Definition E11_2 : list bool := encb pa11_1 P11_2.
Definition J11_2 : list bool := encb pa11_1 a11_2.
Definition E11_3 : list bool := encb pa11_2 P11_3.
Definition J11_3 : list bool := encb pa11_2 a11_3.
Definition E11_4 : list bool := encb pa11_3 P11_4.
Definition J11_4 : list bool := encb pa11_3 a11_4.
Definition E11_5 : list bool := encb pa11_4 P11_5.
Definition J11_5 : list bool := encb pa11_4 a11_5.
Definition E11_6 : list bool := encb pa11_5 P11_6.
Definition J11_6 : list bool := encb pa11_5 a11_6.
Definition E11_7 : list bool := encb pa11_6 P11_7.
Definition J11_7 : list bool := encb pa11_6 a11_7.
Definition E11_8 : list bool := encb pa11_7 P11_8.
Definition J11_8 : list bool := encb pa11_7 a11_8.
Definition E11_9 : list bool := encb pa11_8 P11_9.
Definition J11_9 : list bool := encb pa11_8 a11_9.

Definition cells11 (c1 c2 c3 c4 c5 c6 c7 c8 c9 : nat) : list bool :=
  rep10 je11 ++ c1101 ++ encb false (b11 c1 c2 c3 c4 c5 c6 c7 c8 c9) ++ w11.

Lemma cells11_eq : forall c1 c2 c3 c4 c5 c6 c7 c8 c9,
  cells11 c1 c2 c3 c4 c5 c6 c7 c8 c9 = Hd11 ++ rp E11_1 c1 ++ J11_1 ++ rp E11_2 c2 ++ J11_2 ++ rp
    E11_3 c3 ++ J11_3 ++ rp E11_4 c4 ++ J11_4 ++ rp E11_5 c5 ++ J11_5 ++ rp E11_6 c6 ++ J11_6 ++ rp
    E11_7 c7 ++ J11_7 ++ rp E11_8 c8 ++ J11_8 ++ rp E11_9 c9 ++ J11_9 ++ w11.
Proof.
  intros c1 c2 c3 c4 c5 c6 c7 c8 c9. unfold cells11, b11, Hd11, E11_1, J11_1, E11_2, J11_2, E11_3, J11_3, E11_4, J11_4, E11_5, J11_5, E11_6, J11_6, E11_7, J11_7, E11_8, J11_8, E11_9, J11_9.
  cbn [den bden]. rewrite app_nil_r.
  rewrite (encb_app a11_0), pa11_0_eq.
  rewrite (encb_rp P11_1 pa11_0 pp11_1), (encb_app a11_1), pa11_1_eq.
  rewrite (encb_rp P11_2 pa11_1 pp11_2), (encb_app a11_2), pa11_2_eq.
  rewrite (encb_rp P11_3 pa11_2 pp11_3), (encb_app a11_3), pa11_3_eq.
  rewrite (encb_rp P11_4 pa11_3 pp11_4), (encb_app a11_4), pa11_4_eq.
  rewrite (encb_rp P11_5 pa11_4 pp11_5), (encb_app a11_5), pa11_5_eq.
  rewrite (encb_rp P11_6 pa11_5 pp11_6), (encb_app a11_6), pa11_6_eq.
  rewrite (encb_rp P11_7 pa11_6 pp11_7), (encb_app a11_7), pa11_7_eq.
  rewrite (encb_rp P11_8 pa11_7 pp11_8), (encb_app a11_8), pa11_8_eq.
  rewrite (encb_rp P11_9 pa11_8 pp11_9).
  rewrite <- ?app_assoc. reflexivity.
Qed.

(** ** Boundaries, computed from the rounds of one instance *)

Definition look11_1 : nat := 36.
Definition dep11_1 : nat := 1.
Definition p11_1 : nat := Eval vm_compute in length E11_1.
Definition N11_1 : nat := Eval vm_compute in
  let b0 := (look11_1 / p11_1 + dep11_1 + 14)%nat in
  (b0 + N.to_nat ((rb11_1 + 4 * 1024 - N.of_nat b0) mod 4)%N)%nat.
Definition look11_2 : nat := 36.
Definition dep11_2 : nat := 1.
Definition p11_2 : nat := Eval vm_compute in length E11_2.
Definition N11_2 : nat := Eval vm_compute in
  let b0 := (look11_2 / p11_2 + dep11_2 + 14)%nat in
  (b0 + N.to_nat ((rb11_2 + 4 * 1024 - N.of_nat b0) mod 4)%N)%nat.
Definition look11_3 : nat := 36.
Definition dep11_3 : nat := 1.
Definition p11_3 : nat := Eval vm_compute in length E11_3.
Definition N11_3 : nat := Eval vm_compute in
  let b0 := (look11_3 / p11_3 + dep11_3 + 14)%nat in
  (b0 + N.to_nat ((rb11_3 + 4 * 1024 - N.of_nat b0) mod 4)%N)%nat.
Definition look11_4 : nat := 36.
Definition dep11_4 : nat := 1.
Definition p11_4 : nat := Eval vm_compute in length E11_4.
Definition N11_4 : nat := Eval vm_compute in
  let b0 := (look11_4 / p11_4 + dep11_4 + 14)%nat in
  (b0 + N.to_nat ((rb11_4 + 4 * 1024 - N.of_nat b0) mod 4)%N)%nat.
Definition look11_5 : nat := 36.
Definition dep11_5 : nat := 1.
Definition p11_5 : nat := Eval vm_compute in length E11_5.
Definition N11_5 : nat := Eval vm_compute in
  let b0 := (look11_5 / p11_5 + dep11_5 + 14)%nat in
  (b0 + N.to_nat ((rb11_5 + 4 * 1024 - N.of_nat b0) mod 4)%N)%nat.
Definition look11_6 : nat := 36.
Definition dep11_6 : nat := 1.
Definition p11_6 : nat := Eval vm_compute in length E11_6.
Definition N11_6 : nat := Eval vm_compute in
  let b0 := (look11_6 / p11_6 + dep11_6 + 14)%nat in
  (b0 + N.to_nat ((rb11_6 + 4 * 1024 - N.of_nat b0) mod 4)%N)%nat.
Definition look11_7 : nat := 36.
Definition dep11_7 : nat := 1.
Definition p11_7 : nat := Eval vm_compute in length E11_7.
Definition N11_7 : nat := Eval vm_compute in
  let b0 := (look11_7 / p11_7 + dep11_7 + 14)%nat in
  (b0 + N.to_nat ((rb11_7 + 4 * 1024 - N.of_nat b0) mod 4)%N)%nat.
Definition look11_8 : nat := 36.
Definition dep11_8 : nat := 1.
Definition p11_8 : nat := Eval vm_compute in length E11_8.
Definition N11_8 : nat := Eval vm_compute in
  let b0 := (look11_8 / p11_8 + dep11_8 + 14)%nat in
  (b0 + N.to_nat ((rb11_8 + 4 * 1024 - N.of_nat b0) mod 4)%N)%nat.
Definition look11_9 : nat := 36.
Definition dep11_9 : nat := 1.
Definition p11_9 : nat := Eval vm_compute in length E11_9.
Definition N11_9 : nat := Eval vm_compute in
  let b0 := (look11_9 / p11_9 + dep11_9 + 14)%nat in
  (b0 + N.to_nat ((rb11_9 + 4 * 1024 - N.of_nat b0) mod 4)%N)%nat.
Definition looke11 : nat := 36.
Definition inst11 : list bool := cells11 N11_1 N11_2 N11_3 N11_4 N11_5 N11_6 N11_7 N11_8 N11_9.
Definition s11_1 : N := Eval vm_compute in N.of_nat (length Hd11).
Definition s11_2 : N := Eval vm_compute in
  (s11_1 + N.of_nat (N11_1 * p11_1 + length J11_1))%N.
Definition s11_3 : N := Eval vm_compute in
  (s11_2 + N.of_nat (N11_2 * p11_2 + length J11_2))%N.
Definition s11_4 : N := Eval vm_compute in
  (s11_3 + N.of_nat (N11_3 * p11_3 + length J11_3))%N.
Definition s11_5 : N := Eval vm_compute in
  (s11_4 + N.of_nat (N11_4 * p11_4 + length J11_4))%N.
Definition s11_6 : N := Eval vm_compute in
  (s11_5 + N.of_nat (N11_5 * p11_5 + length J11_5))%N.
Definition s11_7 : N := Eval vm_compute in
  (s11_6 + N.of_nat (N11_6 * p11_6 + length J11_6))%N.
Definition s11_8 : N := Eval vm_compute in
  (s11_7 + N.of_nat (N11_7 * p11_7 + length J11_7))%N.
Definition s11_9 : N := Eval vm_compute in
  (s11_8 + N.of_nat (N11_8 * p11_8 + length J11_8))%N.
Definition s11_10 : N := Eval vm_compute in
  (s11_9 + N.of_nat (N11_9 * p11_9 + length J11_9))%N.
Definition tr11 : list (N * N * N) := Eval vm_compute in
  gtrace 36 (length inst11) 0 0 0 (c1101, true, inst11).
Definition f11_1 : N * N * N * N := Eval vm_compute in
  gfindk (N.of_nat p11_1) (s11_1 + N.of_nat (dep11_1 * p11_1))
         (s11_1 + N.of_nat (N11_1 * p11_1) - N.of_nat look11_1) (1%N :: 2%N :: 4%N :: nil) tr11.
Definition rr11_1 : nat := Eval vm_compute in N.to_nat (fst (fst (fst f11_1))).
Definition R11_1 : nat := Eval vm_compute in N.to_nat (snd (fst f11_1)).
Definition kq11_1 : nat := Eval vm_compute in N.to_nat (snd f11_1).
Definition cc11_1 : nat := Eval vm_compute in N.to_nat ((snd (fst (fst f11_1)) + N.of_nat look11_1 - s11_1) / N.of_nat p11_1).
Definition uu11_1 : nat := Eval vm_compute in N.to_nat ((snd (fst (fst f11_1)) + N.of_nat look11_1 - s11_1) mod N.of_nat p11_1).
Definition jj11_1 : nat := Eval vm_compute in (N11_1 - cc11_1 - 1) mod kq11_1.
Definition S11_1 : sst := Eval vm_compute in
  gcut look11_1 (grst rr11_1 (c1101, true, inst11)).
Definition f11_2 : N * N * N * N := Eval vm_compute in
  gfindk (N.of_nat p11_2) (s11_2 + N.of_nat (dep11_2 * p11_2))
         (s11_2 + N.of_nat (N11_2 * p11_2) - N.of_nat look11_2) (1%N :: 2%N :: 4%N :: nil) tr11.
Definition rr11_2 : nat := Eval vm_compute in N.to_nat (fst (fst (fst f11_2))).
Definition R11_2 : nat := Eval vm_compute in N.to_nat (snd (fst f11_2)).
Definition kq11_2 : nat := Eval vm_compute in N.to_nat (snd f11_2).
Definition cc11_2 : nat := Eval vm_compute in N.to_nat ((snd (fst (fst f11_2)) + N.of_nat look11_2 - s11_2) / N.of_nat p11_2).
Definition uu11_2 : nat := Eval vm_compute in N.to_nat ((snd (fst (fst f11_2)) + N.of_nat look11_2 - s11_2) mod N.of_nat p11_2).
Definition jj11_2 : nat := Eval vm_compute in (N11_2 - cc11_2 - 1) mod kq11_2.
Definition S11_2 : sst := Eval vm_compute in
  gcut look11_2 (grst rr11_2 (c1101, true, inst11)).
Definition f11_3 : N * N * N * N := Eval vm_compute in
  gfindk (N.of_nat p11_3) (s11_3 + N.of_nat (dep11_3 * p11_3))
         (s11_3 + N.of_nat (N11_3 * p11_3) - N.of_nat look11_3) (1%N :: 2%N :: 4%N :: nil) tr11.
Definition rr11_3 : nat := Eval vm_compute in N.to_nat (fst (fst (fst f11_3))).
Definition R11_3 : nat := Eval vm_compute in N.to_nat (snd (fst f11_3)).
Definition kq11_3 : nat := Eval vm_compute in N.to_nat (snd f11_3).
Definition cc11_3 : nat := Eval vm_compute in N.to_nat ((snd (fst (fst f11_3)) + N.of_nat look11_3 - s11_3) / N.of_nat p11_3).
Definition uu11_3 : nat := Eval vm_compute in N.to_nat ((snd (fst (fst f11_3)) + N.of_nat look11_3 - s11_3) mod N.of_nat p11_3).
Definition jj11_3 : nat := Eval vm_compute in (N11_3 - cc11_3 - 1) mod kq11_3.
Definition S11_3 : sst := Eval vm_compute in
  gcut look11_3 (grst rr11_3 (c1101, true, inst11)).
Definition f11_4 : N * N * N * N := Eval vm_compute in
  gfindk (N.of_nat p11_4) (s11_4 + N.of_nat (dep11_4 * p11_4))
         (s11_4 + N.of_nat (N11_4 * p11_4) - N.of_nat look11_4) (1%N :: 2%N :: 4%N :: nil) tr11.
Definition rr11_4 : nat := Eval vm_compute in N.to_nat (fst (fst (fst f11_4))).
Definition R11_4 : nat := Eval vm_compute in N.to_nat (snd (fst f11_4)).
Definition kq11_4 : nat := Eval vm_compute in N.to_nat (snd f11_4).
Definition cc11_4 : nat := Eval vm_compute in N.to_nat ((snd (fst (fst f11_4)) + N.of_nat look11_4 - s11_4) / N.of_nat p11_4).
Definition uu11_4 : nat := Eval vm_compute in N.to_nat ((snd (fst (fst f11_4)) + N.of_nat look11_4 - s11_4) mod N.of_nat p11_4).
Definition jj11_4 : nat := Eval vm_compute in (N11_4 - cc11_4 - 1) mod kq11_4.
Definition S11_4 : sst := Eval vm_compute in
  gcut look11_4 (grst rr11_4 (c1101, true, inst11)).
Definition f11_5 : N * N * N * N := Eval vm_compute in
  gfindk (N.of_nat p11_5) (s11_5 + N.of_nat (dep11_5 * p11_5))
         (s11_5 + N.of_nat (N11_5 * p11_5) - N.of_nat look11_5) (1%N :: 2%N :: 4%N :: nil) tr11.
Definition rr11_5 : nat := Eval vm_compute in N.to_nat (fst (fst (fst f11_5))).
Definition R11_5 : nat := Eval vm_compute in N.to_nat (snd (fst f11_5)).
Definition kq11_5 : nat := Eval vm_compute in N.to_nat (snd f11_5).
Definition cc11_5 : nat := Eval vm_compute in N.to_nat ((snd (fst (fst f11_5)) + N.of_nat look11_5 - s11_5) / N.of_nat p11_5).
Definition uu11_5 : nat := Eval vm_compute in N.to_nat ((snd (fst (fst f11_5)) + N.of_nat look11_5 - s11_5) mod N.of_nat p11_5).
Definition jj11_5 : nat := Eval vm_compute in (N11_5 - cc11_5 - 1) mod kq11_5.
Definition S11_5 : sst := Eval vm_compute in
  gcut look11_5 (grst rr11_5 (c1101, true, inst11)).
Definition f11_6 : N * N * N * N := Eval vm_compute in
  gfindk (N.of_nat p11_6) (s11_6 + N.of_nat (dep11_6 * p11_6))
         (s11_6 + N.of_nat (N11_6 * p11_6) - N.of_nat look11_6) (1%N :: 2%N :: 4%N :: nil) tr11.
Definition rr11_6 : nat := Eval vm_compute in N.to_nat (fst (fst (fst f11_6))).
Definition R11_6 : nat := Eval vm_compute in N.to_nat (snd (fst f11_6)).
Definition kq11_6 : nat := Eval vm_compute in N.to_nat (snd f11_6).
Definition cc11_6 : nat := Eval vm_compute in N.to_nat ((snd (fst (fst f11_6)) + N.of_nat look11_6 - s11_6) / N.of_nat p11_6).
Definition uu11_6 : nat := Eval vm_compute in N.to_nat ((snd (fst (fst f11_6)) + N.of_nat look11_6 - s11_6) mod N.of_nat p11_6).
Definition jj11_6 : nat := Eval vm_compute in (N11_6 - cc11_6 - 1) mod kq11_6.
Definition S11_6 : sst := Eval vm_compute in
  gcut look11_6 (grst rr11_6 (c1101, true, inst11)).
Definition f11_7 : N * N * N * N := Eval vm_compute in
  gfindk (N.of_nat p11_7) (s11_7 + N.of_nat (dep11_7 * p11_7))
         (s11_7 + N.of_nat (N11_7 * p11_7) - N.of_nat look11_7) (1%N :: 2%N :: 4%N :: nil) tr11.
Definition rr11_7 : nat := Eval vm_compute in N.to_nat (fst (fst (fst f11_7))).
Definition R11_7 : nat := Eval vm_compute in N.to_nat (snd (fst f11_7)).
Definition kq11_7 : nat := Eval vm_compute in N.to_nat (snd f11_7).
Definition cc11_7 : nat := Eval vm_compute in N.to_nat ((snd (fst (fst f11_7)) + N.of_nat look11_7 - s11_7) / N.of_nat p11_7).
Definition uu11_7 : nat := Eval vm_compute in N.to_nat ((snd (fst (fst f11_7)) + N.of_nat look11_7 - s11_7) mod N.of_nat p11_7).
Definition jj11_7 : nat := Eval vm_compute in (N11_7 - cc11_7 - 1) mod kq11_7.
Definition S11_7 : sst := Eval vm_compute in
  gcut look11_7 (grst rr11_7 (c1101, true, inst11)).
Definition f11_8 : N * N * N * N := Eval vm_compute in
  gfindk (N.of_nat p11_8) (s11_8 + N.of_nat (dep11_8 * p11_8))
         (s11_8 + N.of_nat (N11_8 * p11_8) - N.of_nat look11_8) (1%N :: 2%N :: 4%N :: nil) tr11.
Definition rr11_8 : nat := Eval vm_compute in N.to_nat (fst (fst (fst f11_8))).
Definition R11_8 : nat := Eval vm_compute in N.to_nat (snd (fst f11_8)).
Definition kq11_8 : nat := Eval vm_compute in N.to_nat (snd f11_8).
Definition cc11_8 : nat := Eval vm_compute in N.to_nat ((snd (fst (fst f11_8)) + N.of_nat look11_8 - s11_8) / N.of_nat p11_8).
Definition uu11_8 : nat := Eval vm_compute in N.to_nat ((snd (fst (fst f11_8)) + N.of_nat look11_8 - s11_8) mod N.of_nat p11_8).
Definition jj11_8 : nat := Eval vm_compute in (N11_8 - cc11_8 - 1) mod kq11_8.
Definition S11_8 : sst := Eval vm_compute in
  gcut look11_8 (grst rr11_8 (c1101, true, inst11)).
Definition f11_9 : N * N * N * N := Eval vm_compute in
  gfindk (N.of_nat p11_9) (s11_9 + N.of_nat (dep11_9 * p11_9))
         (s11_9 + N.of_nat (N11_9 * p11_9) - N.of_nat look11_9) (1%N :: 2%N :: 4%N :: nil) tr11.
Definition rr11_9 : nat := Eval vm_compute in N.to_nat (fst (fst (fst f11_9))).
Definition R11_9 : nat := Eval vm_compute in N.to_nat (snd (fst f11_9)).
Definition kq11_9 : nat := Eval vm_compute in N.to_nat (snd f11_9).
Definition cc11_9 : nat := Eval vm_compute in N.to_nat ((snd (fst (fst f11_9)) + N.of_nat look11_9 - s11_9) / N.of_nat p11_9).
Definition uu11_9 : nat := Eval vm_compute in N.to_nat ((snd (fst (fst f11_9)) + N.of_nat look11_9 - s11_9) mod N.of_nat p11_9).
Definition jj11_9 : nat := Eval vm_compute in (N11_9 - cc11_9 - 1) mod kq11_9.
Definition S11_9 : sst := Eval vm_compute in
  gcut look11_9 (grst rr11_9 (c1101, true, inst11)).
Definition fe11 : N * N := Eval vm_compute in
  glast (s11_10 - N.of_nat (looke11 + 60)) tr11 (0, 0)%N.
Definition rre11 : nat := Eval vm_compute in N.to_nat (fst fe11).
Definition ue11 : nat := Eval vm_compute in
  N.to_nat (snd fe11 + N.of_nat looke11 - (s11_9 + N.of_nat (N11_9 * p11_9))).
Definition Se11 : sst := Eval vm_compute in gcut looke11 (grst rre11 (c1101, true, inst11)).
Definition Rj11_0 : nat := rr11_1.
Definition Rj11_1 : nat := Eval vm_compute in
  rr11_2 - rr11_1 - R11_1 * ((N11_1 - cc11_1 - 1 - jj11_1) / kq11_1).
Definition Rj11_2 : nat := Eval vm_compute in
  rr11_3 - rr11_2 - R11_2 * ((N11_2 - cc11_2 - 1 - jj11_2) / kq11_2).
Definition Rj11_3 : nat := Eval vm_compute in
  rr11_4 - rr11_3 - R11_3 * ((N11_3 - cc11_3 - 1 - jj11_3) / kq11_3).
Definition Rj11_4 : nat := Eval vm_compute in
  rr11_5 - rr11_4 - R11_4 * ((N11_4 - cc11_4 - 1 - jj11_4) / kq11_4).
Definition Rj11_5 : nat := Eval vm_compute in
  rr11_6 - rr11_5 - R11_5 * ((N11_5 - cc11_5 - 1 - jj11_5) / kq11_5).
Definition Rj11_6 : nat := Eval vm_compute in
  rr11_7 - rr11_6 - R11_6 * ((N11_6 - cc11_6 - 1 - jj11_6) / kq11_6).
Definition Rj11_7 : nat := Eval vm_compute in
  rr11_8 - rr11_7 - R11_7 * ((N11_7 - cc11_7 - 1 - jj11_7) / kq11_7).
Definition Rj11_8 : nat := Eval vm_compute in
  rr11_9 - rr11_8 - R11_8 * ((N11_8 - cc11_8 - 1 - jj11_8) / kq11_8).
Definition Rj11_9 : nat := Eval vm_compute in
  rre11 - rr11_9 - R11_9 * ((N11_9 - cc11_9 - 1 - jj11_9) / kq11_9).

(** ** The cuts *)

Definition u11_1 : list bool := firstn uu11_1 E11_1.
Definition v11_1 : list bool := skipn uu11_1 E11_1.
Definition u11_2 : list bool := firstn uu11_2 E11_2.
Definition v11_2 : list bool := skipn uu11_2 E11_2.
Definition u11_3 : list bool := firstn uu11_3 E11_3.
Definition v11_3 : list bool := skipn uu11_3 E11_3.
Definition u11_4 : list bool := firstn uu11_4 E11_4.
Definition v11_4 : list bool := skipn uu11_4 E11_4.
Definition u11_5 : list bool := firstn uu11_5 E11_5.
Definition v11_5 : list bool := skipn uu11_5 E11_5.
Definition u11_6 : list bool := firstn uu11_6 E11_6.
Definition v11_6 : list bool := skipn uu11_6 E11_6.
Definition u11_7 : list bool := firstn uu11_7 E11_7.
Definition v11_7 : list bool := skipn uu11_7 E11_7.
Definition u11_8 : list bool := firstn uu11_8 E11_8.
Definition v11_8 : list bool := skipn uu11_8 E11_8.
Definition u11_9 : list bool := firstn uu11_9 E11_9.
Definition v11_9 : list bool := skipn uu11_9 E11_9.
Definition F11_0 : list bool := Hd11 ++ rp E11_1 cc11_1 ++ u11_1.
Definition C11_1 : list bool := v11_1 ++ u11_1.
Definition K11_1 : list bool := rp C11_1 kq11_1.
Lemma tl11_1 : rp E11_1 (jj11_1 + 1) = u11_1 ++ rp C11_1 jj11_1 ++ v11_1.
Proof. vm_compute. reflexivity. Qed.
Definition F11_1 : list bool :=
  (rp C11_1 jj11_1 ++ v11_1) ++ J11_1 ++ rp E11_2 cc11_2 ++ u11_2.
Definition C11_2 : list bool := v11_2 ++ u11_2.
Definition K11_2 : list bool := rp C11_2 kq11_2.
Lemma tl11_2 : rp E11_2 (jj11_2 + 1) = u11_2 ++ rp C11_2 jj11_2 ++ v11_2.
Proof. vm_compute. reflexivity. Qed.
Definition F11_2 : list bool :=
  (rp C11_2 jj11_2 ++ v11_2) ++ J11_2 ++ rp E11_3 cc11_3 ++ u11_3.
Definition C11_3 : list bool := v11_3 ++ u11_3.
Definition K11_3 : list bool := rp C11_3 kq11_3.
Lemma tl11_3 : rp E11_3 (jj11_3 + 1) = u11_3 ++ rp C11_3 jj11_3 ++ v11_3.
Proof. vm_compute. reflexivity. Qed.
Definition F11_3 : list bool :=
  (rp C11_3 jj11_3 ++ v11_3) ++ J11_3 ++ rp E11_4 cc11_4 ++ u11_4.
Definition C11_4 : list bool := v11_4 ++ u11_4.
Definition K11_4 : list bool := rp C11_4 kq11_4.
Lemma tl11_4 : rp E11_4 (jj11_4 + 1) = u11_4 ++ rp C11_4 jj11_4 ++ v11_4.
Proof. vm_compute. reflexivity. Qed.
Definition F11_4 : list bool :=
  (rp C11_4 jj11_4 ++ v11_4) ++ J11_4 ++ rp E11_5 cc11_5 ++ u11_5.
Definition C11_5 : list bool := v11_5 ++ u11_5.
Definition K11_5 : list bool := rp C11_5 kq11_5.
Lemma tl11_5 : rp E11_5 (jj11_5 + 1) = u11_5 ++ rp C11_5 jj11_5 ++ v11_5.
Proof. vm_compute. reflexivity. Qed.
Definition F11_5 : list bool :=
  (rp C11_5 jj11_5 ++ v11_5) ++ J11_5 ++ rp E11_6 cc11_6 ++ u11_6.
Definition C11_6 : list bool := v11_6 ++ u11_6.
Definition K11_6 : list bool := rp C11_6 kq11_6.
Lemma tl11_6 : rp E11_6 (jj11_6 + 1) = u11_6 ++ rp C11_6 jj11_6 ++ v11_6.
Proof. vm_compute. reflexivity. Qed.
Definition F11_6 : list bool :=
  (rp C11_6 jj11_6 ++ v11_6) ++ J11_6 ++ rp E11_7 cc11_7 ++ u11_7.
Definition C11_7 : list bool := v11_7 ++ u11_7.
Definition K11_7 : list bool := rp C11_7 kq11_7.
Lemma tl11_7 : rp E11_7 (jj11_7 + 1) = u11_7 ++ rp C11_7 jj11_7 ++ v11_7.
Proof. vm_compute. reflexivity. Qed.
Definition F11_7 : list bool :=
  (rp C11_7 jj11_7 ++ v11_7) ++ J11_7 ++ rp E11_8 cc11_8 ++ u11_8.
Definition C11_8 : list bool := v11_8 ++ u11_8.
Definition K11_8 : list bool := rp C11_8 kq11_8.
Lemma tl11_8 : rp E11_8 (jj11_8 + 1) = u11_8 ++ rp C11_8 jj11_8 ++ v11_8.
Proof. vm_compute. reflexivity. Qed.
Definition F11_8 : list bool :=
  (rp C11_8 jj11_8 ++ v11_8) ++ J11_8 ++ rp E11_9 cc11_9 ++ u11_9.
Definition C11_9 : list bool := v11_9 ++ u11_9.
Definition K11_9 : list bool := rp C11_9 kq11_9.
Lemma tl11_9 : rp E11_9 (jj11_9 + 1) = u11_9 ++ rp C11_9 jj11_9 ++ v11_9.
Proof. vm_compute. reflexivity. Qed.
Definition F11_9 : list bool := (rp C11_9 jj11_9 ++ v11_9) ++ firstn ue11 J11_9.
Definition Fw11 : list bool := skipn ue11 J11_9 ++ w11.

Lemma cells11_cut : forall n1 n2 n3 n4 n5 n6 n7 n8 n9,
  cells11 (cc11_1 + (n1 * kq11_1 + jj11_1) + 1) (cc11_2 + (n2 * kq11_2 + jj11_2) + 1) (cc11_3 + (n3 *
    kq11_3 + jj11_3) + 1) (cc11_4 + (n4 * kq11_4 + jj11_4) + 1) (cc11_5 + (n5 * kq11_5 + jj11_5) +
    1) (cc11_6 + (n6 * kq11_6 + jj11_6) + 1) (cc11_7 + (n7 * kq11_7 + jj11_7) + 1) (cc11_8 + (n8 *
    kq11_8 + jj11_8) + 1) (cc11_9 + (n9 * kq11_9 + jj11_9) + 1) = (F11_0 ++ rp K11_1 n1 ++ F11_1 ++
    rp K11_2 n2 ++ F11_2 ++ rp K11_3 n3 ++ F11_3 ++ rp K11_4 n4 ++ F11_4 ++ rp K11_5 n5 ++ F11_5 ++
    rp K11_6 n6 ++ F11_6 ++ rp K11_7 n7 ++ F11_7 ++ rp K11_8 n8 ++ F11_8 ++ rp K11_9 n9 ++ F11_9 ++
    []) ++ Fw11.
Proof.
  intros n1 n2 n3 n4 n5 n6 n7 n8 n9. rewrite cells11_eq.
  replace (cc11_1 + (n1 * kq11_1 + jj11_1) + 1) with (cc11_1 + n1 * kq11_1 + (jj11_1 + 1)) by lia.
  rewrite (rp_recut E11_1 u11_1 v11_1 (n1 * kq11_1) cc11_1 (jj11_1 + 1) (rp C11_1 jj11_1 ++ v11_1)
             (eq_sym (firstn_skipn uu11_1 E11_1)) tl11_1).
  rewrite (rp_mul (v11_1 ++ u11_1) kq11_1 n1).
  replace (cc11_2 + (n2 * kq11_2 + jj11_2) + 1) with (cc11_2 + n2 * kq11_2 + (jj11_2 + 1)) by lia.
  rewrite (rp_recut E11_2 u11_2 v11_2 (n2 * kq11_2) cc11_2 (jj11_2 + 1) (rp C11_2 jj11_2 ++ v11_2)
             (eq_sym (firstn_skipn uu11_2 E11_2)) tl11_2).
  rewrite (rp_mul (v11_2 ++ u11_2) kq11_2 n2).
  replace (cc11_3 + (n3 * kq11_3 + jj11_3) + 1) with (cc11_3 + n3 * kq11_3 + (jj11_3 + 1)) by lia.
  rewrite (rp_recut E11_3 u11_3 v11_3 (n3 * kq11_3) cc11_3 (jj11_3 + 1) (rp C11_3 jj11_3 ++ v11_3)
             (eq_sym (firstn_skipn uu11_3 E11_3)) tl11_3).
  rewrite (rp_mul (v11_3 ++ u11_3) kq11_3 n3).
  replace (cc11_4 + (n4 * kq11_4 + jj11_4) + 1) with (cc11_4 + n4 * kq11_4 + (jj11_4 + 1)) by lia.
  rewrite (rp_recut E11_4 u11_4 v11_4 (n4 * kq11_4) cc11_4 (jj11_4 + 1) (rp C11_4 jj11_4 ++ v11_4)
             (eq_sym (firstn_skipn uu11_4 E11_4)) tl11_4).
  rewrite (rp_mul (v11_4 ++ u11_4) kq11_4 n4).
  replace (cc11_5 + (n5 * kq11_5 + jj11_5) + 1) with (cc11_5 + n5 * kq11_5 + (jj11_5 + 1)) by lia.
  rewrite (rp_recut E11_5 u11_5 v11_5 (n5 * kq11_5) cc11_5 (jj11_5 + 1) (rp C11_5 jj11_5 ++ v11_5)
             (eq_sym (firstn_skipn uu11_5 E11_5)) tl11_5).
  rewrite (rp_mul (v11_5 ++ u11_5) kq11_5 n5).
  replace (cc11_6 + (n6 * kq11_6 + jj11_6) + 1) with (cc11_6 + n6 * kq11_6 + (jj11_6 + 1)) by lia.
  rewrite (rp_recut E11_6 u11_6 v11_6 (n6 * kq11_6) cc11_6 (jj11_6 + 1) (rp C11_6 jj11_6 ++ v11_6)
             (eq_sym (firstn_skipn uu11_6 E11_6)) tl11_6).
  rewrite (rp_mul (v11_6 ++ u11_6) kq11_6 n6).
  replace (cc11_7 + (n7 * kq11_7 + jj11_7) + 1) with (cc11_7 + n7 * kq11_7 + (jj11_7 + 1)) by lia.
  rewrite (rp_recut E11_7 u11_7 v11_7 (n7 * kq11_7) cc11_7 (jj11_7 + 1) (rp C11_7 jj11_7 ++ v11_7)
             (eq_sym (firstn_skipn uu11_7 E11_7)) tl11_7).
  rewrite (rp_mul (v11_7 ++ u11_7) kq11_7 n7).
  replace (cc11_8 + (n8 * kq11_8 + jj11_8) + 1) with (cc11_8 + n8 * kq11_8 + (jj11_8 + 1)) by lia.
  rewrite (rp_recut E11_8 u11_8 v11_8 (n8 * kq11_8) cc11_8 (jj11_8 + 1) (rp C11_8 jj11_8 ++ v11_8)
             (eq_sym (firstn_skipn uu11_8 E11_8)) tl11_8).
  rewrite (rp_mul (v11_8 ++ u11_8) kq11_8 n8).
  replace (cc11_9 + (n9 * kq11_9 + jj11_9) + 1) with (cc11_9 + n9 * kq11_9 + (jj11_9 + 1)) by lia.
  rewrite (rp_recut E11_9 u11_9 v11_9 (n9 * kq11_9) cc11_9 (jj11_9 + 1) (rp C11_9 jj11_9 ++ v11_9)
             (eq_sym (firstn_skipn uu11_9 E11_9)) tl11_9).
  rewrite (rp_mul (v11_9 ++ u11_9) kq11_9 n9).
  rewrite <- (firstn_skipn ue11 J11_9) at 1.
  unfold F11_0, K11_1, F11_1, C11_1, K11_2, F11_2, C11_2, K11_3, F11_3, C11_3, K11_4, F11_4, C11_4, K11_5, F11_5, C11_5, K11_6, F11_6, C11_6, K11_7, F11_7, C11_7, K11_8, F11_8, C11_8, K11_9, F11_9, C11_9, Fw11.
  rewrite ?app_nil_r, <- ?app_assoc. reflexivity.
Qed.

(** ** Runs and cycles, round by round *)

Definition st110 : sst := (c1101, true, []).
Definition lF11_0 : list (Z * nat) := Eval vm_compute in grl Rj11_0 st110 F11_0.
Lemma RF11_0 : Run st110 F11_0 S11_1 (pSh lF11_0) (pV lF11_0).
Proof. apply (crun_run Rj11_0 4). vm_compute. reflexivity. Qed.
Definition lC11_1 : list (Z * nat) := Eval vm_compute in grl R11_1 S11_1 K11_1.
Lemma RC11_1 : Run S11_1 K11_1 S11_1 (pSh lC11_1) (pV lC11_1).
Proof. apply (crun_run R11_1 4). vm_compute. reflexivity. Qed.
Definition lF11_1 : list (Z * nat) := Eval vm_compute in grl Rj11_1 S11_1 F11_1.
Lemma RF11_1 : Run S11_1 F11_1 S11_2 (pSh lF11_1) (pV lF11_1).
Proof. apply (crun_run Rj11_1 4). vm_compute. reflexivity. Qed.
Definition lC11_2 : list (Z * nat) := Eval vm_compute in grl R11_2 S11_2 K11_2.
Lemma RC11_2 : Run S11_2 K11_2 S11_2 (pSh lC11_2) (pV lC11_2).
Proof. apply (crun_run R11_2 4). vm_compute. reflexivity. Qed.
Definition lF11_2 : list (Z * nat) := Eval vm_compute in grl Rj11_2 S11_2 F11_2.
Lemma RF11_2 : Run S11_2 F11_2 S11_3 (pSh lF11_2) (pV lF11_2).
Proof. apply (crun_run Rj11_2 4). vm_compute. reflexivity. Qed.
Definition lC11_3 : list (Z * nat) := Eval vm_compute in grl R11_3 S11_3 K11_3.
Lemma RC11_3 : Run S11_3 K11_3 S11_3 (pSh lC11_3) (pV lC11_3).
Proof. apply (crun_run R11_3 4). vm_compute. reflexivity. Qed.
Definition lF11_3 : list (Z * nat) := Eval vm_compute in grl Rj11_3 S11_3 F11_3.
Lemma RF11_3 : Run S11_3 F11_3 S11_4 (pSh lF11_3) (pV lF11_3).
Proof. apply (crun_run Rj11_3 4). vm_compute. reflexivity. Qed.
Definition lC11_4 : list (Z * nat) := Eval vm_compute in grl R11_4 S11_4 K11_4.
Lemma RC11_4 : Run S11_4 K11_4 S11_4 (pSh lC11_4) (pV lC11_4).
Proof. apply (crun_run R11_4 4). vm_compute. reflexivity. Qed.
Definition lF11_4 : list (Z * nat) := Eval vm_compute in grl Rj11_4 S11_4 F11_4.
Lemma RF11_4 : Run S11_4 F11_4 S11_5 (pSh lF11_4) (pV lF11_4).
Proof. apply (crun_run Rj11_4 4). vm_compute. reflexivity. Qed.
Definition lC11_5 : list (Z * nat) := Eval vm_compute in grl R11_5 S11_5 K11_5.
Lemma RC11_5 : Run S11_5 K11_5 S11_5 (pSh lC11_5) (pV lC11_5).
Proof. apply (crun_run R11_5 4). vm_compute. reflexivity. Qed.
Definition lF11_5 : list (Z * nat) := Eval vm_compute in grl Rj11_5 S11_5 F11_5.
Lemma RF11_5 : Run S11_5 F11_5 S11_6 (pSh lF11_5) (pV lF11_5).
Proof. apply (crun_run Rj11_5 4). vm_compute. reflexivity. Qed.
Definition lC11_6 : list (Z * nat) := Eval vm_compute in grl R11_6 S11_6 K11_6.
Lemma RC11_6 : Run S11_6 K11_6 S11_6 (pSh lC11_6) (pV lC11_6).
Proof. apply (crun_run R11_6 4). vm_compute. reflexivity. Qed.
Definition lF11_6 : list (Z * nat) := Eval vm_compute in grl Rj11_6 S11_6 F11_6.
Lemma RF11_6 : Run S11_6 F11_6 S11_7 (pSh lF11_6) (pV lF11_6).
Proof. apply (crun_run Rj11_6 4). vm_compute. reflexivity. Qed.
Definition lC11_7 : list (Z * nat) := Eval vm_compute in grl R11_7 S11_7 K11_7.
Lemma RC11_7 : Run S11_7 K11_7 S11_7 (pSh lC11_7) (pV lC11_7).
Proof. apply (crun_run R11_7 4). vm_compute. reflexivity. Qed.
Definition lF11_7 : list (Z * nat) := Eval vm_compute in grl Rj11_7 S11_7 F11_7.
Lemma RF11_7 : Run S11_7 F11_7 S11_8 (pSh lF11_7) (pV lF11_7).
Proof. apply (crun_run Rj11_7 4). vm_compute. reflexivity. Qed.
Definition lC11_8 : list (Z * nat) := Eval vm_compute in grl R11_8 S11_8 K11_8.
Lemma RC11_8 : Run S11_8 K11_8 S11_8 (pSh lC11_8) (pV lC11_8).
Proof. apply (crun_run R11_8 4). vm_compute. reflexivity. Qed.
Definition lF11_8 : list (Z * nat) := Eval vm_compute in grl Rj11_8 S11_8 F11_8.
Lemma RF11_8 : Run S11_8 F11_8 S11_9 (pSh lF11_8) (pV lF11_8).
Proof. apply (crun_run Rj11_8 4). vm_compute. reflexivity. Qed.
Definition lC11_9 : list (Z * nat) := Eval vm_compute in grl R11_9 S11_9 K11_9.
Lemma RC11_9 : Run S11_9 K11_9 S11_9 (pSh lC11_9) (pV lC11_9).
Proof. apply (crun_run R11_9 4). vm_compute. reflexivity. Qed.
Definition lF11_9 : list (Z * nat) := Eval vm_compute in grl Rj11_9 S11_9 F11_9.
Lemma RF11_9 : Run S11_9 F11_9 Se11 (pSh lF11_9) (pV lF11_9).
Proof. apply (crun_run Rj11_9 4). vm_compute. reflexivity. Qed.

Definition segs11 (n1 n2 n3 n4 n5 n6 n7 n8 n9 : nat) : list seg :=
  [SP lF11_0; SK lC11_1 n1; SP lF11_1; SK lC11_2 n2; SP lF11_2; SK lC11_3 n3; SP lF11_3; SK lC11_4 n4;
    SP lF11_4; SK lC11_5 n5; SP lF11_5; SK lC11_6 n6; SP lF11_6; SK lC11_7 n7; SP lF11_7; SK lC11_8
    n8; SP lF11_8; SK lC11_9 n9; SP lF11_9].

Lemma runA11 : forall n1 n2 n3 n4 n5 n6 n7 n8 n9,
  Run st110 (F11_0 ++ rp K11_1 n1 ++ F11_1 ++ rp K11_2 n2 ++ F11_2 ++ rp K11_3 n3 ++ F11_3 ++ rp K11_4
    n4 ++ F11_4 ++ rp K11_5 n5 ++ F11_5 ++ rp K11_6 n6 ++ F11_6 ++ rp K11_7 n7 ++ F11_7 ++ rp K11_8
    n8 ++ F11_8 ++ rp K11_9 n9 ++ F11_9 ++ []) Se11
      (segSh (segs11 n1 n2 n3 n4 n5 n6 n7 n8 n9)) (segV (segs11 n1 n2 n3 n4 n5 n6 n7 n8 n9)).
Proof.
  intros n1 n2 n3 n4 n5 n6 n7 n8 n9. unfold segs11.
  exact (run_SP _ _ _ _ _ _ _ RF11_0
    (run_SK _ _ _ _ _ _ _ RC11_1
    (run_SP _ _ _ _ _ _ _ RF11_1 (run_SK _ _ _ _ _ _ _ RC11_2
    (run_SP _ _ _ _ _ _ _ RF11_2 (run_SK _ _ _ _ _ _ _ RC11_3
    (run_SP _ _ _ _ _ _ _ RF11_3 (run_SK _ _ _ _ _ _ _ RC11_4
    (run_SP _ _ _ _ _ _ _ RF11_4 (run_SK _ _ _ _ _ _ _ RC11_5
    (run_SP _ _ _ _ _ _ _ RF11_5 (run_SK _ _ _ _ _ _ _ RC11_6
    (run_SP _ _ _ _ _ _ _ RF11_6 (run_SK _ _ _ _ _ _ _ RC11_7
    (run_SP _ _ _ _ _ _ _ RF11_7 (run_SK _ _ _ _ _ _ _ RC11_8
    (run_SP _ _ _ _ _ _ _ RF11_8 (run_SK _ _ _ _ _ _ _ RC11_9
    (run_SP _ _ _ _ _ _ _ RF11_9 (run_end _)))))))))))))))))))).
Qed.

(** ** The carry chain *)

Definition as11 := Eval vm_compute in asm 0 (segs11 O O O O O O O O O).
Definition k11_0 : list bool := Eval vm_compute in
  match as11 with Some ([Lit a; _; _; _; _; _; _; _; _; _; _; _; _; _; _; _; _; _; _], _) => a | _ => [] end.
Definition k11_1 : list bool := Eval vm_compute in
  match as11 with Some ([_; _; Lit a; _; _; _; _; _; _; _; _; _; _; _; _; _; _; _; _], _) => a | _ => [] end.
Definition k11_2 : list bool := Eval vm_compute in
  match as11 with Some ([_; _; _; _; Lit a; _; _; _; _; _; _; _; _; _; _; _; _; _; _], _) => a | _ => [] end.
Definition k11_3 : list bool := Eval vm_compute in
  match as11 with Some ([_; _; _; _; _; _; Lit a; _; _; _; _; _; _; _; _; _; _; _; _], _) => a | _ => [] end.
Definition k11_4 : list bool := Eval vm_compute in
  match as11 with Some ([_; _; _; _; _; _; _; _; Lit a; _; _; _; _; _; _; _; _; _; _], _) => a | _ => [] end.
Definition k11_5 : list bool := Eval vm_compute in
  match as11 with Some ([_; _; _; _; _; _; _; _; _; _; Lit a; _; _; _; _; _; _; _; _], _) => a | _ => [] end.
Definition k11_6 : list bool := Eval vm_compute in
  match as11 with Some ([_; _; _; _; _; _; _; _; _; _; _; _; Lit a; _; _; _; _; _; _], _) => a | _ => [] end.
Definition k11_7 : list bool := Eval vm_compute in
  match as11 with Some ([_; _; _; _; _; _; _; _; _; _; _; _; _; _; Lit a; _; _; _; _], _) => a | _ => [] end.
Definition k11_8 : list bool := Eval vm_compute in
  match as11 with Some ([_; _; _; _; _; _; _; _; _; _; _; _; _; _; _; _; Lit a; _; _], _) => a | _ => [] end.
Definition k11_9 : list bool := Eval vm_compute in
  match as11 with Some ([_; _; _; _; _; _; _; _; _; _; _; _; _; _; _; _; _; _; Lit a], _) => a | _ => [] end.
Definition kk11_1 : list bool := Eval vm_compute in
  match as11 with Some ([_; Rep p _; _; _; _; _; _; _; _; _; _; _; _; _; _; _; _; _; _], _) => p | _ => [] end.
Definition kk11_2 : list bool := Eval vm_compute in
  match as11 with Some ([_; _; _; Rep p _; _; _; _; _; _; _; _; _; _; _; _; _; _; _; _], _) => p | _ => [] end.
Definition kk11_3 : list bool := Eval vm_compute in
  match as11 with Some ([_; _; _; _; _; Rep p _; _; _; _; _; _; _; _; _; _; _; _; _; _], _) => p | _ => [] end.
Definition kk11_4 : list bool := Eval vm_compute in
  match as11 with Some ([_; _; _; _; _; _; _; Rep p _; _; _; _; _; _; _; _; _; _; _; _], _) => p | _ => [] end.
Definition kk11_5 : list bool := Eval vm_compute in
  match as11 with Some ([_; _; _; _; _; _; _; _; _; Rep p _; _; _; _; _; _; _; _; _; _], _) => p | _ => [] end.
Definition kk11_6 : list bool := Eval vm_compute in
  match as11 with Some ([_; _; _; _; _; _; _; _; _; _; _; Rep p _; _; _; _; _; _; _; _], _) => p | _ => [] end.
Definition kk11_7 : list bool := Eval vm_compute in
  match as11 with Some ([_; _; _; _; _; _; _; _; _; _; _; _; _; Rep p _; _; _; _; _; _], _) => p | _ => [] end.
Definition kk11_8 : list bool := Eval vm_compute in
  match as11 with Some ([_; _; _; _; _; _; _; _; _; _; _; _; _; _; _; Rep p _; _; _; _], _) => p | _ => [] end.
Definition kk11_9 : list bool := Eval vm_compute in
  match as11 with Some ([_; _; _; _; _; _; _; _; _; _; _; _; _; _; _; _; _; Rep p _; _], _) => p | _ => [] end.
Definition cB11 : Z := Eval vm_compute in match as11 with Some (_, c) => c | None => (-1)%Z end.

Lemma as11_ok : forall n1 n2 n3 n4 n5 n6 n7 n8 n9,
  asm 0 (segs11 n1 n2 n3 n4 n5 n6 n7 n8 n9) = Some ([Lit k11_0; Rep kk11_1 n1; Lit k11_1; Rep kk11_2
    n2; Lit k11_2; Rep kk11_3 n3; Lit k11_3; Rep kk11_4 n4; Lit k11_4; Rep kk11_5 n5; Lit k11_5; Rep
    kk11_6 n6; Lit k11_6; Rep kk11_7 n7; Lit k11_7; Rep kk11_8 n8; Lit k11_8; Rep kk11_9 n9; Lit
    k11_9], cB11).
Proof. intros n1 n2 n3 n4 n5 n6 n7 n8 n9. vm_compute. reflexivity. Qed.

(** ** The closing computation *)

Definition ec11 := Eval vm_compute in endcert 6000 (addpost Se11 Fw11).
Definition ae11 : Z := Eval vm_compute in match ec11 with Some (a, _, _, _) => a | None => 0%Z end.
Definition z1_11 : nat := Eval vm_compute in match ec11 with Some (_, z, _, _) => z | None => O end.
Definition z2_11 : nat := Eval vm_compute in match ec11 with Some (_, _, z, _) => z | None => O end.
Definition w12 : list bool := Eval vm_compute in match ec11 with Some (_, _, _, x) => x | None => [] end.
Definition la11 : nat := Eval vm_compute in (z1_11 + z2_11 - 1) / 3.
Definition tp11 : N := Eval vm_compute in Z.to_N ((cB11 + ae11) / 4 ^ Z.of_nat la11).
Definition ab11 : list bool := Eval vm_compute in
  zbits ((cB11 + ae11) mod 4 ^ Z.of_nat la11) (2 * la11).

Lemma ec11_ok : endcert 6000 (addpost Se11 Fw11) = Some (ae11, z1_11, z2_11, w12).
Proof. vm_compute. reflexivity. Qed.

Lemma cB11_nn : (0 <= cB11)%Z.
Proof. apply Z.leb_le. vm_compute. reflexivity. Qed.

Lemma ab11_val : (Z.of_N (bvalN ab11) + Z.of_N tp11 * pw4 la11 = cB11 + ae11)%Z.
Proof. vm_compute. reflexivity. Qed.

Lemma ab11_len : length ab11 = 2 * la11.
Proof. vm_compute. reflexivity. Qed.

Lemma z_11 : z1_11 + z2_11 = 3 * la11 + 1.
Proof. vm_compute. reflexivity. Qed.

Definition Cw11 (n1 n2 n3 n4 n5 n6 n7 n8 n9 : nat) : list bool :=
  den [Lit k11_0; Rep kk11_1 n1; Lit k11_1; Rep kk11_2 n2; Lit k11_2; Rep kk11_3 n3; Lit k11_3; Rep
    kk11_4 n4; Lit k11_4; Rep kk11_5 n5; Lit k11_5; Rep kk11_6 n6; Lit k11_6; Rep kk11_7 n7; Lit
    k11_7; Rep kk11_8 n8; Lit k11_8; Rep kk11_9 n9; Lit k11_9] ++ ab11.
Definition lc11 (n1 n2 n3 n4 n5 n6 n7 n8 n9 : nat) : nat := segSh (segs11 n1 n2 n3 n4 n5 n6 n7 n8 n9) + la11.

Lemma Cw11_len : forall n1 n2 n3 n4 n5 n6 n7 n8 n9, length (Cw11 n1 n2 n3 n4 n5 n6 n7 n8 n9) = 2 * lc11 n1 n2 n3 n4 n5 n6 n7 n8 n9.
Proof.
  intros n1 n2 n3 n4 n5 n6 n7 n8 n9.
  exact (proj1 (stageA st110 _ Se11 (segs11 n1 n2 n3 n4 n5 n6 n7 n8 n9) 6000 Fw11 ae11 z1_11 z2_11 w12 _ cB11 ab11 la11
              (Z.of_N tp11) (runA11 n1 n2 n3 n4 n5 n6 n7 n8 n9) ec11_ok (as11_ok n1 n2 n3 n4 n5 n6 n7 n8 n9) cB11_nn ab11_val ab11_len z_11)).
Qed.

Lemma end11 : forall n1 n2 n3 n4 n5 n6 n7 n8 n9 h k, (1 <= k)%nat -> exists n M',
  tickN 3 n (rep10 k ++ c1101 ++ repeat true (3 * h) ++ rep10 je11 ++ c1101 ++
             encb false (b11 (cc11_1 + (n1 * kq11_1 + jj11_1) + 1) (cc11_2 + (n2 * kq11_2 + jj11_2) + 1) (cc11_3
               + (n3 * kq11_3 + jj11_3) + 1) (cc11_4 + (n4 * kq11_4 + jj11_4) + 1) (cc11_5 + (n5 *
               kq11_5 + jj11_5) + 1) (cc11_6 + (n6 * kq11_6 + jj11_6) + 1) (cc11_7 + (n7 * kq11_7 +
               jj11_7) + 1) (cc11_8 + (n8 * kq11_8 + jj11_8) + 1) (cc11_9 + (n9 * kq11_9 + jj11_9) +
               1)) ++ w11) =
    Some (Slev M' (3 * (h + lc11 n1 n2 n3 n4 n5 n6 n7 n8 n9) + 1) w12) /\
  Z.of_nat M' = (Z.of_nat k +
                 (Z.of_nat (bval (Cw11 n1 n2 n3 n4 n5 n6 n7 n8 n9)) + Z.of_N tp11 * pw4 (lc11 n1 n2 n3 n4 n5 n6 n7 n8 n9)) * pw4 h)%Z.
Proof.
  intros n1 n2 n3 n4 n5 n6 n7 n8 n9 h k Hk.
  destruct (stageA st110 _ Se11 (segs11 n1 n2 n3 n4 n5 n6 n7 n8 n9) 6000 Fw11 ae11 z1_11 z2_11 w12 _ cB11 ab11 la11
              (Z.of_N tp11) (runA11 n1 n2 n3 n4 n5 n6 n7 n8 n9) ec11_ok (as11_ok n1 n2 n3 n4 n5 n6 n7 n8 n9) cB11_nn ab11_val ab11_len z_11) as [_ H].
  destruct (H h k Hk) as [n [M' [E D]]]. exists n, M'. split; [| exact D].
  change (rep10 je11 ++ c1101 ++ encb false (b11 (cc11_1 + (n1 * kq11_1 + jj11_1) + 1) (cc11_2 + (n2 *
    kq11_2 + jj11_2) + 1) (cc11_3 + (n3 * kq11_3 + jj11_3) + 1) (cc11_4 + (n4 * kq11_4 + jj11_4) +
    1) (cc11_5 + (n5 * kq11_5 + jj11_5) + 1) (cc11_6 + (n6 * kq11_6 + jj11_6) + 1) (cc11_7 + (n7 *
    kq11_7 + jj11_7) + 1) (cc11_8 + (n8 * kq11_8 + jj11_8) + 1) (cc11_9 + (n9 * kq11_9 + jj11_9) +
    1)) ++ w11)
    with (cells11 (cc11_1 + (n1 * kq11_1 + jj11_1) + 1) (cc11_2 + (n2 * kq11_2 + jj11_2) + 1) (cc11_3 + (n3 * kq11_3 + jj11_3) + 1) (cc11_4 + (n4 * kq11_4 + jj11_4) + 1) (cc11_5 + (n5 * kq11_5 + jj11_5) + 1) (cc11_6 + (n6 * kq11_6 + jj11_6) + 1) (cc11_7 + (n7 * kq11_7 + jj11_7) + 1) (cc11_8 + (n8 * kq11_8 + jj11_8) + 1) (cc11_9 + (n9 * kq11_9 + jj11_9) + 1)).
  rewrite cells11_cut.
  cbv [st110 conc] in E. rewrite ?app_nil_r, <- ?app_assoc in E. rewrite ?app_nil_r, <- ?app_assoc.
  exact E.
Qed.

(** ** What the division needs: which blocks are tripled, and the residues of the counts *)

Definition cfg11_trip : list bool := Eval vm_compute in
  map (fun P => negb (N.eqb (bvalN P mod 3) 0)) [kk11_1; kk11_2; kk11_3; kk11_4; kk11_5; kk11_6; kk11_7; kk11_8; kk11_9].
Definition cfg11_rho : list N := Eval vm_compute in
  [(((rc11_1 + 1594323 - (N.of_nat cc11_1 + 1 + N.of_nat jj11_1)%N) * (N.of_nat kq11_1 mod 3)) mod 3)%N; (((rc11_2 + 1594323 - (N.of_nat cc11_2 + 1 + N.of_nat jj11_2)%N) * (N.of_nat kq11_2 mod 3)) mod 3)%N; (((rc11_3 + 1594323 - (N.of_nat cc11_3 + 1 + N.of_nat jj11_3)%N) * (N.of_nat kq11_3 mod 3)) mod 3)%N; (((rc11_4 + 1594323 - (N.of_nat cc11_4 + 1 + N.of_nat jj11_4)%N) * (N.of_nat kq11_4 mod 3)) mod 3)%N; (((rc11_5 + 1594323 - (N.of_nat cc11_5 + 1 + N.of_nat jj11_5)%N) * (N.of_nat kq11_5 mod 3)) mod 3)%N; (((rc11_6 + 1594323 - (N.of_nat cc11_6 + 1 + N.of_nat jj11_6)%N) * (N.of_nat kq11_6 mod 3)) mod 3)%N; (((rc11_7 + 1594323 - (N.of_nat cc11_7 + 1 + N.of_nat jj11_7)%N) * (N.of_nat kq11_7 mod 3)) mod 3)%N; (((rc11_8 + 1594323 - (N.of_nat cc11_8 + 1 + N.of_nat jj11_8)%N) * (N.of_nat kq11_8 mod 3)) mod 3)%N; (((rc11_9 + 1594323 - (N.of_nat cc11_9 + 1 + N.of_nat jj11_9)%N) * (N.of_nat kq11_9 mod 3)) mod 3)%N].
Definition cfg11_k : list nat := Eval vm_compute in [kq11_1; kq11_2; kq11_3; kq11_4; kq11_5; kq11_6; kq11_7; kq11_8; kq11_9].
Definition cfg11_j : list nat := Eval vm_compute in [jj11_1; jj11_2; jj11_3; jj11_4; jj11_5; jj11_6; jj11_7; jj11_8; jj11_9].
Definition cfg11_rhoT : Z := Eval vm_compute in ((2 * vT11) mod 3)%Z.

End L1112a.

Module L1112b.

(** * 1RB1LB_1RC0RD_0LA1RE_0RF1LC_1LA0RB_---1LC: from level 11 to level 12

    The division by 3 of [0100 (10)^(h-2) C] with the counts as variables, level 12 for the
    real counts, and the residues modulo 3^2 and lower bounds of the counts of level 12.
    Generated by a script. *)

Import Individual62.
Import T694_levels End694 Sym694 Lev694 Lvl1_694 Eng694 Cert694 Run694 Res694 Gen694.
Import L23 L34 L45 L56 L6i L67a L67b L78a L78b L89a L89b L910a L910b L1011a L1011b L1112a.
Import Lia Arith PeanoNat Bool NArith ZArith.
Import Coq.Lists.List.
Import ListNotations.

(** ** The division *)

Lemma Zl11_den : forall G x1 x2 x3 x4 x5 x6 x7 x8 x9,
  [false; false; true; false] ++ rep01 (G * 3 + 0) ++ Cw11 (x1 * 3 + 0) (x2 * 3 + 1) (x3 * 3 + 0) (x4 * 3 + 2) (x5 * 3 + 0) (x6 * 3 + 1) (x7 * 3 + 0) (x8 * 3 + 1) (x9 * 3 + 2) =
  den [Lit [false; false; true; false]; Rep (rp [false; true] 3) G; Lit (rp [false; true] 0 ++ k11_0);
    Rep (rp kk11_1 3) x1; Lit (rp kk11_1 0 ++ k11_1); Rep (rp kk11_2 3) x2; Lit (rp kk11_2 1 ++
    k11_2); Rep (rp kk11_3 3) x3; Lit (rp kk11_3 0 ++ k11_3); Rep (rp kk11_4 3) x4; Lit (rp kk11_4 2
    ++ k11_4); Rep (rp kk11_5 3) x5; Lit (rp kk11_5 0 ++ k11_5); Rep (rp kk11_6 3) x6; Lit (rp
    kk11_6 1 ++ k11_6); Rep (rp kk11_7 3) x7; Lit (rp kk11_7 0 ++ k11_7); Rep (rp kk11_8 3) x8; Lit
    (rp kk11_8 1 ++ k11_8); Rep (rp kk11_9 3) x9; Lit (rp kk11_9 2 ++ k11_9 ++ ab11)].
Proof.
  intros G x1 x2 x3 x4 x5 x6 x7 x8 x9. unfold Cw11. cbn [den bden].
  change (rep01 (G * 3 + 0)) with (rp [false; true] (G * 3 + 0)).
  rewrite ?rp_add, ?rp_mul, ?app_nil_r, <- ?app_assoc. reflexivity.
Qed.

Definition dv11 := Eval vm_compute in
  dmB 3 [Lit [false; false; true; false]; Rep (rp [false; true] 3) O; Lit (rp [false; true] 0 ++
    k11_0); Rep (rp kk11_1 3) O; Lit (rp kk11_1 0 ++ k11_1); Rep (rp kk11_2 3) O; Lit (rp kk11_2 1
    ++ k11_2); Rep (rp kk11_3 3) O; Lit (rp kk11_3 0 ++ k11_3); Rep (rp kk11_4 3) O; Lit (rp kk11_4
    2 ++ k11_4); Rep (rp kk11_5 3) O; Lit (rp kk11_5 0 ++ k11_5); Rep (rp kk11_6 3) O; Lit (rp
    kk11_6 1 ++ k11_6); Rep (rp kk11_7 3) O; Lit (rp kk11_7 0 ++ k11_7); Rep (rp kk11_8 3) O; Lit
    (rp kk11_8 1 ++ k11_8); Rep (rp kk11_9 3) O; Lit (rp kk11_9 2 ++ k11_9 ++ ab11)] tp11.
Definition a12_0 : list bool := Eval vm_compute in
  match dv11 with Some ([Lit a; _; _; _; _; _; _; _; _; _; _; _; _; _; _; _; _; _; _; _; _], _) => a | _ => [] end.
Definition a12_1 : list bool := Eval vm_compute in
  match dv11 with Some ([_; _; Lit a; _; _; _; _; _; _; _; _; _; _; _; _; _; _; _; _; _; _], _) => a | _ => [] end.
Definition a12_2 : list bool := Eval vm_compute in
  match dv11 with Some ([_; _; _; _; Lit a; _; _; _; _; _; _; _; _; _; _; _; _; _; _; _; _], _) => a | _ => [] end.
Definition a12_3 : list bool := Eval vm_compute in
  match dv11 with Some ([_; _; _; _; _; _; Lit a; _; _; _; _; _; _; _; _; _; _; _; _; _; _], _) => a | _ => [] end.
Definition a12_4 : list bool := Eval vm_compute in
  match dv11 with Some ([_; _; _; _; _; _; _; _; Lit a; _; _; _; _; _; _; _; _; _; _; _; _], _) => a | _ => [] end.
Definition a12_5 : list bool := Eval vm_compute in
  match dv11 with Some ([_; _; _; _; _; _; _; _; _; _; Lit a; _; _; _; _; _; _; _; _; _; _], _) => a | _ => [] end.
Definition a12_6 : list bool := Eval vm_compute in
  match dv11 with Some ([_; _; _; _; _; _; _; _; _; _; _; _; Lit a; _; _; _; _; _; _; _; _], _) => a | _ => [] end.
Definition a12_7 : list bool := Eval vm_compute in
  match dv11 with Some ([_; _; _; _; _; _; _; _; _; _; _; _; _; _; Lit a; _; _; _; _; _; _], _) => a | _ => [] end.
Definition a12_8 : list bool := Eval vm_compute in
  match dv11 with Some ([_; _; _; _; _; _; _; _; _; _; _; _; _; _; _; _; Lit a; _; _; _; _], _) => a | _ => [] end.
Definition a12_9 : list bool := Eval vm_compute in
  match dv11 with Some ([_; _; _; _; _; _; _; _; _; _; _; _; _; _; _; _; _; _; Lit a; _; _], _) => a | _ => [] end.
Definition a12_10 : list bool := Eval vm_compute in
  match dv11 with Some ([_; _; _; _; _; _; _; _; _; _; _; _; _; _; _; _; _; _; _; _; Lit a], _) => a | _ => [] end.
Definition P12_1 : list bool := Eval vm_compute in
  match dv11 with Some ([_; Rep p _; _; _; _; _; _; _; _; _; _; _; _; _; _; _; _; _; _; _; _], _) => p | _ => [] end.
Definition P12_2 : list bool := Eval vm_compute in
  match dv11 with Some ([_; _; _; Rep p _; _; _; _; _; _; _; _; _; _; _; _; _; _; _; _; _; _], _) => p | _ => [] end.
Definition P12_3 : list bool := Eval vm_compute in
  match dv11 with Some ([_; _; _; _; _; Rep p _; _; _; _; _; _; _; _; _; _; _; _; _; _; _; _], _) => p | _ => [] end.
Definition P12_4 : list bool := Eval vm_compute in
  match dv11 with Some ([_; _; _; _; _; _; _; Rep p _; _; _; _; _; _; _; _; _; _; _; _; _; _], _) => p | _ => [] end.
Definition P12_5 : list bool := Eval vm_compute in
  match dv11 with Some ([_; _; _; _; _; _; _; _; _; Rep p _; _; _; _; _; _; _; _; _; _; _; _], _) => p | _ => [] end.
Definition P12_6 : list bool := Eval vm_compute in
  match dv11 with Some ([_; _; _; _; _; _; _; _; _; _; _; Rep p _; _; _; _; _; _; _; _; _; _], _) => p | _ => [] end.
Definition P12_7 : list bool := Eval vm_compute in
  match dv11 with Some ([_; _; _; _; _; _; _; _; _; _; _; _; _; Rep p _; _; _; _; _; _; _; _], _) => p | _ => [] end.
Definition P12_8 : list bool := Eval vm_compute in
  match dv11 with Some ([_; _; _; _; _; _; _; _; _; _; _; _; _; _; _; Rep p _; _; _; _; _; _], _) => p | _ => [] end.
Definition P12_9 : list bool := Eval vm_compute in
  match dv11 with Some ([_; _; _; _; _; _; _; _; _; _; _; _; _; _; _; _; _; Rep p _; _; _; _], _) => p | _ => [] end.
Definition P12_10 : list bool := Eval vm_compute in
  match dv11 with Some ([_; _; _; _; _; _; _; _; _; _; _; _; _; _; _; _; _; _; _; Rep p _; _], _) => p | _ => [] end.
Definition r12 : N := Eval vm_compute in match dv11 with Some (_, r) => r | None => 9%N end.
Definition je12 : nat := Eval vm_compute in 3 + N.to_nat r12.

Lemma dv11_ok : forall G x1 x2 x3 x4 x5 x6 x7 x8 x9,
  dmB 3 [Lit [false; false; true; false]; Rep (rp [false; true] 3) G; Lit (rp [false; true] 0 ++
    k11_0); Rep (rp kk11_1 3) x1; Lit (rp kk11_1 0 ++ k11_1); Rep (rp kk11_2 3) x2; Lit (rp kk11_2 1
    ++ k11_2); Rep (rp kk11_3 3) x3; Lit (rp kk11_3 0 ++ k11_3); Rep (rp kk11_4 3) x4; Lit (rp
    kk11_4 2 ++ k11_4); Rep (rp kk11_5 3) x5; Lit (rp kk11_5 0 ++ k11_5); Rep (rp kk11_6 3) x6; Lit
    (rp kk11_6 1 ++ k11_6); Rep (rp kk11_7 3) x7; Lit (rp kk11_7 0 ++ k11_7); Rep (rp kk11_8 3) x8;
    Lit (rp kk11_8 1 ++ k11_8); Rep (rp kk11_9 3) x9; Lit (rp kk11_9 2 ++ k11_9 ++ ab11)] tp11 =
  Some ([Lit a12_0; Rep P12_1 G; Lit a12_1; Rep P12_2 x1; Lit a12_2; Rep P12_3 x2; Lit a12_3; Rep
    P12_4 x3; Lit a12_4; Rep P12_5 x4; Lit a12_5; Rep P12_6 x5; Lit a12_6; Rep P12_7 x6; Lit a12_7;
    Rep P12_8 x7; Lit a12_8; Rep P12_9 x8; Lit a12_9; Rep P12_10 x9; Lit a12_10], r12).
Proof. intros G x1 x2 x3 x4 x5 x6 x7 x8 x9. vm_compute. reflexivity. Qed.

Lemma tp11_lt : (tp11 < 3)%N.
Proof. reflexivity. Qed.

(** ** Level 12 *)

Definition b12 (d1 d2 d3 d4 d5 d6 d7 d8 d9 d10 : nat) : list bool :=
  den [Lit a12_0; Rep P12_1 d1; Lit a12_1; Rep P12_2 d2; Lit a12_2; Rep P12_3 d3; Lit a12_3; Rep P12_4
    d4; Lit a12_4; Rep P12_5 d5; Lit a12_5; Rep P12_6 d6; Lit a12_6; Rep P12_7 d7; Lit a12_7; Rep
    P12_8 d8; Lit a12_8; Rep P12_9 d9; Lit a12_9; Rep P12_10 d10; Lit a12_10].

Definition c12_1 : nat := (2 * bval (b11 c11_1 c11_2 c11_3 c11_4 c11_5 c11_6 c11_7 c11_8 c11_9)) / 3.
Definition c12_2 : nat := ((c11_1 - (cc11_1 + 1 + jj11_1)) / kq11_1) / 3.
Definition c12_3 : nat := ((c11_2 - (cc11_2 + 1 + jj11_2)) / kq11_2) / 3.
Definition c12_4 : nat := ((c11_3 - (cc11_3 + 1 + jj11_3)) / kq11_3) / 3.
Definition c12_5 : nat := ((c11_4 - (cc11_4 + 1 + jj11_4)) / kq11_4) / 3.
Definition c12_6 : nat := ((c11_5 - (cc11_5 + 1 + jj11_5)) / kq11_5) / 3.
Definition c12_7 : nat := ((c11_6 - (cc11_6 + 1 + jj11_6)) / kq11_6) / 3.
Definition c12_8 : nat := ((c11_7 - (cc11_7 + 1 + jj11_7)) / kq11_7) / 3.
Definition c12_9 : nat := ((c11_8 - (cc11_8 + 1 + jj11_8)) / kq11_8) / 3.
Definition c12_10 : nat := ((c11_9 - (cc11_9 + 1 + jj11_9)) / kq11_9) / 3.

Lemma ET11 : 2 * bval (b11 c11_1 c11_2 c11_3 c11_4 c11_5 c11_6 c11_7 c11_8 c11_9) = c12_1 * 3 + 0.
Proof. pose proof T11_res as H. unfold vT11 in H. unfold c12_1. gl (bval (b11 c11_1 c11_2 c11_3 c11_4 c11_5 c11_6 c11_7 c11_8 c11_9)). Qed.

Lemma EC11_1 : c11_1 = cc11_1 + ((c12_2 * 3 + 0) * kq11_1 + jj11_1) + 1.
Proof.
  pose proof c11_1_res as H. pose proof c11_1_res2 as H2. pose proof c11_1_lb as Hb.
  unfold rc11_1 in H. unfold rb11_1 in H2. unfold lb11_1 in Hb.
  unfold c12_2, cc11_1, kq11_1, jj11_1. cbn [Z.of_N] in H, H2, Hb. gl c11_1.
Qed.

Lemma EC11_2 : c11_2 = cc11_2 + ((c12_3 * 3 + 1) * kq11_2 + jj11_2) + 1.
Proof.
  pose proof c11_2_res as H. pose proof c11_2_res2 as H2. pose proof c11_2_lb as Hb.
  unfold rc11_2 in H. unfold rb11_2 in H2. unfold lb11_2 in Hb.
  unfold c12_3, cc11_2, kq11_2, jj11_2. cbn [Z.of_N] in H, H2, Hb. gl c11_2.
Qed.

Lemma EC11_3 : c11_3 = cc11_3 + ((c12_4 * 3 + 0) * kq11_3 + jj11_3) + 1.
Proof.
  pose proof c11_3_res as H. pose proof c11_3_res2 as H2. pose proof c11_3_lb as Hb.
  unfold rc11_3 in H. unfold rb11_3 in H2. unfold lb11_3 in Hb.
  unfold c12_4, cc11_3, kq11_3, jj11_3. cbn [Z.of_N] in H, H2, Hb. gl c11_3.
Qed.

Lemma EC11_4 : c11_4 = cc11_4 + ((c12_5 * 3 + 2) * kq11_4 + jj11_4) + 1.
Proof.
  pose proof c11_4_res as H. pose proof c11_4_res2 as H2. pose proof c11_4_lb as Hb.
  unfold rc11_4 in H. unfold rb11_4 in H2. unfold lb11_4 in Hb.
  unfold c12_5, cc11_4, kq11_4, jj11_4. cbn [Z.of_N] in H, H2, Hb. gl c11_4.
Qed.

Lemma EC11_5 : c11_5 = cc11_5 + ((c12_6 * 3 + 0) * kq11_5 + jj11_5) + 1.
Proof.
  pose proof c11_5_res as H. pose proof c11_5_res2 as H2. pose proof c11_5_lb as Hb.
  unfold rc11_5 in H. unfold rb11_5 in H2. unfold lb11_5 in Hb.
  unfold c12_6, cc11_5, kq11_5, jj11_5. cbn [Z.of_N] in H, H2, Hb. gl c11_5.
Qed.

Lemma EC11_6 : c11_6 = cc11_6 + ((c12_7 * 3 + 1) * kq11_6 + jj11_6) + 1.
Proof.
  pose proof c11_6_res as H. pose proof c11_6_res2 as H2. pose proof c11_6_lb as Hb.
  unfold rc11_6 in H. unfold rb11_6 in H2. unfold lb11_6 in Hb.
  unfold c12_7, cc11_6, kq11_6, jj11_6. cbn [Z.of_N] in H, H2, Hb. gl c11_6.
Qed.

Lemma EC11_7 : c11_7 = cc11_7 + ((c12_8 * 3 + 0) * kq11_7 + jj11_7) + 1.
Proof.
  pose proof c11_7_res as H. pose proof c11_7_res2 as H2. pose proof c11_7_lb as Hb.
  unfold rc11_7 in H. unfold rb11_7 in H2. unfold lb11_7 in Hb.
  unfold c12_8, cc11_7, kq11_7, jj11_7. cbn [Z.of_N] in H, H2, Hb. gl c11_7.
Qed.

Lemma EC11_8 : c11_8 = cc11_8 + ((c12_9 * 3 + 1) * kq11_8 + jj11_8) + 1.
Proof.
  pose proof c11_8_res as H. pose proof c11_8_res2 as H2. pose proof c11_8_lb as Hb.
  unfold rc11_8 in H. unfold rb11_8 in H2. unfold lb11_8 in Hb.
  unfold c12_9, cc11_8, kq11_8, jj11_8. cbn [Z.of_N] in H, H2, Hb. gl c11_8.
Qed.

Lemma EC11_9 : c11_9 = cc11_9 + ((c12_10 * 3 + 2) * kq11_9 + jj11_9) + 1.
Proof.
  pose proof c11_9_res as H. pose proof c11_9_res2 as H2. pose proof c11_9_lb as Hb.
  unfold rc11_9 in H. unfold rb11_9 in H2. unfold lb11_9 in Hb.
  unfold c12_10, cc11_9, kq11_9, jj11_9. cbn [Z.of_N] in H, H2, Hb. gl c11_9.
Qed.

Definition u12 : nat :=
  2 + 2 * bval (b11 (cc11_1 + ((c12_2 * 3 + 0) * kq11_1 + jj11_1) + 1) (cc11_2 + ((c12_3 * 3 + 1) *
    kq11_2 + jj11_2) + 1) (cc11_3 + ((c12_4 * 3 + 0) * kq11_3 + jj11_3) + 1) (cc11_4 + ((c12_5 * 3 +
    2) * kq11_4 + jj11_4) + 1) (cc11_5 + ((c12_6 * 3 + 0) * kq11_5 + jj11_5) + 1) (cc11_6 + ((c12_7
    * 3 + 1) * kq11_6 + jj11_6) + 1) (cc11_7 + ((c12_8 * 3 + 0) * kq11_7 + jj11_7) + 1) (cc11_8 +
    ((c12_9 * 3 + 1) * kq11_8 + jj11_8) + 1) (cc11_9 + ((c12_10 * 3 + 2) * kq11_9 + jj11_9) + 1)) +
    lc11 (c12_2 * 3 + 0) (c12_3 * 3 + 1) (c12_4 * 3 + 0) (c12_5 * 3 + 2) (c12_6 * 3 + 0) (c12_7 * 3
    + 1) (c12_8 * 3 + 0) (c12_9 * 3 + 1) (c12_10 * 3 + 2).

Theorem lvl12 : Lvl je12 (b12 c12_1 c12_2 c12_3 c12_4 c12_5 c12_6 c12_7 c12_8 c12_9 c12_10) u12 w12.
Proof.
  pose proof lvl11 as H. pose proof ET11 as HT.
  rewrite EC11_1 in H, HT.
  rewrite EC11_2 in H, HT.
  rewrite EC11_3 in H, HT.
  rewrite EC11_4 in H, HT.
  rewrite EC11_5 in H, HT.
  rewrite EC11_6 in H, HT.
  rewrite EC11_7 in H, HT.
  rewrite EC11_8 in H, HT.
  rewrite EC11_9 in H, HT.
  apply (level_next_top _ (b11 (cc11_1 + ((c12_2 * 3 + 0) * kq11_1 + jj11_1) + 1) (cc11_2 + ((c12_3 *
    3 + 1) * kq11_2 + jj11_2) + 1) (cc11_3 + ((c12_4 * 3 + 0) * kq11_3 + jj11_3) + 1) (cc11_4 +
    ((c12_5 * 3 + 2) * kq11_4 + jj11_4) + 1) (cc11_5 + ((c12_6 * 3 + 0) * kq11_5 + jj11_5) + 1)
    (cc11_6 + ((c12_7 * 3 + 1) * kq11_6 + jj11_6) + 1) (cc11_7 + ((c12_8 * 3 + 0) * kq11_7 + jj11_7)
    + 1) (cc11_8 + ((c12_9 * 3 + 1) * kq11_8 + jj11_8) + 1) (cc11_9 + ((c12_10 * 3 + 2) * kq11_9 +
    jj11_9) + 1)) _ w11 (Cw11 (c12_2 * 3 + 0) (c12_3 * 3 + 1) (c12_4 * 3 + 0) (c12_5 * 3 + 2) (c12_6
    * 3 + 0) (c12_7 * 3 + 1) (c12_8 * 3 + 0) (c12_9 * 3 + 1) (c12_10 * 3 + 2)) (lc11 (c12_2 * 3 + 0)
    (c12_3 * 3 + 1) (c12_4 * 3 + 0) (c12_5 * 3 + 2) (c12_6 * 3 + 0) (c12_7 * 3 + 1) (c12_8 * 3 + 0)
    (c12_9 * 3 + 1) (c12_10 * 3 + 2)) tp11 (b12 c12_1 c12_2 c12_3 c12_4 c12_5 c12_6 c12_7 c12_8
    c12_9 c12_10) r12 w12 H (Cw11_len _ _ _ _ _ _ _ _ _) tp11_lt (fun k Hk => end11 _ _ _ _ _ _ _ _
    _ _ k Hk)).
  rewrite HT, Zl11_den. apply dmB_sound. apply dv11_ok.
Qed.

(** ** The counts of level 12 modulo 3^2, and lower bounds *)

Definition rc12_1 : N := Eval vm_compute in Z.to_N (((2 * vT11 - 0) / 3) mod 9).
Lemma c12_1_res : (Z.of_nat c12_1 mod Z.of_N 9 = Z.of_N rc12_1)%Z.
Proof.
  pose proof T11_res as H. unfold vT11 in H. unfold c12_1, rc12_1. cbn [Z.of_N].
  gl (bval (b11 c11_1 c11_2 c11_3 c11_4 c11_5 c11_6 c11_7 c11_8 c11_9)).
Qed.
Definition lb12_1 : N := Eval vm_compute in ((2 * lbe11) / 3)%N.
Lemma c12_1_lb : (Z.of_N lb12_1 <= Z.of_nat c12_1)%Z.
Proof.
  pose proof (T11_lb c11_1 c11_2 c11_3 c11_4 c11_5 c11_6 c11_7 c11_8 c11_9) as H. unfold lbe11 in H. unfold c12_1, lb12_1.
  cbn [Z.of_N] in *. gl (bval (b11 c11_1 c11_2 c11_3 c11_4 c11_5 c11_6 c11_7 c11_8 c11_9)).
Qed.
Definition rb12_1 : N := Eval vm_compute in Z.to_N (((2 * Z.of_N t2_11 - 0) * 11) mod 32).
Lemma c12_1_res2 : (Z.of_nat c12_1 mod Z.of_N 32 = Z.of_N rb12_1)%Z.
Proof.
  pose proof T11_res as H. unfold vT11 in H.
  pose proof (T11_low c11_1 c11_2 c11_3 c11_4 c11_5 c11_6 c11_7 c11_8 c11_9) as H2. unfold t2_11 in H2.
  unfold c12_1, rb12_1. cbn [Z.of_N] in *. gl (bval (b11 c11_1 c11_2 c11_3 c11_4 c11_5 c11_6 c11_7 c11_8 c11_9)).
Qed.

Definition rc12_2 : N := Eval vm_compute in
  Z.to_N (((((Z.of_N rc11_1 - (Z.of_nat cc11_1 + 1 + Z.of_nat jj11_1)) * 1) mod 27) / 3) mod 9).
Definition lb12_2 : N := Eval vm_compute in (((lb11_1 - (N.of_nat cc11_1 + 1 + N.of_nat jj11_1)) / 1) / 3)%N.
Definition rb12_2 : N := Eval vm_compute in
  Z.to_N (((((Z.of_N rb11_1 - (Z.of_nat cc11_1 + 1 + Z.of_nat jj11_1)) mod 32) / 1 - 0) * 11) mod 32).
Lemma c12_2_res : (Z.of_nat c12_2 mod Z.of_N 9 = Z.of_N rc12_2)%Z.
Proof.
  pose proof c11_1_res as H. pose proof c11_1_res2 as H2. pose proof c11_1_lb as Hb.
  unfold rc11_1 in H. unfold rb11_1 in H2. unfold lb11_1 in Hb.
  unfold c12_2, rc12_2, cc11_1, kq11_1, jj11_1. cbn [Z.of_N] in *. gl c11_1.
Qed.
Lemma c12_2_res2 : (Z.of_nat c12_2 mod Z.of_N 32 = Z.of_N rb12_2)%Z.
Proof.
  pose proof c11_1_res as H. pose proof c11_1_res2 as H2. pose proof c11_1_lb as Hb.
  unfold rc11_1 in H. unfold rb11_1 in H2. unfold lb11_1 in Hb.
  unfold c12_2, rb12_2, cc11_1, kq11_1, jj11_1. cbn [Z.of_N] in *. gl c11_1.
Qed.
Lemma c12_2_lb : (Z.of_N lb12_2 <= Z.of_nat c12_2)%Z.
Proof.
  pose proof c11_1_res as H. pose proof c11_1_res2 as H2. pose proof c11_1_lb as Hb.
  unfold rc11_1 in H. unfold rb11_1 in H2. unfold lb11_1 in Hb.
  unfold c12_2, lb12_2, cc11_1, kq11_1, jj11_1. cbn [Z.of_N] in *. gl c11_1.
Qed.

Definition rc12_3 : N := Eval vm_compute in
  Z.to_N (((((Z.of_N rc11_2 - (Z.of_nat cc11_2 + 1 + Z.of_nat jj11_2)) * 1) mod 27) / 3) mod 9).
Definition lb12_3 : N := Eval vm_compute in (((lb11_2 - (N.of_nat cc11_2 + 1 + N.of_nat jj11_2)) / 1) / 3)%N.
Definition rb12_3 : N := Eval vm_compute in
  Z.to_N (((((Z.of_N rb11_2 - (Z.of_nat cc11_2 + 1 + Z.of_nat jj11_2)) mod 32) / 1 - 1) * 11) mod 32).
Lemma c12_3_res : (Z.of_nat c12_3 mod Z.of_N 9 = Z.of_N rc12_3)%Z.
Proof.
  pose proof c11_2_res as H. pose proof c11_2_res2 as H2. pose proof c11_2_lb as Hb.
  unfold rc11_2 in H. unfold rb11_2 in H2. unfold lb11_2 in Hb.
  unfold c12_3, rc12_3, cc11_2, kq11_2, jj11_2. cbn [Z.of_N] in *. gl c11_2.
Qed.
Lemma c12_3_res2 : (Z.of_nat c12_3 mod Z.of_N 32 = Z.of_N rb12_3)%Z.
Proof.
  pose proof c11_2_res as H. pose proof c11_2_res2 as H2. pose proof c11_2_lb as Hb.
  unfold rc11_2 in H. unfold rb11_2 in H2. unfold lb11_2 in Hb.
  unfold c12_3, rb12_3, cc11_2, kq11_2, jj11_2. cbn [Z.of_N] in *. gl c11_2.
Qed.
Lemma c12_3_lb : (Z.of_N lb12_3 <= Z.of_nat c12_3)%Z.
Proof.
  pose proof c11_2_res as H. pose proof c11_2_res2 as H2. pose proof c11_2_lb as Hb.
  unfold rc11_2 in H. unfold rb11_2 in H2. unfold lb11_2 in Hb.
  unfold c12_3, lb12_3, cc11_2, kq11_2, jj11_2. cbn [Z.of_N] in *. gl c11_2.
Qed.

Definition rc12_4 : N := Eval vm_compute in
  Z.to_N (((((Z.of_N rc11_3 - (Z.of_nat cc11_3 + 1 + Z.of_nat jj11_3)) * 1) mod 27) / 3) mod 9).
Definition lb12_4 : N := Eval vm_compute in (((lb11_3 - (N.of_nat cc11_3 + 1 + N.of_nat jj11_3)) / 1) / 3)%N.
Definition rb12_4 : N := Eval vm_compute in
  Z.to_N (((((Z.of_N rb11_3 - (Z.of_nat cc11_3 + 1 + Z.of_nat jj11_3)) mod 32) / 1 - 0) * 11) mod 32).
Lemma c12_4_res : (Z.of_nat c12_4 mod Z.of_N 9 = Z.of_N rc12_4)%Z.
Proof.
  pose proof c11_3_res as H. pose proof c11_3_res2 as H2. pose proof c11_3_lb as Hb.
  unfold rc11_3 in H. unfold rb11_3 in H2. unfold lb11_3 in Hb.
  unfold c12_4, rc12_4, cc11_3, kq11_3, jj11_3. cbn [Z.of_N] in *. gl c11_3.
Qed.
Lemma c12_4_res2 : (Z.of_nat c12_4 mod Z.of_N 32 = Z.of_N rb12_4)%Z.
Proof.
  pose proof c11_3_res as H. pose proof c11_3_res2 as H2. pose proof c11_3_lb as Hb.
  unfold rc11_3 in H. unfold rb11_3 in H2. unfold lb11_3 in Hb.
  unfold c12_4, rb12_4, cc11_3, kq11_3, jj11_3. cbn [Z.of_N] in *. gl c11_3.
Qed.
Lemma c12_4_lb : (Z.of_N lb12_4 <= Z.of_nat c12_4)%Z.
Proof.
  pose proof c11_3_res as H. pose proof c11_3_res2 as H2. pose proof c11_3_lb as Hb.
  unfold rc11_3 in H. unfold rb11_3 in H2. unfold lb11_3 in Hb.
  unfold c12_4, lb12_4, cc11_3, kq11_3, jj11_3. cbn [Z.of_N] in *. gl c11_3.
Qed.

Definition rc12_5 : N := Eval vm_compute in
  Z.to_N (((((Z.of_N rc11_4 - (Z.of_nat cc11_4 + 1 + Z.of_nat jj11_4)) * 1) mod 27) / 3) mod 9).
Definition lb12_5 : N := Eval vm_compute in (((lb11_4 - (N.of_nat cc11_4 + 1 + N.of_nat jj11_4)) / 1) / 3)%N.
Definition rb12_5 : N := Eval vm_compute in
  Z.to_N (((((Z.of_N rb11_4 - (Z.of_nat cc11_4 + 1 + Z.of_nat jj11_4)) mod 32) / 1 - 2) * 11) mod 32).
Lemma c12_5_res : (Z.of_nat c12_5 mod Z.of_N 9 = Z.of_N rc12_5)%Z.
Proof.
  pose proof c11_4_res as H. pose proof c11_4_res2 as H2. pose proof c11_4_lb as Hb.
  unfold rc11_4 in H. unfold rb11_4 in H2. unfold lb11_4 in Hb.
  unfold c12_5, rc12_5, cc11_4, kq11_4, jj11_4. cbn [Z.of_N] in *. gl c11_4.
Qed.
Lemma c12_5_res2 : (Z.of_nat c12_5 mod Z.of_N 32 = Z.of_N rb12_5)%Z.
Proof.
  pose proof c11_4_res as H. pose proof c11_4_res2 as H2. pose proof c11_4_lb as Hb.
  unfold rc11_4 in H. unfold rb11_4 in H2. unfold lb11_4 in Hb.
  unfold c12_5, rb12_5, cc11_4, kq11_4, jj11_4. cbn [Z.of_N] in *. gl c11_4.
Qed.
Lemma c12_5_lb : (Z.of_N lb12_5 <= Z.of_nat c12_5)%Z.
Proof.
  pose proof c11_4_res as H. pose proof c11_4_res2 as H2. pose proof c11_4_lb as Hb.
  unfold rc11_4 in H. unfold rb11_4 in H2. unfold lb11_4 in Hb.
  unfold c12_5, lb12_5, cc11_4, kq11_4, jj11_4. cbn [Z.of_N] in *. gl c11_4.
Qed.

Definition rc12_6 : N := Eval vm_compute in
  Z.to_N (((((Z.of_N rc11_5 - (Z.of_nat cc11_5 + 1 + Z.of_nat jj11_5)) * 1) mod 27) / 3) mod 9).
Definition lb12_6 : N := Eval vm_compute in (((lb11_5 - (N.of_nat cc11_5 + 1 + N.of_nat jj11_5)) / 1) / 3)%N.
Definition rb12_6 : N := Eval vm_compute in
  Z.to_N (((((Z.of_N rb11_5 - (Z.of_nat cc11_5 + 1 + Z.of_nat jj11_5)) mod 16) / 1 - 0) * 11) mod 16).
Lemma c12_6_res : (Z.of_nat c12_6 mod Z.of_N 9 = Z.of_N rc12_6)%Z.
Proof.
  pose proof c11_5_res as H. pose proof c11_5_res2 as H2. pose proof c11_5_lb as Hb.
  unfold rc11_5 in H. unfold rb11_5 in H2. unfold lb11_5 in Hb.
  unfold c12_6, rc12_6, cc11_5, kq11_5, jj11_5. cbn [Z.of_N] in *. gl c11_5.
Qed.
Lemma c12_6_res2 : (Z.of_nat c12_6 mod Z.of_N 16 = Z.of_N rb12_6)%Z.
Proof.
  pose proof c11_5_res as H. pose proof c11_5_res2 as H2. pose proof c11_5_lb as Hb.
  unfold rc11_5 in H. unfold rb11_5 in H2. unfold lb11_5 in Hb.
  unfold c12_6, rb12_6, cc11_5, kq11_5, jj11_5. cbn [Z.of_N] in *. gl c11_5.
Qed.
Lemma c12_6_lb : (Z.of_N lb12_6 <= Z.of_nat c12_6)%Z.
Proof.
  pose proof c11_5_res as H. pose proof c11_5_res2 as H2. pose proof c11_5_lb as Hb.
  unfold rc11_5 in H. unfold rb11_5 in H2. unfold lb11_5 in Hb.
  unfold c12_6, lb12_6, cc11_5, kq11_5, jj11_5. cbn [Z.of_N] in *. gl c11_5.
Qed.

Definition rc12_7 : N := Eval vm_compute in
  Z.to_N (((((Z.of_N rc11_6 - (Z.of_nat cc11_6 + 1 + Z.of_nat jj11_6)) * 1) mod 27) / 3) mod 9).
Definition lb12_7 : N := Eval vm_compute in (((lb11_6 - (N.of_nat cc11_6 + 1 + N.of_nat jj11_6)) / 1) / 3)%N.
Definition rb12_7 : N := Eval vm_compute in
  Z.to_N (((((Z.of_N rb11_6 - (Z.of_nat cc11_6 + 1 + Z.of_nat jj11_6)) mod 32) / 1 - 1) * 11) mod 32).
Lemma c12_7_res : (Z.of_nat c12_7 mod Z.of_N 9 = Z.of_N rc12_7)%Z.
Proof.
  pose proof c11_6_res as H. pose proof c11_6_res2 as H2. pose proof c11_6_lb as Hb.
  unfold rc11_6 in H. unfold rb11_6 in H2. unfold lb11_6 in Hb.
  unfold c12_7, rc12_7, cc11_6, kq11_6, jj11_6. cbn [Z.of_N] in *. gl c11_6.
Qed.
Lemma c12_7_res2 : (Z.of_nat c12_7 mod Z.of_N 32 = Z.of_N rb12_7)%Z.
Proof.
  pose proof c11_6_res as H. pose proof c11_6_res2 as H2. pose proof c11_6_lb as Hb.
  unfold rc11_6 in H. unfold rb11_6 in H2. unfold lb11_6 in Hb.
  unfold c12_7, rb12_7, cc11_6, kq11_6, jj11_6. cbn [Z.of_N] in *. gl c11_6.
Qed.
Lemma c12_7_lb : (Z.of_N lb12_7 <= Z.of_nat c12_7)%Z.
Proof.
  pose proof c11_6_res as H. pose proof c11_6_res2 as H2. pose proof c11_6_lb as Hb.
  unfold rc11_6 in H. unfold rb11_6 in H2. unfold lb11_6 in Hb.
  unfold c12_7, lb12_7, cc11_6, kq11_6, jj11_6. cbn [Z.of_N] in *. gl c11_6.
Qed.

Definition rc12_8 : N := Eval vm_compute in
  Z.to_N (((((Z.of_N rc11_7 - (Z.of_nat cc11_7 + 1 + Z.of_nat jj11_7)) * 1) mod 27) / 3) mod 9).
Definition lb12_8 : N := Eval vm_compute in (((lb11_7 - (N.of_nat cc11_7 + 1 + N.of_nat jj11_7)) / 1) / 3)%N.
Definition rb12_8 : N := Eval vm_compute in
  Z.to_N (((((Z.of_N rb11_7 - (Z.of_nat cc11_7 + 1 + Z.of_nat jj11_7)) mod 32) / 1 - 0) * 11) mod 32).
Lemma c12_8_res : (Z.of_nat c12_8 mod Z.of_N 9 = Z.of_N rc12_8)%Z.
Proof.
  pose proof c11_7_res as H. pose proof c11_7_res2 as H2. pose proof c11_7_lb as Hb.
  unfold rc11_7 in H. unfold rb11_7 in H2. unfold lb11_7 in Hb.
  unfold c12_8, rc12_8, cc11_7, kq11_7, jj11_7. cbn [Z.of_N] in *. gl c11_7.
Qed.
Lemma c12_8_res2 : (Z.of_nat c12_8 mod Z.of_N 32 = Z.of_N rb12_8)%Z.
Proof.
  pose proof c11_7_res as H. pose proof c11_7_res2 as H2. pose proof c11_7_lb as Hb.
  unfold rc11_7 in H. unfold rb11_7 in H2. unfold lb11_7 in Hb.
  unfold c12_8, rb12_8, cc11_7, kq11_7, jj11_7. cbn [Z.of_N] in *. gl c11_7.
Qed.
Lemma c12_8_lb : (Z.of_N lb12_8 <= Z.of_nat c12_8)%Z.
Proof.
  pose proof c11_7_res as H. pose proof c11_7_res2 as H2. pose proof c11_7_lb as Hb.
  unfold rc11_7 in H. unfold rb11_7 in H2. unfold lb11_7 in Hb.
  unfold c12_8, lb12_8, cc11_7, kq11_7, jj11_7. cbn [Z.of_N] in *. gl c11_7.
Qed.

Definition rc12_9 : N := Eval vm_compute in
  Z.to_N (((((Z.of_N rc11_8 - (Z.of_nat cc11_8 + 1 + Z.of_nat jj11_8)) * 1) mod 27) / 3) mod 9).
Definition lb12_9 : N := Eval vm_compute in (((lb11_8 - (N.of_nat cc11_8 + 1 + N.of_nat jj11_8)) / 1) / 3)%N.
Definition rb12_9 : N := Eval vm_compute in
  Z.to_N (((((Z.of_N rb11_8 - (Z.of_nat cc11_8 + 1 + Z.of_nat jj11_8)) mod 32) / 1 - 1) * 11) mod 32).
Lemma c12_9_res : (Z.of_nat c12_9 mod Z.of_N 9 = Z.of_N rc12_9)%Z.
Proof.
  pose proof c11_8_res as H. pose proof c11_8_res2 as H2. pose proof c11_8_lb as Hb.
  unfold rc11_8 in H. unfold rb11_8 in H2. unfold lb11_8 in Hb.
  unfold c12_9, rc12_9, cc11_8, kq11_8, jj11_8. cbn [Z.of_N] in *. gl c11_8.
Qed.
Lemma c12_9_res2 : (Z.of_nat c12_9 mod Z.of_N 32 = Z.of_N rb12_9)%Z.
Proof.
  pose proof c11_8_res as H. pose proof c11_8_res2 as H2. pose proof c11_8_lb as Hb.
  unfold rc11_8 in H. unfold rb11_8 in H2. unfold lb11_8 in Hb.
  unfold c12_9, rb12_9, cc11_8, kq11_8, jj11_8. cbn [Z.of_N] in *. gl c11_8.
Qed.
Lemma c12_9_lb : (Z.of_N lb12_9 <= Z.of_nat c12_9)%Z.
Proof.
  pose proof c11_8_res as H. pose proof c11_8_res2 as H2. pose proof c11_8_lb as Hb.
  unfold rc11_8 in H. unfold rb11_8 in H2. unfold lb11_8 in Hb.
  unfold c12_9, lb12_9, cc11_8, kq11_8, jj11_8. cbn [Z.of_N] in *. gl c11_8.
Qed.

Definition rc12_10 : N := Eval vm_compute in
  Z.to_N (((((Z.of_N rc11_9 - (Z.of_nat cc11_9 + 1 + Z.of_nat jj11_9)) * 1) mod 27) / 3) mod 9).
Definition lb12_10 : N := Eval vm_compute in (((lb11_9 - (N.of_nat cc11_9 + 1 + N.of_nat jj11_9)) / 1) / 3)%N.
Definition rb12_10 : N := Eval vm_compute in
  Z.to_N (((((Z.of_N rb11_9 - (Z.of_nat cc11_9 + 1 + Z.of_nat jj11_9)) mod 32) / 1 - 2) * 11) mod 32).
Lemma c12_10_res : (Z.of_nat c12_10 mod Z.of_N 9 = Z.of_N rc12_10)%Z.
Proof.
  pose proof c11_9_res as H. pose proof c11_9_res2 as H2. pose proof c11_9_lb as Hb.
  unfold rc11_9 in H. unfold rb11_9 in H2. unfold lb11_9 in Hb.
  unfold c12_10, rc12_10, cc11_9, kq11_9, jj11_9. cbn [Z.of_N] in *. gl c11_9.
Qed.
Lemma c12_10_res2 : (Z.of_nat c12_10 mod Z.of_N 32 = Z.of_N rb12_10)%Z.
Proof.
  pose proof c11_9_res as H. pose proof c11_9_res2 as H2. pose proof c11_9_lb as Hb.
  unfold rc11_9 in H. unfold rb11_9 in H2. unfold lb11_9 in Hb.
  unfold c12_10, rb12_10, cc11_9, kq11_9, jj11_9. cbn [Z.of_N] in *. gl c11_9.
Qed.
Lemma c12_10_lb : (Z.of_N lb12_10 <= Z.of_nat c12_10)%Z.
Proof.
  pose proof c11_9_res as H. pose proof c11_9_res2 as H2. pose proof c11_9_lb as Hb.
  unfold rc11_9 in H. unfold rb11_9 in H2. unfold lb11_9 in Hb.
  unfold c12_10, lb12_10, cc11_9, kq11_9, jj11_9. cbn [Z.of_N] in *. gl c11_9.
Qed.

(** ** The word of level 12 modulo 3^2 *)

Definition vT12 : Z := Eval vm_compute in
  gv (resW 9 [RL a12_0; RR P12_1 9 rc12_1; RL a12_1; RR P12_2 9 rc12_2; RL a12_2; RR P12_3 9 rc12_3;
    RL a12_3; RR P12_4 9 rc12_4; RL a12_4; RR P12_5 9 rc12_5; RL a12_5; RR P12_6 9 rc12_6; RL a12_6;
    RR P12_7 9 rc12_7; RL a12_7; RR P12_8 9 rc12_8; RL a12_8; RR P12_9 9 rc12_9; RL a12_9; RR P12_10
    9 rc12_10; RL a12_10]).

Lemma T12_res : (Z.of_nat (bval (b12 c12_1 c12_2 c12_3 c12_4 c12_5 c12_6 c12_7 c12_8 c12_9 c12_10)) mod 9 = vT12)%Z.
Proof.
  unfold b12.
  apply (resW_sound 9 [Lit a12_0; Rep P12_1 c12_1; Lit a12_1; Rep P12_2 c12_2; Lit a12_2; Rep P12_3
    c12_3; Lit a12_3; Rep P12_4 c12_4; Lit a12_4; Rep P12_5 c12_5; Lit a12_5; Rep P12_6 c12_6; Lit
    a12_6; Rep P12_7 c12_7; Lit a12_7; Rep P12_8 c12_8; Lit a12_8; Rep P12_9 c12_9; Lit a12_9; Rep
    P12_10 c12_10; Lit a12_10]
           [RL a12_0; RR P12_1 9 rc12_1; RL a12_1; RR P12_2 9 rc12_2; RL a12_2; RR P12_3 9 rc12_3; RL a12_3; RR
            P12_4 9 rc12_4; RL a12_4; RR P12_5 9 rc12_5; RL a12_5; RR P12_6 9 rc12_6; RL a12_6; RR
            P12_7 9 rc12_7; RL a12_7; RR P12_8 9 rc12_8; RL a12_8; RR P12_9 9 rc12_9; RL a12_9; RR
            P12_10 9 rc12_10; RL a12_10]);
    [lia | | vm_compute; reflexivity].
  exact (Forall2_cons _ _ (mL a12_0)
    (Forall2_cons _ _ (mR P12_1 c12_1 9%N rc12_1 c12_1_res)
    (Forall2_cons _ _ (mL a12_1)
    (Forall2_cons _ _ (mR P12_2 c12_2 9%N rc12_2 c12_2_res)
    (Forall2_cons _ _ (mL a12_2)
    (Forall2_cons _ _ (mR P12_3 c12_3 9%N rc12_3 c12_3_res)
    (Forall2_cons _ _ (mL a12_3)
    (Forall2_cons _ _ (mR P12_4 c12_4 9%N rc12_4 c12_4_res)
    (Forall2_cons _ _ (mL a12_4)
    (Forall2_cons _ _ (mR P12_5 c12_5 9%N rc12_5 c12_5_res)
    (Forall2_cons _ _ (mL a12_5)
    (Forall2_cons _ _ (mR P12_6 c12_6 9%N rc12_6 c12_6_res)
    (Forall2_cons _ _ (mL a12_6)
    (Forall2_cons _ _ (mR P12_7 c12_7 9%N rc12_7 c12_7_res)
    (Forall2_cons _ _ (mL a12_7)
    (Forall2_cons _ _ (mR P12_8 c12_8 9%N rc12_8 c12_8_res)
    (Forall2_cons _ _ (mL a12_8)
    (Forall2_cons _ _ (mR P12_9 c12_9 9%N rc12_9 c12_9_res)
    (Forall2_cons _ _ (mL a12_9)
    (Forall2_cons _ _ (mR P12_10 c12_10 9%N rc12_10 c12_10_res)
    (Forall2_cons _ _ (mL a12_10) (Forall2_nil _)))))))))))))))))))))).
Qed.

Definition lbe12 : N := Eval vm_compute in bvalN a12_10.

Lemma T12_lb : forall d1 d2 d3 d4 d5 d6 d7 d8 d9 d10, (Z.of_N lbe12 <= Z.of_nat (bval (b12 d1 d2 d3 d4 d5 d6 d7 d8 d9 d10)))%Z.
Proof.
  intros d1 d2 d3 d4 d5 d6 d7 d8 d9 d10. unfold b12. change lbe12 with (bvalN a12_10).
  exact (lbZ [Lit a12_0; Rep P12_1 d1; Lit a12_1; Rep P12_2 d2; Lit a12_2; Rep P12_3 d3; Lit a12_3;
    Rep P12_4 d4; Lit a12_4; Rep P12_5 d5; Lit a12_5; Rep P12_6 d6; Lit a12_6; Rep P12_7 d7; Lit
    a12_7; Rep P12_8 d8; Lit a12_8; Rep P12_9 d9; Lit a12_9; Rep P12_10 d10] a12_10).
Qed.

Definition t2_12 : N := Eval vm_compute in bvalN a12_0.

Lemma T12_low : forall d1 d2 d3 d4 d5 d6 d7 d8 d9 d10, (Z.of_nat (bval (b12 d1 d2 d3 d4 d5 d6 d7 d8 d9 d10)) mod 16 = Z.of_N t2_12)%Z.
Proof.
  intros d1 d2 d3 d4 d5 d6 d7 d8 d9 d10. unfold b12.
  exact (bval_low_den a12_0 [Rep P12_1 d1; Lit a12_1; Rep P12_2 d2; Lit a12_2; Rep P12_3 d3; Lit
    a12_3; Rep P12_4 d4; Lit a12_4; Rep P12_5 d5; Lit a12_5; Rep P12_6 d6; Lit a12_6; Rep P12_7 d7;
    Lit a12_7; Rep P12_8 d8; Lit a12_8; Rep P12_9 d9; Lit a12_9; Rep P12_10 d10; Lit a12_10]).
Qed.

End L1112b.

Module L1213a.

(** * 1RB1LB_1RC0RD_0LA1RE_0RF1LC_1LA0RB_---1LC: the end phase of level 12

    Level 12 has class 4: the end phase is one computation on the low literal of the counter
    word ([c4cert]), and the word that is added is the complement of the rest of the counter
    word between two literals.  Generated by a script. *)

Import Individual62.
Import T694_levels End694 Sym694 Lev694 Lvl1_694 Eng694 Cert694 Run694 Res694 Gen694.
Import L23 L34 L45 L56 L6i L67a L67b L78a L78b L89a L89b L910a L910b L1011a L1011b L1112a L1112b.
Import Lia Arith PeanoNat Bool NArith ZArith.
Import Coq.Lists.List.
Import ListNotations.

Definition c4_12 := Eval vm_compute in c4cert 6000 6000 je12 a12_0 w12.
Definition s4_12 : nat := Eval vm_compute in match c4_12 with Some (x, _, _, _, _) => x | None => O end.
Definition la12 : nat := Eval vm_compute in match c4_12 with Some (_, x, _, _, _) => x | None => O end.
Definition k12_0 : list bool := Eval vm_compute in match c4_12 with Some (_, _, x, _, _) => x | None => [] end.
Definition ab4_12 : list bool := Eval vm_compute in match c4_12 with Some (_, _, _, x, _) => x | None => [] end.
Definition w13 : list bool := Eval vm_compute in match c4_12 with Some (_, _, _, _, x) => x | None => [] end.
Definition tp12 : N := 0%N.
Definition ab12 : list bool := [].

Lemma c4_12_ok : c4cert 6000 6000 je12 a12_0 w12 = Some (s4_12, la12, k12_0, ab4_12, w13).
Proof. vm_compute. reflexivity. Qed.

Definition rest12 (n1 n2 n3 n4 n5 n6 n7 n8 n9 n10 : nat) : list blk :=
  [Rep P12_1 n1; Lit a12_1; Rep P12_2 n2; Lit a12_2; Rep P12_3 n3; Lit a12_3; Rep P12_4 n4; Lit a12_4;
    Rep P12_5 n5; Lit a12_5; Rep P12_6 n6; Lit a12_6; Rep P12_7 n7; Lit a12_7; Rep P12_8 n8; Lit
    a12_8; Rep P12_9 n9; Lit a12_9; Rep P12_10 n10; Lit a12_10].

Lemma rest12_len : forall n1 n2 n3 n4 n5 n6 n7 n8 n9 n10, length (den (rest12 n1 n2 n3 n4 n5 n6 n7 n8 n9 n10)) = 2 * hlen (rest12 n1 n2 n3 n4 n5 n6 n7 n8 n9 n10).
Proof. intros n1 n2 n3 n4 n5 n6 n7 n8 n9 n10. apply den_len. vm_compute. reflexivity. Qed.

Definition kk12_1 : list bool := map negb P12_1.
Definition k12_1 : list bool := map negb a12_1.
Definition kk12_2 : list bool := map negb P12_2.
Definition k12_2 : list bool := map negb a12_2.
Definition kk12_3 : list bool := map negb P12_3.
Definition k12_3 : list bool := map negb a12_3.
Definition kk12_4 : list bool := map negb P12_4.
Definition k12_4 : list bool := map negb a12_4.
Definition kk12_5 : list bool := map negb P12_5.
Definition k12_5 : list bool := map negb a12_5.
Definition kk12_6 : list bool := map negb P12_6.
Definition k12_6 : list bool := map negb a12_6.
Definition kk12_7 : list bool := map negb P12_7.
Definition k12_7 : list bool := map negb a12_7.
Definition kk12_8 : list bool := map negb P12_8.
Definition k12_8 : list bool := map negb a12_8.
Definition kk12_9 : list bool := map negb P12_9.
Definition k12_9 : list bool := map negb a12_9.
Definition kk12_10 : list bool := map negb P12_10.
Definition k12_10 : list bool := map negb a12_10 ++ ab4_12.

Definition Cw12 (n1 n2 n3 n4 n5 n6 n7 n8 n9 n10 : nat) : list bool :=
  den [Lit k12_0; Rep kk12_1 n1; Lit k12_1; Rep kk12_2 n2; Lit k12_2; Rep kk12_3 n3; Lit k12_3; Rep
    kk12_4 n4; Lit k12_4; Rep kk12_5 n5; Lit k12_5; Rep kk12_6 n6; Lit k12_6; Rep kk12_7 n7; Lit
    k12_7; Rep kk12_8 n8; Lit k12_8; Rep kk12_9 n9; Lit k12_9; Rep kk12_10 n10; Lit k12_10] ++ ab12.
Definition lc12 (n1 n2 n3 n4 n5 n6 n7 n8 n9 n10 : nat) : nat := s4_12 + hlen (rest12 n1 n2 n3 n4 n5 n6 n7 n8 n9 n10) + la12.

Lemma Cw12_eq : forall n1 n2 n3 n4 n5 n6 n7 n8 n9 n10,
  Cw12 n1 n2 n3 n4 n5 n6 n7 n8 n9 n10 = k12_0 ++ map negb (den (rest12 n1 n2 n3 n4 n5 n6 n7 n8 n9 n10)) ++ ab4_12.
Proof.
  intros n1 n2 n3 n4 n5 n6 n7 n8 n9 n10. rewrite negb_den. unfold Cw12, rest12, ab12, kk12_1, kk12_2, kk12_3, kk12_4, kk12_5, kk12_6, kk12_7, kk12_8, kk12_9, kk12_10, k12_1, k12_2, k12_3, k12_4, k12_5, k12_6, k12_7, k12_8, k12_9, k12_10.
  cbn [map nblk den bden]. rewrite ?app_nil_r, <- ?app_assoc. reflexivity.
Qed.

Lemma Cw12_len : forall n1 n2 n3 n4 n5 n6 n7 n8 n9 n10, length (Cw12 n1 n2 n3 n4 n5 n6 n7 n8 n9 n10) = 2 * lc12 n1 n2 n3 n4 n5 n6 n7 n8 n9 n10.
Proof.
  intros n1 n2 n3 n4 n5 n6 n7 n8 n9 n10. rewrite Cw12_eq, !length_app, length_map, rest12_len. unfold lc12.
  assert (H1 : length k12_0 = 2 * s4_12) by (vm_compute; reflexivity).
  assert (H2 : length ab4_12 = 2 * la12) by (vm_compute; reflexivity).
  rewrite H1, H2. lia.
Qed.

Lemma end12 : forall n1 n2 n3 n4 n5 n6 n7 n8 n9 n10 h k, (1 <= h)%nat -> (1 <= k)%nat -> exists n M',
  tickN 3 n (rep10 k ++ c1101 ++ repeat true (3 * h) ++ rep10 je12 ++ c1101 ++
             encb false (b12 n1 n2 n3 n4 n5 n6 n7 n8 n9 n10) ++ w12) =
    Some (Slev M' (3 * (h + lc12 n1 n2 n3 n4 n5 n6 n7 n8 n9 n10) + 1) w13) /\
  Z.of_nat M' = (Z.of_nat k +
                 (Z.of_nat (bval (Cw12 n1 n2 n3 n4 n5 n6 n7 n8 n9 n10)) + Z.of_N tp12 * pw4 (lc12 n1 n2 n3 n4 n5 n6 n7 n8 n9 n10)) * pw4 h)%Z.
Proof.
  intros n1 n2 n3 n4 n5 n6 n7 n8 n9 n10 h k Hh Hk.
  destruct (c4cert_sound _ _ _ _ _ _ _ _ _ _ c4_12_ok (den (rest12 n1 n2 n3 n4 n5 n6 n7 n8 n9 n10)) (hlen (rest12 n1 n2 n3 n4 n5 n6 n7 n8 n9 n10)) h
              (rest12_len n1 n2 n3 n4 n5 n6 n7 n8 n9 n10) Hh k Hk) as [n [M' [E D]]].
  exists n, M'. split; [exact E |].
  rewrite D, (Cw12_eq n1 n2 n3 n4 n5 n6 n7 n8 n9 n10). unfold tp12. cbn [Z.of_N]. ring.
Qed.

(** ** What the division needs: which blocks are tripled, and the residues of the counts *)

Definition cfg12_trip : list bool := Eval vm_compute in
  map (fun P => negb (N.eqb (bvalN P mod 3) 0)) [kk12_1; kk12_2; kk12_3; kk12_4; kk12_5; kk12_6; kk12_7; kk12_8; kk12_9; kk12_10].
Definition cfg12_rho : list N := Eval vm_compute in
  [(((rc12_1 + 1594323 - 0%N) * (N.of_nat 1%nat mod 3)) mod 3)%N; (((rc12_2 + 1594323 - 0%N) * (N.of_nat 1%nat mod 3)) mod 3)%N; (((rc12_3 + 1594323 - 0%N) * (N.of_nat 1%nat mod 3)) mod 3)%N; (((rc12_4 + 1594323 - 0%N) * (N.of_nat 1%nat mod 3)) mod 3)%N; (((rc12_5 + 1594323 - 0%N) * (N.of_nat 1%nat mod 3)) mod 3)%N; (((rc12_6 + 1594323 - 0%N) * (N.of_nat 1%nat mod 3)) mod 3)%N; (((rc12_7 + 1594323 - 0%N) * (N.of_nat 1%nat mod 3)) mod 3)%N; (((rc12_8 + 1594323 - 0%N) * (N.of_nat 1%nat mod 3)) mod 3)%N; (((rc12_9 + 1594323 - 0%N) * (N.of_nat 1%nat mod 3)) mod 3)%N; (((rc12_10 + 1594323 - 0%N) * (N.of_nat 1%nat mod 3)) mod 3)%N].
Definition cfg12_k : list nat := Eval vm_compute in [1%nat; 1%nat; 1%nat; 1%nat; 1%nat; 1%nat; 1%nat; 1%nat; 1%nat; 1%nat].
Definition cfg12_j : list nat := Eval vm_compute in [0%nat; 0%nat; 0%nat; 0%nat; 0%nat; 0%nat; 0%nat; 0%nat; 0%nat; 0%nat].
Definition cfg12_rhoT : Z := Eval vm_compute in ((2 * vT12) mod 3)%Z.

End L1213a.

Module L1213b.

(** * 1RB1LB_1RC0RD_0LA1RE_0RF1LC_1LA0RB_---1LC: from level 12 to level 13

    The division by 3 of [0100 (10)^(h-2) C] with the counts as variables, level 13 for the
    real counts, and the residues modulo 3^1 and lower bounds of the counts of level 13.
    Generated by a script. *)

Import Individual62.
Import T694_levels End694 Sym694 Lev694 Lvl1_694 Eng694 Cert694 Run694 Res694 Gen694.
Import L23 L34 L45 L56 L6i L67a L67b L78a L78b L89a L89b L910a L910b L1011a L1011b L1112a L1112b L1213a.
Import Lia Arith PeanoNat Bool NArith ZArith.
Import Coq.Lists.List.
Import ListNotations.

(** ** The division *)

Lemma Zl12_den : forall G x1 x2 x3 x4 x5 x6 x7 x8 x9 x10,
  [false; false; true; false] ++ rep01 (G * 3 + 0) ++ Cw12 (x1 * 3 + 1) (x2 * 3 + 1) (x3 * 3 + 2) (x4 * 3 + 0) (x5 * 3 + 0) (x6 * 3 + 2) (x7 * 3 + 1) (x8 * 3 + 2) (x9 * 3 + 0) (x10 * 3 + 2) =
  den [Lit [false; false; true; false]; Rep (rp [false; true] 3) G; Lit (rp [false; true] 0 ++ k12_0);
    Rep (rp kk12_1 3) x1; Lit (rp kk12_1 1 ++ k12_1); Rep (rp kk12_2 3) x2; Lit (rp kk12_2 1 ++
    k12_2); Rep (rp kk12_3 3) x3; Lit (rp kk12_3 2 ++ k12_3); Rep (rp kk12_4 3) x4; Lit (rp kk12_4 0
    ++ k12_4); Rep (rp kk12_5 3) x5; Lit (rp kk12_5 0 ++ k12_5); Rep (rp kk12_6 3) x6; Lit (rp
    kk12_6 2 ++ k12_6); Rep (rp kk12_7 3) x7; Lit (rp kk12_7 1 ++ k12_7); Rep (rp kk12_8 3) x8; Lit
    (rp kk12_8 2 ++ k12_8); Rep (rp kk12_9 3) x9; Lit (rp kk12_9 0 ++ k12_9); Rep (rp kk12_10 3)
    x10; Lit (rp kk12_10 2 ++ k12_10 ++ ab12)].
Proof.
  intros G x1 x2 x3 x4 x5 x6 x7 x8 x9 x10. unfold Cw12. cbn [den bden].
  change (rep01 (G * 3 + 0)) with (rp [false; true] (G * 3 + 0)).
  rewrite ?rp_add, ?rp_mul, ?app_nil_r, <- ?app_assoc. reflexivity.
Qed.

Definition dv12 := Eval vm_compute in
  dmB 3 [Lit [false; false; true; false]; Rep (rp [false; true] 3) O; Lit (rp [false; true] 0 ++
    k12_0); Rep (rp kk12_1 3) O; Lit (rp kk12_1 1 ++ k12_1); Rep (rp kk12_2 3) O; Lit (rp kk12_2 1
    ++ k12_2); Rep (rp kk12_3 3) O; Lit (rp kk12_3 2 ++ k12_3); Rep (rp kk12_4 3) O; Lit (rp kk12_4
    0 ++ k12_4); Rep (rp kk12_5 3) O; Lit (rp kk12_5 0 ++ k12_5); Rep (rp kk12_6 3) O; Lit (rp
    kk12_6 2 ++ k12_6); Rep (rp kk12_7 3) O; Lit (rp kk12_7 1 ++ k12_7); Rep (rp kk12_8 3) O; Lit
    (rp kk12_8 2 ++ k12_8); Rep (rp kk12_9 3) O; Lit (rp kk12_9 0 ++ k12_9); Rep (rp kk12_10 3) O;
    Lit (rp kk12_10 2 ++ k12_10 ++ ab12)] tp12.
Definition a13_0 : list bool := Eval vm_compute in
  match dv12 with Some ([Lit a; _; _; _; _; _; _; _; _; _; _; _; _; _; _; _; _; _; _; _; _; _; _], _) => a | _ => [] end.
Definition a13_1 : list bool := Eval vm_compute in
  match dv12 with Some ([_; _; Lit a; _; _; _; _; _; _; _; _; _; _; _; _; _; _; _; _; _; _; _; _], _) => a | _ => [] end.
Definition a13_2 : list bool := Eval vm_compute in
  match dv12 with Some ([_; _; _; _; Lit a; _; _; _; _; _; _; _; _; _; _; _; _; _; _; _; _; _; _], _) => a | _ => [] end.
Definition a13_3 : list bool := Eval vm_compute in
  match dv12 with Some ([_; _; _; _; _; _; Lit a; _; _; _; _; _; _; _; _; _; _; _; _; _; _; _; _], _) => a | _ => [] end.
Definition a13_4 : list bool := Eval vm_compute in
  match dv12 with Some ([_; _; _; _; _; _; _; _; Lit a; _; _; _; _; _; _; _; _; _; _; _; _; _; _], _) => a | _ => [] end.
Definition a13_5 : list bool := Eval vm_compute in
  match dv12 with Some ([_; _; _; _; _; _; _; _; _; _; Lit a; _; _; _; _; _; _; _; _; _; _; _; _], _) => a | _ => [] end.
Definition a13_6 : list bool := Eval vm_compute in
  match dv12 with Some ([_; _; _; _; _; _; _; _; _; _; _; _; Lit a; _; _; _; _; _; _; _; _; _; _], _) => a | _ => [] end.
Definition a13_7 : list bool := Eval vm_compute in
  match dv12 with Some ([_; _; _; _; _; _; _; _; _; _; _; _; _; _; Lit a; _; _; _; _; _; _; _; _], _) => a | _ => [] end.
Definition a13_8 : list bool := Eval vm_compute in
  match dv12 with Some ([_; _; _; _; _; _; _; _; _; _; _; _; _; _; _; _; Lit a; _; _; _; _; _; _], _) => a | _ => [] end.
Definition a13_9 : list bool := Eval vm_compute in
  match dv12 with Some ([_; _; _; _; _; _; _; _; _; _; _; _; _; _; _; _; _; _; Lit a; _; _; _; _], _) => a | _ => [] end.
Definition a13_10 : list bool := Eval vm_compute in
  match dv12 with Some ([_; _; _; _; _; _; _; _; _; _; _; _; _; _; _; _; _; _; _; _; Lit a; _; _], _) => a | _ => [] end.
Definition a13_11 : list bool := Eval vm_compute in
  match dv12 with Some ([_; _; _; _; _; _; _; _; _; _; _; _; _; _; _; _; _; _; _; _; _; _; Lit a], _) => a | _ => [] end.
Definition P13_1 : list bool := Eval vm_compute in
  match dv12 with Some ([_; Rep p _; _; _; _; _; _; _; _; _; _; _; _; _; _; _; _; _; _; _; _; _; _], _) => p | _ => [] end.
Definition P13_2 : list bool := Eval vm_compute in
  match dv12 with Some ([_; _; _; Rep p _; _; _; _; _; _; _; _; _; _; _; _; _; _; _; _; _; _; _; _], _) => p | _ => [] end.
Definition P13_3 : list bool := Eval vm_compute in
  match dv12 with Some ([_; _; _; _; _; Rep p _; _; _; _; _; _; _; _; _; _; _; _; _; _; _; _; _; _], _) => p | _ => [] end.
Definition P13_4 : list bool := Eval vm_compute in
  match dv12 with Some ([_; _; _; _; _; _; _; Rep p _; _; _; _; _; _; _; _; _; _; _; _; _; _; _; _], _) => p | _ => [] end.
Definition P13_5 : list bool := Eval vm_compute in
  match dv12 with Some ([_; _; _; _; _; _; _; _; _; Rep p _; _; _; _; _; _; _; _; _; _; _; _; _; _], _) => p | _ => [] end.
Definition P13_6 : list bool := Eval vm_compute in
  match dv12 with Some ([_; _; _; _; _; _; _; _; _; _; _; Rep p _; _; _; _; _; _; _; _; _; _; _; _], _) => p | _ => [] end.
Definition P13_7 : list bool := Eval vm_compute in
  match dv12 with Some ([_; _; _; _; _; _; _; _; _; _; _; _; _; Rep p _; _; _; _; _; _; _; _; _; _], _) => p | _ => [] end.
Definition P13_8 : list bool := Eval vm_compute in
  match dv12 with Some ([_; _; _; _; _; _; _; _; _; _; _; _; _; _; _; Rep p _; _; _; _; _; _; _; _], _) => p | _ => [] end.
Definition P13_9 : list bool := Eval vm_compute in
  match dv12 with Some ([_; _; _; _; _; _; _; _; _; _; _; _; _; _; _; _; _; Rep p _; _; _; _; _; _], _) => p | _ => [] end.
Definition P13_10 : list bool := Eval vm_compute in
  match dv12 with Some ([_; _; _; _; _; _; _; _; _; _; _; _; _; _; _; _; _; _; _; Rep p _; _; _; _], _) => p | _ => [] end.
Definition P13_11 : list bool := Eval vm_compute in
  match dv12 with Some ([_; _; _; _; _; _; _; _; _; _; _; _; _; _; _; _; _; _; _; _; _; Rep p _; _], _) => p | _ => [] end.
Definition r13 : N := Eval vm_compute in match dv12 with Some (_, r) => r | None => 9%N end.
Definition je13 : nat := Eval vm_compute in 3 + N.to_nat r13.

Lemma dv12_ok : forall G x1 x2 x3 x4 x5 x6 x7 x8 x9 x10,
  dmB 3 [Lit [false; false; true; false]; Rep (rp [false; true] 3) G; Lit (rp [false; true] 0 ++
    k12_0); Rep (rp kk12_1 3) x1; Lit (rp kk12_1 1 ++ k12_1); Rep (rp kk12_2 3) x2; Lit (rp kk12_2 1
    ++ k12_2); Rep (rp kk12_3 3) x3; Lit (rp kk12_3 2 ++ k12_3); Rep (rp kk12_4 3) x4; Lit (rp
    kk12_4 0 ++ k12_4); Rep (rp kk12_5 3) x5; Lit (rp kk12_5 0 ++ k12_5); Rep (rp kk12_6 3) x6; Lit
    (rp kk12_6 2 ++ k12_6); Rep (rp kk12_7 3) x7; Lit (rp kk12_7 1 ++ k12_7); Rep (rp kk12_8 3) x8;
    Lit (rp kk12_8 2 ++ k12_8); Rep (rp kk12_9 3) x9; Lit (rp kk12_9 0 ++ k12_9); Rep (rp kk12_10 3)
    x10; Lit (rp kk12_10 2 ++ k12_10 ++ ab12)] tp12 =
  Some ([Lit a13_0; Rep P13_1 G; Lit a13_1; Rep P13_2 x1; Lit a13_2; Rep P13_3 x2; Lit a13_3; Rep
    P13_4 x3; Lit a13_4; Rep P13_5 x4; Lit a13_5; Rep P13_6 x5; Lit a13_6; Rep P13_7 x6; Lit a13_7;
    Rep P13_8 x7; Lit a13_8; Rep P13_9 x8; Lit a13_9; Rep P13_10 x9; Lit a13_10; Rep P13_11 x10; Lit
    a13_11], r13).
Proof. intros G x1 x2 x3 x4 x5 x6 x7 x8 x9 x10. vm_compute. reflexivity. Qed.

Lemma tp12_lt : (tp12 < 3)%N.
Proof. reflexivity. Qed.

(** ** Level 13 *)

Definition b13 (d1 d2 d3 d4 d5 d6 d7 d8 d9 d10 d11 : nat) : list bool :=
  den [Lit a13_0; Rep P13_1 d1; Lit a13_1; Rep P13_2 d2; Lit a13_2; Rep P13_3 d3; Lit a13_3; Rep P13_4
    d4; Lit a13_4; Rep P13_5 d5; Lit a13_5; Rep P13_6 d6; Lit a13_6; Rep P13_7 d7; Lit a13_7; Rep
    P13_8 d8; Lit a13_8; Rep P13_9 d9; Lit a13_9; Rep P13_10 d10; Lit a13_10; Rep P13_11 d11; Lit
    a13_11].

Definition c13_1 : nat := (2 * bval (b12 c12_1 c12_2 c12_3 c12_4 c12_5 c12_6 c12_7 c12_8 c12_9 c12_10)) / 3.
Definition c13_2 : nat := c12_1 / 3.
Definition c13_3 : nat := c12_2 / 3.
Definition c13_4 : nat := c12_3 / 3.
Definition c13_5 : nat := c12_4 / 3.
Definition c13_6 : nat := c12_5 / 3.
Definition c13_7 : nat := c12_6 / 3.
Definition c13_8 : nat := c12_7 / 3.
Definition c13_9 : nat := c12_8 / 3.
Definition c13_10 : nat := c12_9 / 3.
Definition c13_11 : nat := c12_10 / 3.

Lemma ET12 : 2 * bval (b12 c12_1 c12_2 c12_3 c12_4 c12_5 c12_6 c12_7 c12_8 c12_9 c12_10) = c13_1 * 3 + 0.
Proof. pose proof T12_res as H. unfold vT12 in H. unfold c13_1. gl (bval (b12 c12_1 c12_2 c12_3 c12_4 c12_5 c12_6 c12_7 c12_8 c12_9 c12_10)). Qed.

Lemma EC12_1 : c12_1 = c13_2 * 3 + 1.
Proof.
  pose proof c12_1_res as H. pose proof c12_1_res2 as H2. pose proof c12_1_lb as Hb.
  unfold rc12_1 in H. unfold rb12_1 in H2. unfold lb12_1 in Hb.
  unfold c13_2. cbn [Z.of_N] in H, H2, Hb. gl c12_1.
Qed.

Lemma EC12_2 : c12_2 = c13_3 * 3 + 1.
Proof.
  pose proof c12_2_res as H. pose proof c12_2_res2 as H2. pose proof c12_2_lb as Hb.
  unfold rc12_2 in H. unfold rb12_2 in H2. unfold lb12_2 in Hb.
  unfold c13_3. cbn [Z.of_N] in H, H2, Hb. gl c12_2.
Qed.

Lemma EC12_3 : c12_3 = c13_4 * 3 + 2.
Proof.
  pose proof c12_3_res as H. pose proof c12_3_res2 as H2. pose proof c12_3_lb as Hb.
  unfold rc12_3 in H. unfold rb12_3 in H2. unfold lb12_3 in Hb.
  unfold c13_4. cbn [Z.of_N] in H, H2, Hb. gl c12_3.
Qed.

Lemma EC12_4 : c12_4 = c13_5 * 3 + 0.
Proof.
  pose proof c12_4_res as H. pose proof c12_4_res2 as H2. pose proof c12_4_lb as Hb.
  unfold rc12_4 in H. unfold rb12_4 in H2. unfold lb12_4 in Hb.
  unfold c13_5. cbn [Z.of_N] in H, H2, Hb. gl c12_4.
Qed.

Lemma EC12_5 : c12_5 = c13_6 * 3 + 0.
Proof.
  pose proof c12_5_res as H. pose proof c12_5_res2 as H2. pose proof c12_5_lb as Hb.
  unfold rc12_5 in H. unfold rb12_5 in H2. unfold lb12_5 in Hb.
  unfold c13_6. cbn [Z.of_N] in H, H2, Hb. gl c12_5.
Qed.

Lemma EC12_6 : c12_6 = c13_7 * 3 + 2.
Proof.
  pose proof c12_6_res as H. pose proof c12_6_res2 as H2. pose proof c12_6_lb as Hb.
  unfold rc12_6 in H. unfold rb12_6 in H2. unfold lb12_6 in Hb.
  unfold c13_7. cbn [Z.of_N] in H, H2, Hb. gl c12_6.
Qed.

Lemma EC12_7 : c12_7 = c13_8 * 3 + 1.
Proof.
  pose proof c12_7_res as H. pose proof c12_7_res2 as H2. pose proof c12_7_lb as Hb.
  unfold rc12_7 in H. unfold rb12_7 in H2. unfold lb12_7 in Hb.
  unfold c13_8. cbn [Z.of_N] in H, H2, Hb. gl c12_7.
Qed.

Lemma EC12_8 : c12_8 = c13_9 * 3 + 2.
Proof.
  pose proof c12_8_res as H. pose proof c12_8_res2 as H2. pose proof c12_8_lb as Hb.
  unfold rc12_8 in H. unfold rb12_8 in H2. unfold lb12_8 in Hb.
  unfold c13_9. cbn [Z.of_N] in H, H2, Hb. gl c12_8.
Qed.

Lemma EC12_9 : c12_9 = c13_10 * 3 + 0.
Proof.
  pose proof c12_9_res as H. pose proof c12_9_res2 as H2. pose proof c12_9_lb as Hb.
  unfold rc12_9 in H. unfold rb12_9 in H2. unfold lb12_9 in Hb.
  unfold c13_10. cbn [Z.of_N] in H, H2, Hb. gl c12_9.
Qed.

Lemma EC12_10 : c12_10 = c13_11 * 3 + 2.
Proof.
  pose proof c12_10_res as H. pose proof c12_10_res2 as H2. pose proof c12_10_lb as Hb.
  unfold rc12_10 in H. unfold rb12_10 in H2. unfold lb12_10 in Hb.
  unfold c13_11. cbn [Z.of_N] in H, H2, Hb. gl c12_10.
Qed.

Definition u13 : nat :=
  2 + 2 * bval (b12 (c13_2 * 3 + 1) (c13_3 * 3 + 1) (c13_4 * 3 + 2) (c13_5 * 3 + 0) (c13_6 * 3 + 0)
    (c13_7 * 3 + 2) (c13_8 * 3 + 1) (c13_9 * 3 + 2) (c13_10 * 3 + 0) (c13_11 * 3 + 2)) + lc12 (c13_2
    * 3 + 1) (c13_3 * 3 + 1) (c13_4 * 3 + 2) (c13_5 * 3 + 0) (c13_6 * 3 + 0) (c13_7 * 3 + 2) (c13_8
    * 3 + 1) (c13_9 * 3 + 2) (c13_10 * 3 + 0) (c13_11 * 3 + 2).

Theorem lvl13 : Lvl je13 (b13 c13_1 c13_2 c13_3 c13_4 c13_5 c13_6 c13_7 c13_8 c13_9 c13_10 c13_11) u13 w13.
Proof.
  pose proof lvl12 as H. pose proof ET12 as HT.
  rewrite EC12_1 in H, HT.
  rewrite EC12_2 in H, HT.
  rewrite EC12_3 in H, HT.
  rewrite EC12_4 in H, HT.
  rewrite EC12_5 in H, HT.
  rewrite EC12_6 in H, HT.
  rewrite EC12_7 in H, HT.
  rewrite EC12_8 in H, HT.
  rewrite EC12_9 in H, HT.
  rewrite EC12_10 in H, HT.
  apply (level_next_top _ (b12 (c13_2 * 3 + 1) (c13_3 * 3 + 1) (c13_4 * 3 + 2) (c13_5 * 3 + 0) (c13_6
    * 3 + 0) (c13_7 * 3 + 2) (c13_8 * 3 + 1) (c13_9 * 3 + 2) (c13_10 * 3 + 0) (c13_11 * 3 + 2)) _
    w12 (Cw12 (c13_2 * 3 + 1) (c13_3 * 3 + 1) (c13_4 * 3 + 2) (c13_5 * 3 + 0) (c13_6 * 3 + 0) (c13_7
    * 3 + 2) (c13_8 * 3 + 1) (c13_9 * 3 + 2) (c13_10 * 3 + 0) (c13_11 * 3 + 2)) (lc12 (c13_2 * 3 +
    1) (c13_3 * 3 + 1) (c13_4 * 3 + 2) (c13_5 * 3 + 0) (c13_6 * 3 + 0) (c13_7 * 3 + 2) (c13_8 * 3 +
    1) (c13_9 * 3 + 2) (c13_10 * 3 + 0) (c13_11 * 3 + 2)) tp12 (b13 c13_1 c13_2 c13_3 c13_4 c13_5
    c13_6 c13_7 c13_8 c13_9 c13_10 c13_11) r13 w13 H (Cw12_len _ _ _ _ _ _ _ _ _ _) tp12_lt (fun k
    Hk => end12 _ _ _ _ _ _ _ _ _ _ _ k (h_pos _) Hk)).
  rewrite HT, Zl12_den. apply dmB_sound. apply dv12_ok.
Qed.

(** ** The counts of level 13 modulo 3^1, and lower bounds *)

Definition rc13_1 : N := Eval vm_compute in Z.to_N (((2 * vT12 - 0) / 3) mod 3).
Lemma c13_1_res : (Z.of_nat c13_1 mod Z.of_N 3 = Z.of_N rc13_1)%Z.
Proof.
  pose proof T12_res as H. unfold vT12 in H. unfold c13_1, rc13_1. cbn [Z.of_N].
  gl (bval (b12 c12_1 c12_2 c12_3 c12_4 c12_5 c12_6 c12_7 c12_8 c12_9 c12_10)).
Qed.
Definition lb13_1 : N := Eval vm_compute in ((2 * lbe12) / 3)%N.
Lemma c13_1_lb : (Z.of_N lb13_1 <= Z.of_nat c13_1)%Z.
Proof.
  pose proof (T12_lb c12_1 c12_2 c12_3 c12_4 c12_5 c12_6 c12_7 c12_8 c12_9 c12_10) as H. unfold lbe12 in H. unfold c13_1, lb13_1.
  cbn [Z.of_N] in *. gl (bval (b12 c12_1 c12_2 c12_3 c12_4 c12_5 c12_6 c12_7 c12_8 c12_9 c12_10)).
Qed.
Definition rb13_1 : N := Eval vm_compute in Z.to_N (((2 * Z.of_N t2_12 - 0) * 11) mod 32).
Lemma c13_1_res2 : (Z.of_nat c13_1 mod Z.of_N 32 = Z.of_N rb13_1)%Z.
Proof.
  pose proof T12_res as H. unfold vT12 in H.
  pose proof (T12_low c12_1 c12_2 c12_3 c12_4 c12_5 c12_6 c12_7 c12_8 c12_9 c12_10) as H2. unfold t2_12 in H2.
  unfold c13_1, rb13_1. cbn [Z.of_N] in *. gl (bval (b12 c12_1 c12_2 c12_3 c12_4 c12_5 c12_6 c12_7 c12_8 c12_9 c12_10)).
Qed.

Definition rc13_2 : N := Eval vm_compute in
  Z.to_N (((((Z.of_N rc12_1 - 0) * 1) mod 9) / 3) mod 3).
Definition lb13_2 : N := Eval vm_compute in (((lb12_1 - 0) / 1) / 3)%N.
Definition rb13_2 : N := Eval vm_compute in
  Z.to_N (((((Z.of_N rb12_1 - 0) mod 32) / 1 - 1) * 11) mod 32).
Lemma c13_2_res : (Z.of_nat c13_2 mod Z.of_N 3 = Z.of_N rc13_2)%Z.
Proof.
  pose proof c12_1_res as H. pose proof c12_1_res2 as H2. pose proof c12_1_lb as Hb.
  unfold rc12_1 in H. unfold rb12_1 in H2. unfold lb12_1 in Hb.
  unfold c13_2, rc13_2. cbn [Z.of_N] in *. gl c12_1.
Qed.
Lemma c13_2_res2 : (Z.of_nat c13_2 mod Z.of_N 32 = Z.of_N rb13_2)%Z.
Proof.
  pose proof c12_1_res as H. pose proof c12_1_res2 as H2. pose proof c12_1_lb as Hb.
  unfold rc12_1 in H. unfold rb12_1 in H2. unfold lb12_1 in Hb.
  unfold c13_2, rb13_2. cbn [Z.of_N] in *. gl c12_1.
Qed.
Lemma c13_2_lb : (Z.of_N lb13_2 <= Z.of_nat c13_2)%Z.
Proof.
  pose proof c12_1_res as H. pose proof c12_1_res2 as H2. pose proof c12_1_lb as Hb.
  unfold rc12_1 in H. unfold rb12_1 in H2. unfold lb12_1 in Hb.
  unfold c13_2, lb13_2. cbn [Z.of_N] in *. gl c12_1.
Qed.

Definition rc13_3 : N := Eval vm_compute in
  Z.to_N (((((Z.of_N rc12_2 - 0) * 1) mod 9) / 3) mod 3).
Definition lb13_3 : N := Eval vm_compute in (((lb12_2 - 0) / 1) / 3)%N.
Definition rb13_3 : N := Eval vm_compute in
  Z.to_N (((((Z.of_N rb12_2 - 0) mod 32) / 1 - 1) * 11) mod 32).
Lemma c13_3_res : (Z.of_nat c13_3 mod Z.of_N 3 = Z.of_N rc13_3)%Z.
Proof.
  pose proof c12_2_res as H. pose proof c12_2_res2 as H2. pose proof c12_2_lb as Hb.
  unfold rc12_2 in H. unfold rb12_2 in H2. unfold lb12_2 in Hb.
  unfold c13_3, rc13_3. cbn [Z.of_N] in *. gl c12_2.
Qed.
Lemma c13_3_res2 : (Z.of_nat c13_3 mod Z.of_N 32 = Z.of_N rb13_3)%Z.
Proof.
  pose proof c12_2_res as H. pose proof c12_2_res2 as H2. pose proof c12_2_lb as Hb.
  unfold rc12_2 in H. unfold rb12_2 in H2. unfold lb12_2 in Hb.
  unfold c13_3, rb13_3. cbn [Z.of_N] in *. gl c12_2.
Qed.
Lemma c13_3_lb : (Z.of_N lb13_3 <= Z.of_nat c13_3)%Z.
Proof.
  pose proof c12_2_res as H. pose proof c12_2_res2 as H2. pose proof c12_2_lb as Hb.
  unfold rc12_2 in H. unfold rb12_2 in H2. unfold lb12_2 in Hb.
  unfold c13_3, lb13_3. cbn [Z.of_N] in *. gl c12_2.
Qed.

Definition rc13_4 : N := Eval vm_compute in
  Z.to_N (((((Z.of_N rc12_3 - 0) * 1) mod 9) / 3) mod 3).
Definition lb13_4 : N := Eval vm_compute in (((lb12_3 - 0) / 1) / 3)%N.
Definition rb13_4 : N := Eval vm_compute in
  Z.to_N (((((Z.of_N rb12_3 - 0) mod 32) / 1 - 2) * 11) mod 32).
Lemma c13_4_res : (Z.of_nat c13_4 mod Z.of_N 3 = Z.of_N rc13_4)%Z.
Proof.
  pose proof c12_3_res as H. pose proof c12_3_res2 as H2. pose proof c12_3_lb as Hb.
  unfold rc12_3 in H. unfold rb12_3 in H2. unfold lb12_3 in Hb.
  unfold c13_4, rc13_4. cbn [Z.of_N] in *. gl c12_3.
Qed.
Lemma c13_4_res2 : (Z.of_nat c13_4 mod Z.of_N 32 = Z.of_N rb13_4)%Z.
Proof.
  pose proof c12_3_res as H. pose proof c12_3_res2 as H2. pose proof c12_3_lb as Hb.
  unfold rc12_3 in H. unfold rb12_3 in H2. unfold lb12_3 in Hb.
  unfold c13_4, rb13_4. cbn [Z.of_N] in *. gl c12_3.
Qed.
Lemma c13_4_lb : (Z.of_N lb13_4 <= Z.of_nat c13_4)%Z.
Proof.
  pose proof c12_3_res as H. pose proof c12_3_res2 as H2. pose proof c12_3_lb as Hb.
  unfold rc12_3 in H. unfold rb12_3 in H2. unfold lb12_3 in Hb.
  unfold c13_4, lb13_4. cbn [Z.of_N] in *. gl c12_3.
Qed.

Definition rc13_5 : N := Eval vm_compute in
  Z.to_N (((((Z.of_N rc12_4 - 0) * 1) mod 9) / 3) mod 3).
Definition lb13_5 : N := Eval vm_compute in (((lb12_4 - 0) / 1) / 3)%N.
Definition rb13_5 : N := Eval vm_compute in
  Z.to_N (((((Z.of_N rb12_4 - 0) mod 32) / 1 - 0) * 11) mod 32).
Lemma c13_5_res : (Z.of_nat c13_5 mod Z.of_N 3 = Z.of_N rc13_5)%Z.
Proof.
  pose proof c12_4_res as H. pose proof c12_4_res2 as H2. pose proof c12_4_lb as Hb.
  unfold rc12_4 in H. unfold rb12_4 in H2. unfold lb12_4 in Hb.
  unfold c13_5, rc13_5. cbn [Z.of_N] in *. gl c12_4.
Qed.
Lemma c13_5_res2 : (Z.of_nat c13_5 mod Z.of_N 32 = Z.of_N rb13_5)%Z.
Proof.
  pose proof c12_4_res as H. pose proof c12_4_res2 as H2. pose proof c12_4_lb as Hb.
  unfold rc12_4 in H. unfold rb12_4 in H2. unfold lb12_4 in Hb.
  unfold c13_5, rb13_5. cbn [Z.of_N] in *. gl c12_4.
Qed.
Lemma c13_5_lb : (Z.of_N lb13_5 <= Z.of_nat c13_5)%Z.
Proof.
  pose proof c12_4_res as H. pose proof c12_4_res2 as H2. pose proof c12_4_lb as Hb.
  unfold rc12_4 in H. unfold rb12_4 in H2. unfold lb12_4 in Hb.
  unfold c13_5, lb13_5. cbn [Z.of_N] in *. gl c12_4.
Qed.

Definition rc13_6 : N := Eval vm_compute in
  Z.to_N (((((Z.of_N rc12_5 - 0) * 1) mod 9) / 3) mod 3).
Definition lb13_6 : N := Eval vm_compute in (((lb12_5 - 0) / 1) / 3)%N.
Definition rb13_6 : N := Eval vm_compute in
  Z.to_N (((((Z.of_N rb12_5 - 0) mod 32) / 1 - 0) * 11) mod 32).
Lemma c13_6_res : (Z.of_nat c13_6 mod Z.of_N 3 = Z.of_N rc13_6)%Z.
Proof.
  pose proof c12_5_res as H. pose proof c12_5_res2 as H2. pose proof c12_5_lb as Hb.
  unfold rc12_5 in H. unfold rb12_5 in H2. unfold lb12_5 in Hb.
  unfold c13_6, rc13_6. cbn [Z.of_N] in *. gl c12_5.
Qed.
Lemma c13_6_res2 : (Z.of_nat c13_6 mod Z.of_N 32 = Z.of_N rb13_6)%Z.
Proof.
  pose proof c12_5_res as H. pose proof c12_5_res2 as H2. pose proof c12_5_lb as Hb.
  unfold rc12_5 in H. unfold rb12_5 in H2. unfold lb12_5 in Hb.
  unfold c13_6, rb13_6. cbn [Z.of_N] in *. gl c12_5.
Qed.
Lemma c13_6_lb : (Z.of_N lb13_6 <= Z.of_nat c13_6)%Z.
Proof.
  pose proof c12_5_res as H. pose proof c12_5_res2 as H2. pose proof c12_5_lb as Hb.
  unfold rc12_5 in H. unfold rb12_5 in H2. unfold lb12_5 in Hb.
  unfold c13_6, lb13_6. cbn [Z.of_N] in *. gl c12_5.
Qed.

Definition rc13_7 : N := Eval vm_compute in
  Z.to_N (((((Z.of_N rc12_6 - 0) * 1) mod 9) / 3) mod 3).
Definition lb13_7 : N := Eval vm_compute in (((lb12_6 - 0) / 1) / 3)%N.
Definition rb13_7 : N := Eval vm_compute in
  Z.to_N (((((Z.of_N rb12_6 - 0) mod 16) / 1 - 2) * 11) mod 16).
Lemma c13_7_res : (Z.of_nat c13_7 mod Z.of_N 3 = Z.of_N rc13_7)%Z.
Proof.
  pose proof c12_6_res as H. pose proof c12_6_res2 as H2. pose proof c12_6_lb as Hb.
  unfold rc12_6 in H. unfold rb12_6 in H2. unfold lb12_6 in Hb.
  unfold c13_7, rc13_7. cbn [Z.of_N] in *. gl c12_6.
Qed.
Lemma c13_7_res2 : (Z.of_nat c13_7 mod Z.of_N 16 = Z.of_N rb13_7)%Z.
Proof.
  pose proof c12_6_res as H. pose proof c12_6_res2 as H2. pose proof c12_6_lb as Hb.
  unfold rc12_6 in H. unfold rb12_6 in H2. unfold lb12_6 in Hb.
  unfold c13_7, rb13_7. cbn [Z.of_N] in *. gl c12_6.
Qed.
Lemma c13_7_lb : (Z.of_N lb13_7 <= Z.of_nat c13_7)%Z.
Proof.
  pose proof c12_6_res as H. pose proof c12_6_res2 as H2. pose proof c12_6_lb as Hb.
  unfold rc12_6 in H. unfold rb12_6 in H2. unfold lb12_6 in Hb.
  unfold c13_7, lb13_7. cbn [Z.of_N] in *. gl c12_6.
Qed.

Definition rc13_8 : N := Eval vm_compute in
  Z.to_N (((((Z.of_N rc12_7 - 0) * 1) mod 9) / 3) mod 3).
Definition lb13_8 : N := Eval vm_compute in (((lb12_7 - 0) / 1) / 3)%N.
Definition rb13_8 : N := Eval vm_compute in
  Z.to_N (((((Z.of_N rb12_7 - 0) mod 32) / 1 - 1) * 11) mod 32).
Lemma c13_8_res : (Z.of_nat c13_8 mod Z.of_N 3 = Z.of_N rc13_8)%Z.
Proof.
  pose proof c12_7_res as H. pose proof c12_7_res2 as H2. pose proof c12_7_lb as Hb.
  unfold rc12_7 in H. unfold rb12_7 in H2. unfold lb12_7 in Hb.
  unfold c13_8, rc13_8. cbn [Z.of_N] in *. gl c12_7.
Qed.
Lemma c13_8_res2 : (Z.of_nat c13_8 mod Z.of_N 32 = Z.of_N rb13_8)%Z.
Proof.
  pose proof c12_7_res as H. pose proof c12_7_res2 as H2. pose proof c12_7_lb as Hb.
  unfold rc12_7 in H. unfold rb12_7 in H2. unfold lb12_7 in Hb.
  unfold c13_8, rb13_8. cbn [Z.of_N] in *. gl c12_7.
Qed.
Lemma c13_8_lb : (Z.of_N lb13_8 <= Z.of_nat c13_8)%Z.
Proof.
  pose proof c12_7_res as H. pose proof c12_7_res2 as H2. pose proof c12_7_lb as Hb.
  unfold rc12_7 in H. unfold rb12_7 in H2. unfold lb12_7 in Hb.
  unfold c13_8, lb13_8. cbn [Z.of_N] in *. gl c12_7.
Qed.

Definition rc13_9 : N := Eval vm_compute in
  Z.to_N (((((Z.of_N rc12_8 - 0) * 1) mod 9) / 3) mod 3).
Definition lb13_9 : N := Eval vm_compute in (((lb12_8 - 0) / 1) / 3)%N.
Definition rb13_9 : N := Eval vm_compute in
  Z.to_N (((((Z.of_N rb12_8 - 0) mod 32) / 1 - 2) * 11) mod 32).
Lemma c13_9_res : (Z.of_nat c13_9 mod Z.of_N 3 = Z.of_N rc13_9)%Z.
Proof.
  pose proof c12_8_res as H. pose proof c12_8_res2 as H2. pose proof c12_8_lb as Hb.
  unfold rc12_8 in H. unfold rb12_8 in H2. unfold lb12_8 in Hb.
  unfold c13_9, rc13_9. cbn [Z.of_N] in *. gl c12_8.
Qed.
Lemma c13_9_res2 : (Z.of_nat c13_9 mod Z.of_N 32 = Z.of_N rb13_9)%Z.
Proof.
  pose proof c12_8_res as H. pose proof c12_8_res2 as H2. pose proof c12_8_lb as Hb.
  unfold rc12_8 in H. unfold rb12_8 in H2. unfold lb12_8 in Hb.
  unfold c13_9, rb13_9. cbn [Z.of_N] in *. gl c12_8.
Qed.
Lemma c13_9_lb : (Z.of_N lb13_9 <= Z.of_nat c13_9)%Z.
Proof.
  pose proof c12_8_res as H. pose proof c12_8_res2 as H2. pose proof c12_8_lb as Hb.
  unfold rc12_8 in H. unfold rb12_8 in H2. unfold lb12_8 in Hb.
  unfold c13_9, lb13_9. cbn [Z.of_N] in *. gl c12_8.
Qed.

Definition rc13_10 : N := Eval vm_compute in
  Z.to_N (((((Z.of_N rc12_9 - 0) * 1) mod 9) / 3) mod 3).
Definition lb13_10 : N := Eval vm_compute in (((lb12_9 - 0) / 1) / 3)%N.
Definition rb13_10 : N := Eval vm_compute in
  Z.to_N (((((Z.of_N rb12_9 - 0) mod 32) / 1 - 0) * 11) mod 32).
Lemma c13_10_res : (Z.of_nat c13_10 mod Z.of_N 3 = Z.of_N rc13_10)%Z.
Proof.
  pose proof c12_9_res as H. pose proof c12_9_res2 as H2. pose proof c12_9_lb as Hb.
  unfold rc12_9 in H. unfold rb12_9 in H2. unfold lb12_9 in Hb.
  unfold c13_10, rc13_10. cbn [Z.of_N] in *. gl c12_9.
Qed.
Lemma c13_10_res2 : (Z.of_nat c13_10 mod Z.of_N 32 = Z.of_N rb13_10)%Z.
Proof.
  pose proof c12_9_res as H. pose proof c12_9_res2 as H2. pose proof c12_9_lb as Hb.
  unfold rc12_9 in H. unfold rb12_9 in H2. unfold lb12_9 in Hb.
  unfold c13_10, rb13_10. cbn [Z.of_N] in *. gl c12_9.
Qed.
Lemma c13_10_lb : (Z.of_N lb13_10 <= Z.of_nat c13_10)%Z.
Proof.
  pose proof c12_9_res as H. pose proof c12_9_res2 as H2. pose proof c12_9_lb as Hb.
  unfold rc12_9 in H. unfold rb12_9 in H2. unfold lb12_9 in Hb.
  unfold c13_10, lb13_10. cbn [Z.of_N] in *. gl c12_9.
Qed.

Definition rc13_11 : N := Eval vm_compute in
  Z.to_N (((((Z.of_N rc12_10 - 0) * 1) mod 9) / 3) mod 3).
Definition lb13_11 : N := Eval vm_compute in (((lb12_10 - 0) / 1) / 3)%N.
Definition rb13_11 : N := Eval vm_compute in
  Z.to_N (((((Z.of_N rb12_10 - 0) mod 32) / 1 - 2) * 11) mod 32).
Lemma c13_11_res : (Z.of_nat c13_11 mod Z.of_N 3 = Z.of_N rc13_11)%Z.
Proof.
  pose proof c12_10_res as H. pose proof c12_10_res2 as H2. pose proof c12_10_lb as Hb.
  unfold rc12_10 in H. unfold rb12_10 in H2. unfold lb12_10 in Hb.
  unfold c13_11, rc13_11. cbn [Z.of_N] in *. gl c12_10.
Qed.
Lemma c13_11_res2 : (Z.of_nat c13_11 mod Z.of_N 32 = Z.of_N rb13_11)%Z.
Proof.
  pose proof c12_10_res as H. pose proof c12_10_res2 as H2. pose proof c12_10_lb as Hb.
  unfold rc12_10 in H. unfold rb12_10 in H2. unfold lb12_10 in Hb.
  unfold c13_11, rb13_11. cbn [Z.of_N] in *. gl c12_10.
Qed.
Lemma c13_11_lb : (Z.of_N lb13_11 <= Z.of_nat c13_11)%Z.
Proof.
  pose proof c12_10_res as H. pose proof c12_10_res2 as H2. pose proof c12_10_lb as Hb.
  unfold rc12_10 in H. unfold rb12_10 in H2. unfold lb12_10 in Hb.
  unfold c13_11, lb13_11. cbn [Z.of_N] in *. gl c12_10.
Qed.

(** ** The word of level 13 modulo 3^1 *)

Definition vT13 : Z := Eval vm_compute in
  gv (resW 3 [RL a13_0; RR P13_1 3 rc13_1; RL a13_1; RR P13_2 3 rc13_2; RL a13_2; RR P13_3 3 rc13_3;
    RL a13_3; RR P13_4 3 rc13_4; RL a13_4; RR P13_5 3 rc13_5; RL a13_5; RR P13_6 3 rc13_6; RL a13_6;
    RR P13_7 3 rc13_7; RL a13_7; RR P13_8 3 rc13_8; RL a13_8; RR P13_9 3 rc13_9; RL a13_9; RR P13_10
    3 rc13_10; RL a13_10; RR P13_11 3 rc13_11; RL a13_11]).

Lemma T13_res : (Z.of_nat (bval (b13 c13_1 c13_2 c13_3 c13_4 c13_5 c13_6 c13_7 c13_8 c13_9 c13_10 c13_11)) mod 3 = vT13)%Z.
Proof.
  unfold b13.
  apply (resW_sound 3 [Lit a13_0; Rep P13_1 c13_1; Lit a13_1; Rep P13_2 c13_2; Lit a13_2; Rep P13_3
    c13_3; Lit a13_3; Rep P13_4 c13_4; Lit a13_4; Rep P13_5 c13_5; Lit a13_5; Rep P13_6 c13_6; Lit
    a13_6; Rep P13_7 c13_7; Lit a13_7; Rep P13_8 c13_8; Lit a13_8; Rep P13_9 c13_9; Lit a13_9; Rep
    P13_10 c13_10; Lit a13_10; Rep P13_11 c13_11; Lit a13_11]
           [RL a13_0; RR P13_1 3 rc13_1; RL a13_1; RR P13_2 3 rc13_2; RL a13_2; RR P13_3 3 rc13_3; RL a13_3; RR
            P13_4 3 rc13_4; RL a13_4; RR P13_5 3 rc13_5; RL a13_5; RR P13_6 3 rc13_6; RL a13_6; RR
            P13_7 3 rc13_7; RL a13_7; RR P13_8 3 rc13_8; RL a13_8; RR P13_9 3 rc13_9; RL a13_9; RR
            P13_10 3 rc13_10; RL a13_10; RR P13_11 3 rc13_11; RL a13_11]);
    [lia | | vm_compute; reflexivity].
  exact (Forall2_cons _ _ (mL a13_0)
    (Forall2_cons _ _ (mR P13_1 c13_1 3%N rc13_1 c13_1_res)
    (Forall2_cons _ _ (mL a13_1)
    (Forall2_cons _ _ (mR P13_2 c13_2 3%N rc13_2 c13_2_res)
    (Forall2_cons _ _ (mL a13_2)
    (Forall2_cons _ _ (mR P13_3 c13_3 3%N rc13_3 c13_3_res)
    (Forall2_cons _ _ (mL a13_3)
    (Forall2_cons _ _ (mR P13_4 c13_4 3%N rc13_4 c13_4_res)
    (Forall2_cons _ _ (mL a13_4)
    (Forall2_cons _ _ (mR P13_5 c13_5 3%N rc13_5 c13_5_res)
    (Forall2_cons _ _ (mL a13_5)
    (Forall2_cons _ _ (mR P13_6 c13_6 3%N rc13_6 c13_6_res)
    (Forall2_cons _ _ (mL a13_6)
    (Forall2_cons _ _ (mR P13_7 c13_7 3%N rc13_7 c13_7_res)
    (Forall2_cons _ _ (mL a13_7)
    (Forall2_cons _ _ (mR P13_8 c13_8 3%N rc13_8 c13_8_res)
    (Forall2_cons _ _ (mL a13_8)
    (Forall2_cons _ _ (mR P13_9 c13_9 3%N rc13_9 c13_9_res)
    (Forall2_cons _ _ (mL a13_9)
    (Forall2_cons _ _ (mR P13_10 c13_10 3%N rc13_10 c13_10_res)
    (Forall2_cons _ _ (mL a13_10)
    (Forall2_cons _ _ (mR P13_11 c13_11 3%N rc13_11 c13_11_res)
    (Forall2_cons _ _ (mL a13_11) (Forall2_nil _)))))))))))))))))))))))).
Qed.

Definition lbe13 : N := Eval vm_compute in bvalN a13_11.

Lemma T13_lb : forall d1 d2 d3 d4 d5 d6 d7 d8 d9 d10 d11, (Z.of_N lbe13 <= Z.of_nat (bval (b13 d1 d2 d3 d4 d5 d6 d7 d8 d9 d10 d11)))%Z.
Proof.
  intros d1 d2 d3 d4 d5 d6 d7 d8 d9 d10 d11. unfold b13. change lbe13 with (bvalN a13_11).
  exact (lbZ [Lit a13_0; Rep P13_1 d1; Lit a13_1; Rep P13_2 d2; Lit a13_2; Rep P13_3 d3; Lit a13_3;
    Rep P13_4 d4; Lit a13_4; Rep P13_5 d5; Lit a13_5; Rep P13_6 d6; Lit a13_6; Rep P13_7 d7; Lit
    a13_7; Rep P13_8 d8; Lit a13_8; Rep P13_9 d9; Lit a13_9; Rep P13_10 d10; Lit a13_10; Rep P13_11
    d11] a13_11).
Qed.

Definition t2_13 : N := Eval vm_compute in bvalN a13_0.

Lemma T13_low : forall d1 d2 d3 d4 d5 d6 d7 d8 d9 d10 d11, (Z.of_nat (bval (b13 d1 d2 d3 d4 d5 d6 d7 d8 d9 d10 d11)) mod 16 = Z.of_N t2_13)%Z.
Proof.
  intros d1 d2 d3 d4 d5 d6 d7 d8 d9 d10 d11. unfold b13.
  exact (bval_low_den a13_0 [Rep P13_1 d1; Lit a13_1; Rep P13_2 d2; Lit a13_2; Rep P13_3 d3; Lit
    a13_3; Rep P13_4 d4; Lit a13_4; Rep P13_5 d5; Lit a13_5; Rep P13_6 d6; Lit a13_6; Rep P13_7 d7;
    Lit a13_7; Rep P13_8 d8; Lit a13_8; Rep P13_9 d9; Lit a13_9; Rep P13_10 d10; Lit a13_10; Rep
    P13_11 d11; Lit a13_11]).
Qed.

End L1213b.

Module L1314a.

(** * 1RB1LB_1RC0RD_0LA1RE_0RF1LC_1LA0RB_---1LC: the end phase of level 13

    Level 13 has class 3 and a counter word with 11 repeated blocks.  The end phase is
    certified round by round ([crun_run]): a run to the first block, then for each block a
    cycle per copy and a run across the next junction, and a closing computation.  The cuts
    are computed from the rounds of one instance.  Generated by a script. *)

Import Individual62.
Import T694_levels End694 Sym694 Lev694 Lvl1_694 Eng694 Cert694 Run694 Res694 Gen694.
Import L23 L34 L45 L56 L6i L67a L67b L78a L78b L89a L89b L910a L910b L1011a L1011b L1112a L1112b L1213a L1213b.
Import Lia Arith PeanoNat Bool NArith ZArith.
Import Coq.Lists.List.
Import ListNotations.

(** ** The cells of the counter word *)

Definition pa13_0 : bool := Eval vm_compute in par false a13_0.
Lemma pa13_0_eq : par false a13_0 = pa13_0.
Proof. vm_compute. reflexivity. Qed.
Definition pa13_1 : bool := Eval vm_compute in par pa13_0 a13_1.
Lemma pa13_1_eq : par pa13_0 a13_1 = pa13_1.
Proof. vm_compute. reflexivity. Qed.
Definition pa13_2 : bool := Eval vm_compute in par pa13_1 a13_2.
Lemma pa13_2_eq : par pa13_1 a13_2 = pa13_2.
Proof. vm_compute. reflexivity. Qed.
Definition pa13_3 : bool := Eval vm_compute in par pa13_2 a13_3.
Lemma pa13_3_eq : par pa13_2 a13_3 = pa13_3.
Proof. vm_compute. reflexivity. Qed.
Definition pa13_4 : bool := Eval vm_compute in par pa13_3 a13_4.
Lemma pa13_4_eq : par pa13_3 a13_4 = pa13_4.
Proof. vm_compute. reflexivity. Qed.
Definition pa13_5 : bool := Eval vm_compute in par pa13_4 a13_5.
Lemma pa13_5_eq : par pa13_4 a13_5 = pa13_5.
Proof. vm_compute. reflexivity. Qed.
Definition pa13_6 : bool := Eval vm_compute in par pa13_5 a13_6.
Lemma pa13_6_eq : par pa13_5 a13_6 = pa13_6.
Proof. vm_compute. reflexivity. Qed.
Definition pa13_7 : bool := Eval vm_compute in par pa13_6 a13_7.
Lemma pa13_7_eq : par pa13_6 a13_7 = pa13_7.
Proof. vm_compute. reflexivity. Qed.
Definition pa13_8 : bool := Eval vm_compute in par pa13_7 a13_8.
Lemma pa13_8_eq : par pa13_7 a13_8 = pa13_8.
Proof. vm_compute. reflexivity. Qed.
Definition pa13_9 : bool := Eval vm_compute in par pa13_8 a13_9.
Lemma pa13_9_eq : par pa13_8 a13_9 = pa13_9.
Proof. vm_compute. reflexivity. Qed.
Definition pa13_10 : bool := Eval vm_compute in par pa13_9 a13_10.
Lemma pa13_10_eq : par pa13_9 a13_10 = pa13_10.
Proof. vm_compute. reflexivity. Qed.
Lemma pp13_1 : par pa13_0 P13_1 = pa13_0.
Proof. vm_compute. reflexivity. Qed.
Lemma pp13_2 : par pa13_1 P13_2 = pa13_1.
Proof. vm_compute. reflexivity. Qed.
Lemma pp13_3 : par pa13_2 P13_3 = pa13_2.
Proof. vm_compute. reflexivity. Qed.
Lemma pp13_4 : par pa13_3 P13_4 = pa13_3.
Proof. vm_compute. reflexivity. Qed.
Lemma pp13_5 : par pa13_4 P13_5 = pa13_4.
Proof. vm_compute. reflexivity. Qed.
Lemma pp13_6 : par pa13_5 P13_6 = pa13_5.
Proof. vm_compute. reflexivity. Qed.
Lemma pp13_7 : par pa13_6 P13_7 = pa13_6.
Proof. vm_compute. reflexivity. Qed.
Lemma pp13_8 : par pa13_7 P13_8 = pa13_7.
Proof. vm_compute. reflexivity. Qed.
Lemma pp13_9 : par pa13_8 P13_9 = pa13_8.
Proof. vm_compute. reflexivity. Qed.
Lemma pp13_10 : par pa13_9 P13_10 = pa13_9.
Proof. vm_compute. reflexivity. Qed.
Lemma pp13_11 : par pa13_10 P13_11 = pa13_10.
Proof. vm_compute. reflexivity. Qed.

Definition Hd13 : list bool := rep10 je13 ++ c1101 ++ encb false a13_0.
Definition E13_1 : list bool := encb pa13_0 P13_1.
Definition J13_1 : list bool := encb pa13_0 a13_1.
Definition E13_2 : list bool := encb pa13_1 P13_2.
Definition J13_2 : list bool := encb pa13_1 a13_2.
Definition E13_3 : list bool := encb pa13_2 P13_3.
Definition J13_3 : list bool := encb pa13_2 a13_3.
Definition E13_4 : list bool := encb pa13_3 P13_4.
Definition J13_4 : list bool := encb pa13_3 a13_4.
Definition E13_5 : list bool := encb pa13_4 P13_5.
Definition J13_5 : list bool := encb pa13_4 a13_5.
Definition E13_6 : list bool := encb pa13_5 P13_6.
Definition J13_6 : list bool := encb pa13_5 a13_6.
Definition E13_7 : list bool := encb pa13_6 P13_7.
Definition J13_7 : list bool := encb pa13_6 a13_7.
Definition E13_8 : list bool := encb pa13_7 P13_8.
Definition J13_8 : list bool := encb pa13_7 a13_8.
Definition E13_9 : list bool := encb pa13_8 P13_9.
Definition J13_9 : list bool := encb pa13_8 a13_9.
Definition E13_10 : list bool := encb pa13_9 P13_10.
Definition J13_10 : list bool := encb pa13_9 a13_10.
Definition E13_11 : list bool := encb pa13_10 P13_11.
Definition J13_11 : list bool := encb pa13_10 a13_11.

Definition cells13 (c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 : nat) : list bool :=
  rep10 je13 ++ c1101 ++ encb false (b13 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11) ++ w13.

Lemma cells13_eq : forall c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11,
  cells13 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 = Hd13 ++ rp E13_1 c1 ++ J13_1 ++ rp E13_2 c2 ++ J13_2 ++
    rp E13_3 c3 ++ J13_3 ++ rp E13_4 c4 ++ J13_4 ++ rp E13_5 c5 ++ J13_5 ++ rp E13_6 c6 ++ J13_6 ++
    rp E13_7 c7 ++ J13_7 ++ rp E13_8 c8 ++ J13_8 ++ rp E13_9 c9 ++ J13_9 ++ rp E13_10 c10 ++ J13_10
    ++ rp E13_11 c11 ++ J13_11 ++ w13.
Proof.
  intros c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11. unfold cells13, b13, Hd13, E13_1, J13_1, E13_2, J13_2, E13_3, J13_3, E13_4, J13_4, E13_5, J13_5, E13_6, J13_6, E13_7, J13_7, E13_8, J13_8, E13_9, J13_9, E13_10, J13_10, E13_11, J13_11.
  cbn [den bden]. rewrite app_nil_r.
  rewrite (encb_app a13_0), pa13_0_eq.
  rewrite (encb_rp P13_1 pa13_0 pp13_1), (encb_app a13_1), pa13_1_eq.
  rewrite (encb_rp P13_2 pa13_1 pp13_2), (encb_app a13_2), pa13_2_eq.
  rewrite (encb_rp P13_3 pa13_2 pp13_3), (encb_app a13_3), pa13_3_eq.
  rewrite (encb_rp P13_4 pa13_3 pp13_4), (encb_app a13_4), pa13_4_eq.
  rewrite (encb_rp P13_5 pa13_4 pp13_5), (encb_app a13_5), pa13_5_eq.
  rewrite (encb_rp P13_6 pa13_5 pp13_6), (encb_app a13_6), pa13_6_eq.
  rewrite (encb_rp P13_7 pa13_6 pp13_7), (encb_app a13_7), pa13_7_eq.
  rewrite (encb_rp P13_8 pa13_7 pp13_8), (encb_app a13_8), pa13_8_eq.
  rewrite (encb_rp P13_9 pa13_8 pp13_9), (encb_app a13_9), pa13_9_eq.
  rewrite (encb_rp P13_10 pa13_9 pp13_10), (encb_app a13_10), pa13_10_eq.
  rewrite (encb_rp P13_11 pa13_10 pp13_11).
  rewrite <- ?app_assoc. reflexivity.
Qed.

(** ** Boundaries, computed from the rounds of one instance *)

Definition look13_1 : nat := 36.
Definition dep13_1 : nat := 1.
Definition p13_1 : nat := Eval vm_compute in length E13_1.
Definition N13_1 : nat := Eval vm_compute in
  let b0 := (look13_1 / p13_1 + dep13_1 + 14)%nat in
  (b0 + N.to_nat ((rb13_1 + 4 * 1024 - N.of_nat b0) mod 4)%N)%nat.
Definition look13_2 : nat := 36.
Definition dep13_2 : nat := 1.
Definition p13_2 : nat := Eval vm_compute in length E13_2.
Definition N13_2 : nat := Eval vm_compute in
  let b0 := (look13_2 / p13_2 + dep13_2 + 14)%nat in
  (b0 + N.to_nat ((rb13_2 + 4 * 1024 - N.of_nat b0) mod 4)%N)%nat.
Definition look13_3 : nat := 36.
Definition dep13_3 : nat := 1.
Definition p13_3 : nat := Eval vm_compute in length E13_3.
Definition N13_3 : nat := Eval vm_compute in
  let b0 := (look13_3 / p13_3 + dep13_3 + 14)%nat in
  (b0 + N.to_nat ((rb13_3 + 4 * 1024 - N.of_nat b0) mod 4)%N)%nat.
Definition look13_4 : nat := 36.
Definition dep13_4 : nat := 1.
Definition p13_4 : nat := Eval vm_compute in length E13_4.
Definition N13_4 : nat := Eval vm_compute in
  let b0 := (look13_4 / p13_4 + dep13_4 + 14)%nat in
  (b0 + N.to_nat ((rb13_4 + 4 * 1024 - N.of_nat b0) mod 4)%N)%nat.
Definition look13_5 : nat := 36.
Definition dep13_5 : nat := 1.
Definition p13_5 : nat := Eval vm_compute in length E13_5.
Definition N13_5 : nat := Eval vm_compute in
  let b0 := (look13_5 / p13_5 + dep13_5 + 14)%nat in
  (b0 + N.to_nat ((rb13_5 + 4 * 1024 - N.of_nat b0) mod 4)%N)%nat.
Definition look13_6 : nat := 36.
Definition dep13_6 : nat := 1.
Definition p13_6 : nat := Eval vm_compute in length E13_6.
Definition N13_6 : nat := Eval vm_compute in
  let b0 := (look13_6 / p13_6 + dep13_6 + 14)%nat in
  (b0 + N.to_nat ((rb13_6 + 4 * 1024 - N.of_nat b0) mod 4)%N)%nat.
Definition look13_7 : nat := 36.
Definition dep13_7 : nat := 1.
Definition p13_7 : nat := Eval vm_compute in length E13_7.
Definition N13_7 : nat := Eval vm_compute in
  let b0 := (look13_7 / p13_7 + dep13_7 + 14)%nat in
  (b0 + N.to_nat ((rb13_7 + 4 * 1024 - N.of_nat b0) mod 4)%N)%nat.
Definition look13_8 : nat := 36.
Definition dep13_8 : nat := 1.
Definition p13_8 : nat := Eval vm_compute in length E13_8.
Definition N13_8 : nat := Eval vm_compute in
  let b0 := (look13_8 / p13_8 + dep13_8 + 14)%nat in
  (b0 + N.to_nat ((rb13_8 + 4 * 1024 - N.of_nat b0) mod 4)%N)%nat.
Definition look13_9 : nat := 36.
Definition dep13_9 : nat := 1.
Definition p13_9 : nat := Eval vm_compute in length E13_9.
Definition N13_9 : nat := Eval vm_compute in
  let b0 := (look13_9 / p13_9 + dep13_9 + 14)%nat in
  (b0 + N.to_nat ((rb13_9 + 4 * 1024 - N.of_nat b0) mod 4)%N)%nat.
Definition look13_10 : nat := 36.
Definition dep13_10 : nat := 1.
Definition p13_10 : nat := Eval vm_compute in length E13_10.
Definition N13_10 : nat := Eval vm_compute in
  let b0 := (look13_10 / p13_10 + dep13_10 + 14)%nat in
  (b0 + N.to_nat ((rb13_10 + 4 * 1024 - N.of_nat b0) mod 4)%N)%nat.
Definition look13_11 : nat := 36.
Definition dep13_11 : nat := 1.
Definition p13_11 : nat := Eval vm_compute in length E13_11.
Definition N13_11 : nat := Eval vm_compute in
  let b0 := (look13_11 / p13_11 + dep13_11 + 14)%nat in
  (b0 + N.to_nat ((rb13_11 + 4 * 1024 - N.of_nat b0) mod 4)%N)%nat.
Definition looke13 : nat := 36.
Definition inst13 : list bool := cells13 N13_1 N13_2 N13_3 N13_4 N13_5 N13_6 N13_7 N13_8 N13_9 N13_10 N13_11.
Definition s13_1 : N := Eval vm_compute in N.of_nat (length Hd13).
Definition s13_2 : N := Eval vm_compute in
  (s13_1 + N.of_nat (N13_1 * p13_1 + length J13_1))%N.
Definition s13_3 : N := Eval vm_compute in
  (s13_2 + N.of_nat (N13_2 * p13_2 + length J13_2))%N.
Definition s13_4 : N := Eval vm_compute in
  (s13_3 + N.of_nat (N13_3 * p13_3 + length J13_3))%N.
Definition s13_5 : N := Eval vm_compute in
  (s13_4 + N.of_nat (N13_4 * p13_4 + length J13_4))%N.
Definition s13_6 : N := Eval vm_compute in
  (s13_5 + N.of_nat (N13_5 * p13_5 + length J13_5))%N.
Definition s13_7 : N := Eval vm_compute in
  (s13_6 + N.of_nat (N13_6 * p13_6 + length J13_6))%N.
Definition s13_8 : N := Eval vm_compute in
  (s13_7 + N.of_nat (N13_7 * p13_7 + length J13_7))%N.
Definition s13_9 : N := Eval vm_compute in
  (s13_8 + N.of_nat (N13_8 * p13_8 + length J13_8))%N.
Definition s13_10 : N := Eval vm_compute in
  (s13_9 + N.of_nat (N13_9 * p13_9 + length J13_9))%N.
Definition s13_11 : N := Eval vm_compute in
  (s13_10 + N.of_nat (N13_10 * p13_10 + length J13_10))%N.
Definition s13_12 : N := Eval vm_compute in
  (s13_11 + N.of_nat (N13_11 * p13_11 + length J13_11))%N.
Definition fall13 : list (N * N * N * N) * (N * N) * nat := Eval vm_compute in
  let tr := gtrace 36 (length inst13) 0 0 0 (c1101, true, inst13) in
  (gfindk (N.of_nat p13_1) (s13_1 + N.of_nat (dep13_1 * p13_1))
         (s13_1 + N.of_nat (N13_1 * p13_1) - N.of_nat look13_1) (1%N :: 2%N :: 4%N :: nil) tr ::
   gfindk (N.of_nat p13_2) (s13_2 + N.of_nat (dep13_2 * p13_2))
         (s13_2 + N.of_nat (N13_2 * p13_2) - N.of_nat look13_2) (1%N :: 2%N :: 4%N :: nil) tr ::
   gfindk (N.of_nat p13_3) (s13_3 + N.of_nat (dep13_3 * p13_3))
         (s13_3 + N.of_nat (N13_3 * p13_3) - N.of_nat look13_3) (1%N :: 2%N :: 4%N :: nil) tr ::
   gfindk (N.of_nat p13_4) (s13_4 + N.of_nat (dep13_4 * p13_4))
         (s13_4 + N.of_nat (N13_4 * p13_4) - N.of_nat look13_4) (1%N :: 2%N :: 4%N :: nil) tr ::
   gfindk (N.of_nat p13_5) (s13_5 + N.of_nat (dep13_5 * p13_5))
         (s13_5 + N.of_nat (N13_5 * p13_5) - N.of_nat look13_5) (1%N :: 2%N :: 4%N :: nil) tr ::
   gfindk (N.of_nat p13_6) (s13_6 + N.of_nat (dep13_6 * p13_6))
         (s13_6 + N.of_nat (N13_6 * p13_6) - N.of_nat look13_6) (1%N :: 2%N :: 4%N :: nil) tr ::
   gfindk (N.of_nat p13_7) (s13_7 + N.of_nat (dep13_7 * p13_7))
         (s13_7 + N.of_nat (N13_7 * p13_7) - N.of_nat look13_7) (1%N :: 2%N :: 4%N :: nil) tr ::
   gfindk (N.of_nat p13_8) (s13_8 + N.of_nat (dep13_8 * p13_8))
         (s13_8 + N.of_nat (N13_8 * p13_8) - N.of_nat look13_8) (1%N :: 2%N :: 4%N :: nil) tr ::
   gfindk (N.of_nat p13_9) (s13_9 + N.of_nat (dep13_9 * p13_9))
         (s13_9 + N.of_nat (N13_9 * p13_9) - N.of_nat look13_9) (1%N :: 2%N :: 4%N :: nil) tr ::
   gfindk (N.of_nat p13_10) (s13_10 + N.of_nat (dep13_10 * p13_10))
         (s13_10 + N.of_nat (N13_10 * p13_10) - N.of_nat look13_10) (1%N :: 2%N :: 4%N :: nil) tr ::
   gfindk (N.of_nat p13_11) (s13_11 + N.of_nat (dep13_11 * p13_11))
         (s13_11 + N.of_nat (N13_11 * p13_11) - N.of_nat look13_11) (1%N :: 2%N :: 4%N :: nil) tr ::
   nil,
   glast (s13_12 - N.of_nat (looke13 + 60)) tr (0, 0)%N, length tr).
Definition f13_1 : N * N * N * N := Eval vm_compute in
  nth 0 (fst (fst fall13)) (0, 0, 0, 1)%N.
Definition rr13_1 : nat := Eval vm_compute in N.to_nat (fst (fst (fst f13_1))).
Definition R13_1 : nat := Eval vm_compute in N.to_nat (snd (fst f13_1)).
Definition kq13_1 : nat := Eval vm_compute in N.to_nat (snd f13_1).
Definition cc13_1 : nat := Eval vm_compute in N.to_nat ((snd (fst (fst f13_1)) + N.of_nat look13_1 - s13_1) / N.of_nat p13_1).
Definition uu13_1 : nat := Eval vm_compute in N.to_nat ((snd (fst (fst f13_1)) + N.of_nat look13_1 - s13_1) mod N.of_nat p13_1).
Definition jj13_1 : nat := Eval vm_compute in (N13_1 - cc13_1 - 1) mod kq13_1.
Definition S13_1 : sst := Eval vm_compute in
  gcut look13_1 (grst rr13_1 (c1101, true, inst13)).
Definition f13_2 : N * N * N * N := Eval vm_compute in
  nth 1 (fst (fst fall13)) (0, 0, 0, 1)%N.
Definition rr13_2 : nat := Eval vm_compute in N.to_nat (fst (fst (fst f13_2))).
Definition R13_2 : nat := Eval vm_compute in N.to_nat (snd (fst f13_2)).
Definition kq13_2 : nat := Eval vm_compute in N.to_nat (snd f13_2).
Definition cc13_2 : nat := Eval vm_compute in N.to_nat ((snd (fst (fst f13_2)) + N.of_nat look13_2 - s13_2) / N.of_nat p13_2).
Definition uu13_2 : nat := Eval vm_compute in N.to_nat ((snd (fst (fst f13_2)) + N.of_nat look13_2 - s13_2) mod N.of_nat p13_2).
Definition jj13_2 : nat := Eval vm_compute in (N13_2 - cc13_2 - 1) mod kq13_2.
Definition S13_2 : sst := Eval vm_compute in
  gcut look13_2 (grst rr13_2 (c1101, true, inst13)).
Definition f13_3 : N * N * N * N := Eval vm_compute in
  nth 2 (fst (fst fall13)) (0, 0, 0, 1)%N.
Definition rr13_3 : nat := Eval vm_compute in N.to_nat (fst (fst (fst f13_3))).
Definition R13_3 : nat := Eval vm_compute in N.to_nat (snd (fst f13_3)).
Definition kq13_3 : nat := Eval vm_compute in N.to_nat (snd f13_3).
Definition cc13_3 : nat := Eval vm_compute in N.to_nat ((snd (fst (fst f13_3)) + N.of_nat look13_3 - s13_3) / N.of_nat p13_3).
Definition uu13_3 : nat := Eval vm_compute in N.to_nat ((snd (fst (fst f13_3)) + N.of_nat look13_3 - s13_3) mod N.of_nat p13_3).
Definition jj13_3 : nat := Eval vm_compute in (N13_3 - cc13_3 - 1) mod kq13_3.
Definition S13_3 : sst := Eval vm_compute in
  gcut look13_3 (grst rr13_3 (c1101, true, inst13)).
Definition f13_4 : N * N * N * N := Eval vm_compute in
  nth 3 (fst (fst fall13)) (0, 0, 0, 1)%N.
Definition rr13_4 : nat := Eval vm_compute in N.to_nat (fst (fst (fst f13_4))).
Definition R13_4 : nat := Eval vm_compute in N.to_nat (snd (fst f13_4)).
Definition kq13_4 : nat := Eval vm_compute in N.to_nat (snd f13_4).
Definition cc13_4 : nat := Eval vm_compute in N.to_nat ((snd (fst (fst f13_4)) + N.of_nat look13_4 - s13_4) / N.of_nat p13_4).
Definition uu13_4 : nat := Eval vm_compute in N.to_nat ((snd (fst (fst f13_4)) + N.of_nat look13_4 - s13_4) mod N.of_nat p13_4).
Definition jj13_4 : nat := Eval vm_compute in (N13_4 - cc13_4 - 1) mod kq13_4.
Definition S13_4 : sst := Eval vm_compute in
  gcut look13_4 (grst rr13_4 (c1101, true, inst13)).
Definition f13_5 : N * N * N * N := Eval vm_compute in
  nth 4 (fst (fst fall13)) (0, 0, 0, 1)%N.
Definition rr13_5 : nat := Eval vm_compute in N.to_nat (fst (fst (fst f13_5))).
Definition R13_5 : nat := Eval vm_compute in N.to_nat (snd (fst f13_5)).
Definition kq13_5 : nat := Eval vm_compute in N.to_nat (snd f13_5).
Definition cc13_5 : nat := Eval vm_compute in N.to_nat ((snd (fst (fst f13_5)) + N.of_nat look13_5 - s13_5) / N.of_nat p13_5).
Definition uu13_5 : nat := Eval vm_compute in N.to_nat ((snd (fst (fst f13_5)) + N.of_nat look13_5 - s13_5) mod N.of_nat p13_5).
Definition jj13_5 : nat := Eval vm_compute in (N13_5 - cc13_5 - 1) mod kq13_5.
Definition S13_5 : sst := Eval vm_compute in
  gcut look13_5 (grst rr13_5 (c1101, true, inst13)).
Definition f13_6 : N * N * N * N := Eval vm_compute in
  nth 5 (fst (fst fall13)) (0, 0, 0, 1)%N.
Definition rr13_6 : nat := Eval vm_compute in N.to_nat (fst (fst (fst f13_6))).
Definition R13_6 : nat := Eval vm_compute in N.to_nat (snd (fst f13_6)).
Definition kq13_6 : nat := Eval vm_compute in N.to_nat (snd f13_6).
Definition cc13_6 : nat := Eval vm_compute in N.to_nat ((snd (fst (fst f13_6)) + N.of_nat look13_6 - s13_6) / N.of_nat p13_6).
Definition uu13_6 : nat := Eval vm_compute in N.to_nat ((snd (fst (fst f13_6)) + N.of_nat look13_6 - s13_6) mod N.of_nat p13_6).
Definition jj13_6 : nat := Eval vm_compute in (N13_6 - cc13_6 - 1) mod kq13_6.
Definition S13_6 : sst := Eval vm_compute in
  gcut look13_6 (grst rr13_6 (c1101, true, inst13)).
Definition f13_7 : N * N * N * N := Eval vm_compute in
  nth 6 (fst (fst fall13)) (0, 0, 0, 1)%N.
Definition rr13_7 : nat := Eval vm_compute in N.to_nat (fst (fst (fst f13_7))).
Definition R13_7 : nat := Eval vm_compute in N.to_nat (snd (fst f13_7)).
Definition kq13_7 : nat := Eval vm_compute in N.to_nat (snd f13_7).
Definition cc13_7 : nat := Eval vm_compute in N.to_nat ((snd (fst (fst f13_7)) + N.of_nat look13_7 - s13_7) / N.of_nat p13_7).
Definition uu13_7 : nat := Eval vm_compute in N.to_nat ((snd (fst (fst f13_7)) + N.of_nat look13_7 - s13_7) mod N.of_nat p13_7).
Definition jj13_7 : nat := Eval vm_compute in (N13_7 - cc13_7 - 1) mod kq13_7.
Definition S13_7 : sst := Eval vm_compute in
  gcut look13_7 (grst rr13_7 (c1101, true, inst13)).
Definition f13_8 : N * N * N * N := Eval vm_compute in
  nth 7 (fst (fst fall13)) (0, 0, 0, 1)%N.
Definition rr13_8 : nat := Eval vm_compute in N.to_nat (fst (fst (fst f13_8))).
Definition R13_8 : nat := Eval vm_compute in N.to_nat (snd (fst f13_8)).
Definition kq13_8 : nat := Eval vm_compute in N.to_nat (snd f13_8).
Definition cc13_8 : nat := Eval vm_compute in N.to_nat ((snd (fst (fst f13_8)) + N.of_nat look13_8 - s13_8) / N.of_nat p13_8).
Definition uu13_8 : nat := Eval vm_compute in N.to_nat ((snd (fst (fst f13_8)) + N.of_nat look13_8 - s13_8) mod N.of_nat p13_8).
Definition jj13_8 : nat := Eval vm_compute in (N13_8 - cc13_8 - 1) mod kq13_8.
Definition S13_8 : sst := Eval vm_compute in
  gcut look13_8 (grst rr13_8 (c1101, true, inst13)).
Definition f13_9 : N * N * N * N := Eval vm_compute in
  nth 8 (fst (fst fall13)) (0, 0, 0, 1)%N.
Definition rr13_9 : nat := Eval vm_compute in N.to_nat (fst (fst (fst f13_9))).
Definition R13_9 : nat := Eval vm_compute in N.to_nat (snd (fst f13_9)).
Definition kq13_9 : nat := Eval vm_compute in N.to_nat (snd f13_9).
Definition cc13_9 : nat := Eval vm_compute in N.to_nat ((snd (fst (fst f13_9)) + N.of_nat look13_9 - s13_9) / N.of_nat p13_9).
Definition uu13_9 : nat := Eval vm_compute in N.to_nat ((snd (fst (fst f13_9)) + N.of_nat look13_9 - s13_9) mod N.of_nat p13_9).
Definition jj13_9 : nat := Eval vm_compute in (N13_9 - cc13_9 - 1) mod kq13_9.
Definition S13_9 : sst := Eval vm_compute in
  gcut look13_9 (grst rr13_9 (c1101, true, inst13)).
Definition f13_10 : N * N * N * N := Eval vm_compute in
  nth 9 (fst (fst fall13)) (0, 0, 0, 1)%N.
Definition rr13_10 : nat := Eval vm_compute in N.to_nat (fst (fst (fst f13_10))).
Definition R13_10 : nat := Eval vm_compute in N.to_nat (snd (fst f13_10)).
Definition kq13_10 : nat := Eval vm_compute in N.to_nat (snd f13_10).
Definition cc13_10 : nat := Eval vm_compute in N.to_nat ((snd (fst (fst f13_10)) + N.of_nat look13_10 - s13_10) / N.of_nat p13_10).
Definition uu13_10 : nat := Eval vm_compute in N.to_nat ((snd (fst (fst f13_10)) + N.of_nat look13_10 - s13_10) mod N.of_nat p13_10).
Definition jj13_10 : nat := Eval vm_compute in (N13_10 - cc13_10 - 1) mod kq13_10.
Definition S13_10 : sst := Eval vm_compute in
  gcut look13_10 (grst rr13_10 (c1101, true, inst13)).
Definition f13_11 : N * N * N * N := Eval vm_compute in
  nth 10 (fst (fst fall13)) (0, 0, 0, 1)%N.
Definition rr13_11 : nat := Eval vm_compute in N.to_nat (fst (fst (fst f13_11))).
Definition R13_11 : nat := Eval vm_compute in N.to_nat (snd (fst f13_11)).
Definition kq13_11 : nat := Eval vm_compute in N.to_nat (snd f13_11).
Definition cc13_11 : nat := Eval vm_compute in N.to_nat ((snd (fst (fst f13_11)) + N.of_nat look13_11 - s13_11) / N.of_nat p13_11).
Definition uu13_11 : nat := Eval vm_compute in N.to_nat ((snd (fst (fst f13_11)) + N.of_nat look13_11 - s13_11) mod N.of_nat p13_11).
Definition jj13_11 : nat := Eval vm_compute in (N13_11 - cc13_11 - 1) mod kq13_11.
Definition S13_11 : sst := Eval vm_compute in
  gcut look13_11 (grst rr13_11 (c1101, true, inst13)).
Definition fe13 : N * N := Eval vm_compute in snd (fst fall13).
Definition rre13 : nat := Eval vm_compute in N.to_nat (fst fe13).
Definition ue13 : nat := Eval vm_compute in
  N.to_nat (snd fe13 + N.of_nat looke13 - (s13_11 + N.of_nat (N13_11 * p13_11))).
Definition Se13 : sst := Eval vm_compute in gcut looke13 (grst rre13 (c1101, true, inst13)).
Definition Rj13_0 : nat := rr13_1.
Definition Rj13_1 : nat := Eval vm_compute in
  rr13_2 - rr13_1 - R13_1 * ((N13_1 - cc13_1 - 1 - jj13_1) / kq13_1).
Definition Rj13_2 : nat := Eval vm_compute in
  rr13_3 - rr13_2 - R13_2 * ((N13_2 - cc13_2 - 1 - jj13_2) / kq13_2).
Definition Rj13_3 : nat := Eval vm_compute in
  rr13_4 - rr13_3 - R13_3 * ((N13_3 - cc13_3 - 1 - jj13_3) / kq13_3).
Definition Rj13_4 : nat := Eval vm_compute in
  rr13_5 - rr13_4 - R13_4 * ((N13_4 - cc13_4 - 1 - jj13_4) / kq13_4).
Definition Rj13_5 : nat := Eval vm_compute in
  rr13_6 - rr13_5 - R13_5 * ((N13_5 - cc13_5 - 1 - jj13_5) / kq13_5).
Definition Rj13_6 : nat := Eval vm_compute in
  rr13_7 - rr13_6 - R13_6 * ((N13_6 - cc13_6 - 1 - jj13_6) / kq13_6).
Definition Rj13_7 : nat := Eval vm_compute in
  rr13_8 - rr13_7 - R13_7 * ((N13_7 - cc13_7 - 1 - jj13_7) / kq13_7).
Definition Rj13_8 : nat := Eval vm_compute in
  rr13_9 - rr13_8 - R13_8 * ((N13_8 - cc13_8 - 1 - jj13_8) / kq13_8).
Definition Rj13_9 : nat := Eval vm_compute in
  rr13_10 - rr13_9 - R13_9 * ((N13_9 - cc13_9 - 1 - jj13_9) / kq13_9).
Definition Rj13_10 : nat := Eval vm_compute in
  rr13_11 - rr13_10 - R13_10 * ((N13_10 - cc13_10 - 1 - jj13_10) / kq13_10).
Definition Rj13_11 : nat := Eval vm_compute in
  rre13 - rr13_11 - R13_11 * ((N13_11 - cc13_11 - 1 - jj13_11) / kq13_11).

(** ** The cuts *)

Definition u13_1 : list bool := firstn uu13_1 E13_1.
Definition v13_1 : list bool := skipn uu13_1 E13_1.
Definition u13_2 : list bool := firstn uu13_2 E13_2.
Definition v13_2 : list bool := skipn uu13_2 E13_2.
Definition u13_3 : list bool := firstn uu13_3 E13_3.
Definition v13_3 : list bool := skipn uu13_3 E13_3.
Definition u13_4 : list bool := firstn uu13_4 E13_4.
Definition v13_4 : list bool := skipn uu13_4 E13_4.
Definition u13_5 : list bool := firstn uu13_5 E13_5.
Definition v13_5 : list bool := skipn uu13_5 E13_5.
Definition u13_6 : list bool := firstn uu13_6 E13_6.
Definition v13_6 : list bool := skipn uu13_6 E13_6.
Definition u13_7 : list bool := firstn uu13_7 E13_7.
Definition v13_7 : list bool := skipn uu13_7 E13_7.
Definition u13_8 : list bool := firstn uu13_8 E13_8.
Definition v13_8 : list bool := skipn uu13_8 E13_8.
Definition u13_9 : list bool := firstn uu13_9 E13_9.
Definition v13_9 : list bool := skipn uu13_9 E13_9.
Definition u13_10 : list bool := firstn uu13_10 E13_10.
Definition v13_10 : list bool := skipn uu13_10 E13_10.
Definition u13_11 : list bool := firstn uu13_11 E13_11.
Definition v13_11 : list bool := skipn uu13_11 E13_11.
Definition F13_0 : list bool := Hd13 ++ rp E13_1 cc13_1 ++ u13_1.
Definition C13_1 : list bool := v13_1 ++ u13_1.
Definition K13_1 : list bool := rp C13_1 kq13_1.
Lemma tl13_1 : rp E13_1 (jj13_1 + 1) = u13_1 ++ rp C13_1 jj13_1 ++ v13_1.
Proof. vm_compute. reflexivity. Qed.
Definition F13_1 : list bool :=
  (rp C13_1 jj13_1 ++ v13_1) ++ J13_1 ++ rp E13_2 cc13_2 ++ u13_2.
Definition C13_2 : list bool := v13_2 ++ u13_2.
Definition K13_2 : list bool := rp C13_2 kq13_2.
Lemma tl13_2 : rp E13_2 (jj13_2 + 1) = u13_2 ++ rp C13_2 jj13_2 ++ v13_2.
Proof. vm_compute. reflexivity. Qed.
Definition F13_2 : list bool :=
  (rp C13_2 jj13_2 ++ v13_2) ++ J13_2 ++ rp E13_3 cc13_3 ++ u13_3.
Definition C13_3 : list bool := v13_3 ++ u13_3.
Definition K13_3 : list bool := rp C13_3 kq13_3.
Lemma tl13_3 : rp E13_3 (jj13_3 + 1) = u13_3 ++ rp C13_3 jj13_3 ++ v13_3.
Proof. vm_compute. reflexivity. Qed.
Definition F13_3 : list bool :=
  (rp C13_3 jj13_3 ++ v13_3) ++ J13_3 ++ rp E13_4 cc13_4 ++ u13_4.
Definition C13_4 : list bool := v13_4 ++ u13_4.
Definition K13_4 : list bool := rp C13_4 kq13_4.
Lemma tl13_4 : rp E13_4 (jj13_4 + 1) = u13_4 ++ rp C13_4 jj13_4 ++ v13_4.
Proof. vm_compute. reflexivity. Qed.
Definition F13_4 : list bool :=
  (rp C13_4 jj13_4 ++ v13_4) ++ J13_4 ++ rp E13_5 cc13_5 ++ u13_5.
Definition C13_5 : list bool := v13_5 ++ u13_5.
Definition K13_5 : list bool := rp C13_5 kq13_5.
Lemma tl13_5 : rp E13_5 (jj13_5 + 1) = u13_5 ++ rp C13_5 jj13_5 ++ v13_5.
Proof. vm_compute. reflexivity. Qed.
Definition F13_5 : list bool :=
  (rp C13_5 jj13_5 ++ v13_5) ++ J13_5 ++ rp E13_6 cc13_6 ++ u13_6.
Definition C13_6 : list bool := v13_6 ++ u13_6.
Definition K13_6 : list bool := rp C13_6 kq13_6.
Lemma tl13_6 : rp E13_6 (jj13_6 + 1) = u13_6 ++ rp C13_6 jj13_6 ++ v13_6.
Proof. vm_compute. reflexivity. Qed.
Definition F13_6 : list bool :=
  (rp C13_6 jj13_6 ++ v13_6) ++ J13_6 ++ rp E13_7 cc13_7 ++ u13_7.
Definition C13_7 : list bool := v13_7 ++ u13_7.
Definition K13_7 : list bool := rp C13_7 kq13_7.
Lemma tl13_7 : rp E13_7 (jj13_7 + 1) = u13_7 ++ rp C13_7 jj13_7 ++ v13_7.
Proof. vm_compute. reflexivity. Qed.
Definition F13_7 : list bool :=
  (rp C13_7 jj13_7 ++ v13_7) ++ J13_7 ++ rp E13_8 cc13_8 ++ u13_8.
Definition C13_8 : list bool := v13_8 ++ u13_8.
Definition K13_8 : list bool := rp C13_8 kq13_8.
Lemma tl13_8 : rp E13_8 (jj13_8 + 1) = u13_8 ++ rp C13_8 jj13_8 ++ v13_8.
Proof. vm_compute. reflexivity. Qed.
Definition F13_8 : list bool :=
  (rp C13_8 jj13_8 ++ v13_8) ++ J13_8 ++ rp E13_9 cc13_9 ++ u13_9.
Definition C13_9 : list bool := v13_9 ++ u13_9.
Definition K13_9 : list bool := rp C13_9 kq13_9.
Lemma tl13_9 : rp E13_9 (jj13_9 + 1) = u13_9 ++ rp C13_9 jj13_9 ++ v13_9.
Proof. vm_compute. reflexivity. Qed.
Definition F13_9 : list bool :=
  (rp C13_9 jj13_9 ++ v13_9) ++ J13_9 ++ rp E13_10 cc13_10 ++ u13_10.
Definition C13_10 : list bool := v13_10 ++ u13_10.
Definition K13_10 : list bool := rp C13_10 kq13_10.
Lemma tl13_10 : rp E13_10 (jj13_10 + 1) = u13_10 ++ rp C13_10 jj13_10 ++ v13_10.
Proof. vm_compute. reflexivity. Qed.
Definition F13_10 : list bool :=
  (rp C13_10 jj13_10 ++ v13_10) ++ J13_10 ++ rp E13_11 cc13_11 ++ u13_11.
Definition C13_11 : list bool := v13_11 ++ u13_11.
Definition K13_11 : list bool := rp C13_11 kq13_11.
Lemma tl13_11 : rp E13_11 (jj13_11 + 1) = u13_11 ++ rp C13_11 jj13_11 ++ v13_11.
Proof. vm_compute. reflexivity. Qed.
Definition F13_11 : list bool := (rp C13_11 jj13_11 ++ v13_11) ++ firstn ue13 J13_11.
Definition Fw13 : list bool := skipn ue13 J13_11 ++ w13.

Lemma cells13_cut : forall n1 n2 n3 n4 n5 n6 n7 n8 n9 n10 n11,
  cells13 (cc13_1 + (n1 * kq13_1 + jj13_1) + 1) (cc13_2 + (n2 * kq13_2 + jj13_2) + 1) (cc13_3 + (n3 *
    kq13_3 + jj13_3) + 1) (cc13_4 + (n4 * kq13_4 + jj13_4) + 1) (cc13_5 + (n5 * kq13_5 + jj13_5) +
    1) (cc13_6 + (n6 * kq13_6 + jj13_6) + 1) (cc13_7 + (n7 * kq13_7 + jj13_7) + 1) (cc13_8 + (n8 *
    kq13_8 + jj13_8) + 1) (cc13_9 + (n9 * kq13_9 + jj13_9) + 1) (cc13_10 + (n10 * kq13_10 + jj13_10)
    + 1) (cc13_11 + (n11 * kq13_11 + jj13_11) + 1) = (F13_0 ++ rp K13_1 n1 ++ F13_1 ++ rp K13_2 n2
    ++ F13_2 ++ rp K13_3 n3 ++ F13_3 ++ rp K13_4 n4 ++ F13_4 ++ rp K13_5 n5 ++ F13_5 ++ rp K13_6 n6
    ++ F13_6 ++ rp K13_7 n7 ++ F13_7 ++ rp K13_8 n8 ++ F13_8 ++ rp K13_9 n9 ++ F13_9 ++ rp K13_10
    n10 ++ F13_10 ++ rp K13_11 n11 ++ F13_11 ++ []) ++ Fw13.
Proof.
  intros n1 n2 n3 n4 n5 n6 n7 n8 n9 n10 n11. rewrite cells13_eq.
  replace (cc13_1 + (n1 * kq13_1 + jj13_1) + 1) with (cc13_1 + n1 * kq13_1 + (jj13_1 + 1)) by lia.
  rewrite (rp_recut E13_1 u13_1 v13_1 (n1 * kq13_1) cc13_1 (jj13_1 + 1) (rp C13_1 jj13_1 ++ v13_1)
             (eq_sym (firstn_skipn uu13_1 E13_1)) tl13_1).
  rewrite (rp_mul (v13_1 ++ u13_1) kq13_1 n1).
  replace (cc13_2 + (n2 * kq13_2 + jj13_2) + 1) with (cc13_2 + n2 * kq13_2 + (jj13_2 + 1)) by lia.
  rewrite (rp_recut E13_2 u13_2 v13_2 (n2 * kq13_2) cc13_2 (jj13_2 + 1) (rp C13_2 jj13_2 ++ v13_2)
             (eq_sym (firstn_skipn uu13_2 E13_2)) tl13_2).
  rewrite (rp_mul (v13_2 ++ u13_2) kq13_2 n2).
  replace (cc13_3 + (n3 * kq13_3 + jj13_3) + 1) with (cc13_3 + n3 * kq13_3 + (jj13_3 + 1)) by lia.
  rewrite (rp_recut E13_3 u13_3 v13_3 (n3 * kq13_3) cc13_3 (jj13_3 + 1) (rp C13_3 jj13_3 ++ v13_3)
             (eq_sym (firstn_skipn uu13_3 E13_3)) tl13_3).
  rewrite (rp_mul (v13_3 ++ u13_3) kq13_3 n3).
  replace (cc13_4 + (n4 * kq13_4 + jj13_4) + 1) with (cc13_4 + n4 * kq13_4 + (jj13_4 + 1)) by lia.
  rewrite (rp_recut E13_4 u13_4 v13_4 (n4 * kq13_4) cc13_4 (jj13_4 + 1) (rp C13_4 jj13_4 ++ v13_4)
             (eq_sym (firstn_skipn uu13_4 E13_4)) tl13_4).
  rewrite (rp_mul (v13_4 ++ u13_4) kq13_4 n4).
  replace (cc13_5 + (n5 * kq13_5 + jj13_5) + 1) with (cc13_5 + n5 * kq13_5 + (jj13_5 + 1)) by lia.
  rewrite (rp_recut E13_5 u13_5 v13_5 (n5 * kq13_5) cc13_5 (jj13_5 + 1) (rp C13_5 jj13_5 ++ v13_5)
             (eq_sym (firstn_skipn uu13_5 E13_5)) tl13_5).
  rewrite (rp_mul (v13_5 ++ u13_5) kq13_5 n5).
  replace (cc13_6 + (n6 * kq13_6 + jj13_6) + 1) with (cc13_6 + n6 * kq13_6 + (jj13_6 + 1)) by lia.
  rewrite (rp_recut E13_6 u13_6 v13_6 (n6 * kq13_6) cc13_6 (jj13_6 + 1) (rp C13_6 jj13_6 ++ v13_6)
             (eq_sym (firstn_skipn uu13_6 E13_6)) tl13_6).
  rewrite (rp_mul (v13_6 ++ u13_6) kq13_6 n6).
  replace (cc13_7 + (n7 * kq13_7 + jj13_7) + 1) with (cc13_7 + n7 * kq13_7 + (jj13_7 + 1)) by lia.
  rewrite (rp_recut E13_7 u13_7 v13_7 (n7 * kq13_7) cc13_7 (jj13_7 + 1) (rp C13_7 jj13_7 ++ v13_7)
             (eq_sym (firstn_skipn uu13_7 E13_7)) tl13_7).
  rewrite (rp_mul (v13_7 ++ u13_7) kq13_7 n7).
  replace (cc13_8 + (n8 * kq13_8 + jj13_8) + 1) with (cc13_8 + n8 * kq13_8 + (jj13_8 + 1)) by lia.
  rewrite (rp_recut E13_8 u13_8 v13_8 (n8 * kq13_8) cc13_8 (jj13_8 + 1) (rp C13_8 jj13_8 ++ v13_8)
             (eq_sym (firstn_skipn uu13_8 E13_8)) tl13_8).
  rewrite (rp_mul (v13_8 ++ u13_8) kq13_8 n8).
  replace (cc13_9 + (n9 * kq13_9 + jj13_9) + 1) with (cc13_9 + n9 * kq13_9 + (jj13_9 + 1)) by lia.
  rewrite (rp_recut E13_9 u13_9 v13_9 (n9 * kq13_9) cc13_9 (jj13_9 + 1) (rp C13_9 jj13_9 ++ v13_9)
             (eq_sym (firstn_skipn uu13_9 E13_9)) tl13_9).
  rewrite (rp_mul (v13_9 ++ u13_9) kq13_9 n9).
  replace (cc13_10 + (n10 * kq13_10 + jj13_10) + 1) with (cc13_10 + n10 * kq13_10 + (jj13_10 + 1)) by lia.
  rewrite (rp_recut E13_10 u13_10 v13_10 (n10 * kq13_10) cc13_10 (jj13_10 + 1) (rp C13_10 jj13_10 ++ v13_10)
             (eq_sym (firstn_skipn uu13_10 E13_10)) tl13_10).
  rewrite (rp_mul (v13_10 ++ u13_10) kq13_10 n10).
  replace (cc13_11 + (n11 * kq13_11 + jj13_11) + 1) with (cc13_11 + n11 * kq13_11 + (jj13_11 + 1)) by lia.
  rewrite (rp_recut E13_11 u13_11 v13_11 (n11 * kq13_11) cc13_11 (jj13_11 + 1) (rp C13_11 jj13_11 ++ v13_11)
             (eq_sym (firstn_skipn uu13_11 E13_11)) tl13_11).
  rewrite (rp_mul (v13_11 ++ u13_11) kq13_11 n11).
  rewrite <- (firstn_skipn ue13 J13_11) at 1.
  unfold F13_0, K13_1, F13_1, C13_1, K13_2, F13_2, C13_2, K13_3, F13_3, C13_3, K13_4, F13_4, C13_4, K13_5, F13_5, C13_5, K13_6, F13_6, C13_6, K13_7, F13_7, C13_7, K13_8, F13_8, C13_8, K13_9, F13_9, C13_9, K13_10, F13_10, C13_10, K13_11, F13_11, C13_11, Fw13.
  rewrite ?app_nil_r, <- ?app_assoc. reflexivity.
Qed.

(** ** Runs and cycles, round by round *)

Definition st130 : sst := (c1101, true, []).
Definition lF13_0 : list (Z * nat) := Eval vm_compute in grl Rj13_0 st130 F13_0.
Lemma RF13_0 : Run st130 F13_0 S13_1 (pSh lF13_0) (pV lF13_0).
Proof. apply (crun_run Rj13_0 4). vm_compute. reflexivity. Qed.
Definition lC13_1 : list (Z * nat) := Eval vm_compute in grl R13_1 S13_1 K13_1.
Lemma RC13_1 : Run S13_1 K13_1 S13_1 (pSh lC13_1) (pV lC13_1).
Proof. apply (crun_run R13_1 4). vm_compute. reflexivity. Qed.
Definition lF13_1 : list (Z * nat) := Eval vm_compute in grl Rj13_1 S13_1 F13_1.
Lemma RF13_1 : Run S13_1 F13_1 S13_2 (pSh lF13_1) (pV lF13_1).
Proof. apply (crun_run Rj13_1 4). vm_compute. reflexivity. Qed.
Definition lC13_2 : list (Z * nat) := Eval vm_compute in grl R13_2 S13_2 K13_2.
Lemma RC13_2 : Run S13_2 K13_2 S13_2 (pSh lC13_2) (pV lC13_2).
Proof. apply (crun_run R13_2 4). vm_compute. reflexivity. Qed.
Definition lF13_2 : list (Z * nat) := Eval vm_compute in grl Rj13_2 S13_2 F13_2.
Lemma RF13_2 : Run S13_2 F13_2 S13_3 (pSh lF13_2) (pV lF13_2).
Proof. apply (crun_run Rj13_2 4). vm_compute. reflexivity. Qed.
Definition lC13_3 : list (Z * nat) := Eval vm_compute in grl R13_3 S13_3 K13_3.
Lemma RC13_3 : Run S13_3 K13_3 S13_3 (pSh lC13_3) (pV lC13_3).
Proof. apply (crun_run R13_3 4). vm_compute. reflexivity. Qed.
Definition lF13_3 : list (Z * nat) := Eval vm_compute in grl Rj13_3 S13_3 F13_3.
Lemma RF13_3 : Run S13_3 F13_3 S13_4 (pSh lF13_3) (pV lF13_3).
Proof. apply (crun_run Rj13_3 4). vm_compute. reflexivity. Qed.
Definition lC13_4 : list (Z * nat) := Eval vm_compute in grl R13_4 S13_4 K13_4.
Lemma RC13_4 : Run S13_4 K13_4 S13_4 (pSh lC13_4) (pV lC13_4).
Proof. apply (crun_run R13_4 4). vm_compute. reflexivity. Qed.
Definition lF13_4 : list (Z * nat) := Eval vm_compute in grl Rj13_4 S13_4 F13_4.
Lemma RF13_4 : Run S13_4 F13_4 S13_5 (pSh lF13_4) (pV lF13_4).
Proof. apply (crun_run Rj13_4 4). vm_compute. reflexivity. Qed.
Definition lC13_5 : list (Z * nat) := Eval vm_compute in grl R13_5 S13_5 K13_5.
Lemma RC13_5 : Run S13_5 K13_5 S13_5 (pSh lC13_5) (pV lC13_5).
Proof. apply (crun_run R13_5 4). vm_compute. reflexivity. Qed.
Definition lF13_5 : list (Z * nat) := Eval vm_compute in grl Rj13_5 S13_5 F13_5.
Lemma RF13_5 : Run S13_5 F13_5 S13_6 (pSh lF13_5) (pV lF13_5).
Proof. apply (crun_run Rj13_5 4). vm_compute. reflexivity. Qed.
Definition lC13_6 : list (Z * nat) := Eval vm_compute in grl R13_6 S13_6 K13_6.
Lemma RC13_6 : Run S13_6 K13_6 S13_6 (pSh lC13_6) (pV lC13_6).
Proof. apply (crun_run R13_6 4). vm_compute. reflexivity. Qed.
Definition lF13_6 : list (Z * nat) := Eval vm_compute in grl Rj13_6 S13_6 F13_6.
Lemma RF13_6 : Run S13_6 F13_6 S13_7 (pSh lF13_6) (pV lF13_6).
Proof. apply (crun_run Rj13_6 4). vm_compute. reflexivity. Qed.
Definition lC13_7 : list (Z * nat) := Eval vm_compute in grl R13_7 S13_7 K13_7.
Lemma RC13_7 : Run S13_7 K13_7 S13_7 (pSh lC13_7) (pV lC13_7).
Proof. apply (crun_run R13_7 4). vm_compute. reflexivity. Qed.
Definition lF13_7 : list (Z * nat) := Eval vm_compute in grl Rj13_7 S13_7 F13_7.
Lemma RF13_7 : Run S13_7 F13_7 S13_8 (pSh lF13_7) (pV lF13_7).
Proof. apply (crun_run Rj13_7 4). vm_compute. reflexivity. Qed.
Definition lC13_8 : list (Z * nat) := Eval vm_compute in grl R13_8 S13_8 K13_8.
Lemma RC13_8 : Run S13_8 K13_8 S13_8 (pSh lC13_8) (pV lC13_8).
Proof. apply (crun_run R13_8 4). vm_compute. reflexivity. Qed.
Definition lF13_8 : list (Z * nat) := Eval vm_compute in grl Rj13_8 S13_8 F13_8.
Lemma RF13_8 : Run S13_8 F13_8 S13_9 (pSh lF13_8) (pV lF13_8).
Proof. apply (crun_run Rj13_8 4). vm_compute. reflexivity. Qed.
Definition lC13_9 : list (Z * nat) := Eval vm_compute in grl R13_9 S13_9 K13_9.
Lemma RC13_9 : Run S13_9 K13_9 S13_9 (pSh lC13_9) (pV lC13_9).
Proof. apply (crun_run R13_9 4). vm_compute. reflexivity. Qed.
Definition lF13_9 : list (Z * nat) := Eval vm_compute in grl Rj13_9 S13_9 F13_9.
Lemma RF13_9 : Run S13_9 F13_9 S13_10 (pSh lF13_9) (pV lF13_9).
Proof. apply (crun_run Rj13_9 4). vm_compute. reflexivity. Qed.
Definition lC13_10 : list (Z * nat) := Eval vm_compute in grl R13_10 S13_10 K13_10.
Lemma RC13_10 : Run S13_10 K13_10 S13_10 (pSh lC13_10) (pV lC13_10).
Proof. apply (crun_run R13_10 4). vm_compute. reflexivity. Qed.
Definition lF13_10 : list (Z * nat) := Eval vm_compute in grl Rj13_10 S13_10 F13_10.
Lemma RF13_10 : Run S13_10 F13_10 S13_11 (pSh lF13_10) (pV lF13_10).
Proof. apply (crun_run Rj13_10 4). vm_compute. reflexivity. Qed.
Definition lC13_11 : list (Z * nat) := Eval vm_compute in grl R13_11 S13_11 K13_11.
Lemma RC13_11 : Run S13_11 K13_11 S13_11 (pSh lC13_11) (pV lC13_11).
Proof. apply (crun_run R13_11 4). vm_compute. reflexivity. Qed.
Definition lF13_11 : list (Z * nat) := Eval vm_compute in grl Rj13_11 S13_11 F13_11.
Lemma RF13_11 : Run S13_11 F13_11 Se13 (pSh lF13_11) (pV lF13_11).
Proof. apply (crun_run Rj13_11 4). vm_compute. reflexivity. Qed.

Definition segs13 (n1 n2 n3 n4 n5 n6 n7 n8 n9 n10 n11 : nat) : list seg :=
  [SP lF13_0; SK lC13_1 n1; SP lF13_1; SK lC13_2 n2; SP lF13_2; SK lC13_3 n3; SP lF13_3; SK lC13_4 n4;
    SP lF13_4; SK lC13_5 n5; SP lF13_5; SK lC13_6 n6; SP lF13_6; SK lC13_7 n7; SP lF13_7; SK lC13_8
    n8; SP lF13_8; SK lC13_9 n9; SP lF13_9; SK lC13_10 n10; SP lF13_10; SK lC13_11 n11; SP lF13_11].

Lemma runA13 : forall n1 n2 n3 n4 n5 n6 n7 n8 n9 n10 n11,
  Run st130 (F13_0 ++ rp K13_1 n1 ++ F13_1 ++ rp K13_2 n2 ++ F13_2 ++ rp K13_3 n3 ++ F13_3 ++ rp K13_4
    n4 ++ F13_4 ++ rp K13_5 n5 ++ F13_5 ++ rp K13_6 n6 ++ F13_6 ++ rp K13_7 n7 ++ F13_7 ++ rp K13_8
    n8 ++ F13_8 ++ rp K13_9 n9 ++ F13_9 ++ rp K13_10 n10 ++ F13_10 ++ rp K13_11 n11 ++ F13_11 ++ [])
    Se13
      (segSh (segs13 n1 n2 n3 n4 n5 n6 n7 n8 n9 n10 n11)) (segV (segs13 n1 n2 n3 n4 n5 n6 n7 n8 n9 n10 n11)).
Proof.
  intros n1 n2 n3 n4 n5 n6 n7 n8 n9 n10 n11. unfold segs13.
  exact (run_SP _ _ _ _ _ _ _ RF13_0
    (run_SK _ _ _ _ _ _ _ RC13_1
    (run_SP _ _ _ _ _ _ _ RF13_1 (run_SK _ _ _ _ _ _ _ RC13_2
    (run_SP _ _ _ _ _ _ _ RF13_2 (run_SK _ _ _ _ _ _ _ RC13_3
    (run_SP _ _ _ _ _ _ _ RF13_3 (run_SK _ _ _ _ _ _ _ RC13_4
    (run_SP _ _ _ _ _ _ _ RF13_4 (run_SK _ _ _ _ _ _ _ RC13_5
    (run_SP _ _ _ _ _ _ _ RF13_5 (run_SK _ _ _ _ _ _ _ RC13_6
    (run_SP _ _ _ _ _ _ _ RF13_6 (run_SK _ _ _ _ _ _ _ RC13_7
    (run_SP _ _ _ _ _ _ _ RF13_7 (run_SK _ _ _ _ _ _ _ RC13_8
    (run_SP _ _ _ _ _ _ _ RF13_8 (run_SK _ _ _ _ _ _ _ RC13_9
    (run_SP _ _ _ _ _ _ _ RF13_9 (run_SK _ _ _ _ _ _ _ RC13_10
    (run_SP _ _ _ _ _ _ _ RF13_10 (run_SK _ _ _ _ _ _ _ RC13_11
    (run_SP _ _ _ _ _ _ _ RF13_11 (run_end _)))))))))))))))))))))))).
Qed.

(** ** The carry chain *)

Definition as13 := Eval vm_compute in asm 0 (segs13 O O O O O O O O O O O).
Definition k13_0 : list bool := Eval vm_compute in
  match as13 with Some ([Lit a; _; _; _; _; _; _; _; _; _; _; _; _; _; _; _; _; _; _; _; _; _; _], _) => a | _ => [] end.
Definition k13_1 : list bool := Eval vm_compute in
  match as13 with Some ([_; _; Lit a; _; _; _; _; _; _; _; _; _; _; _; _; _; _; _; _; _; _; _; _], _) => a | _ => [] end.
Definition k13_2 : list bool := Eval vm_compute in
  match as13 with Some ([_; _; _; _; Lit a; _; _; _; _; _; _; _; _; _; _; _; _; _; _; _; _; _; _], _) => a | _ => [] end.
Definition k13_3 : list bool := Eval vm_compute in
  match as13 with Some ([_; _; _; _; _; _; Lit a; _; _; _; _; _; _; _; _; _; _; _; _; _; _; _; _], _) => a | _ => [] end.
Definition k13_4 : list bool := Eval vm_compute in
  match as13 with Some ([_; _; _; _; _; _; _; _; Lit a; _; _; _; _; _; _; _; _; _; _; _; _; _; _], _) => a | _ => [] end.
Definition k13_5 : list bool := Eval vm_compute in
  match as13 with Some ([_; _; _; _; _; _; _; _; _; _; Lit a; _; _; _; _; _; _; _; _; _; _; _; _], _) => a | _ => [] end.
Definition k13_6 : list bool := Eval vm_compute in
  match as13 with Some ([_; _; _; _; _; _; _; _; _; _; _; _; Lit a; _; _; _; _; _; _; _; _; _; _], _) => a | _ => [] end.
Definition k13_7 : list bool := Eval vm_compute in
  match as13 with Some ([_; _; _; _; _; _; _; _; _; _; _; _; _; _; Lit a; _; _; _; _; _; _; _; _], _) => a | _ => [] end.
Definition k13_8 : list bool := Eval vm_compute in
  match as13 with Some ([_; _; _; _; _; _; _; _; _; _; _; _; _; _; _; _; Lit a; _; _; _; _; _; _], _) => a | _ => [] end.
Definition k13_9 : list bool := Eval vm_compute in
  match as13 with Some ([_; _; _; _; _; _; _; _; _; _; _; _; _; _; _; _; _; _; Lit a; _; _; _; _], _) => a | _ => [] end.
Definition k13_10 : list bool := Eval vm_compute in
  match as13 with Some ([_; _; _; _; _; _; _; _; _; _; _; _; _; _; _; _; _; _; _; _; Lit a; _; _], _) => a | _ => [] end.
Definition k13_11 : list bool := Eval vm_compute in
  match as13 with Some ([_; _; _; _; _; _; _; _; _; _; _; _; _; _; _; _; _; _; _; _; _; _; Lit a], _) => a | _ => [] end.
Definition kk13_1 : list bool := Eval vm_compute in
  match as13 with Some ([_; Rep p _; _; _; _; _; _; _; _; _; _; _; _; _; _; _; _; _; _; _; _; _; _], _) => p | _ => [] end.
Definition kk13_2 : list bool := Eval vm_compute in
  match as13 with Some ([_; _; _; Rep p _; _; _; _; _; _; _; _; _; _; _; _; _; _; _; _; _; _; _; _], _) => p | _ => [] end.
Definition kk13_3 : list bool := Eval vm_compute in
  match as13 with Some ([_; _; _; _; _; Rep p _; _; _; _; _; _; _; _; _; _; _; _; _; _; _; _; _; _], _) => p | _ => [] end.
Definition kk13_4 : list bool := Eval vm_compute in
  match as13 with Some ([_; _; _; _; _; _; _; Rep p _; _; _; _; _; _; _; _; _; _; _; _; _; _; _; _], _) => p | _ => [] end.
Definition kk13_5 : list bool := Eval vm_compute in
  match as13 with Some ([_; _; _; _; _; _; _; _; _; Rep p _; _; _; _; _; _; _; _; _; _; _; _; _; _], _) => p | _ => [] end.
Definition kk13_6 : list bool := Eval vm_compute in
  match as13 with Some ([_; _; _; _; _; _; _; _; _; _; _; Rep p _; _; _; _; _; _; _; _; _; _; _; _], _) => p | _ => [] end.
Definition kk13_7 : list bool := Eval vm_compute in
  match as13 with Some ([_; _; _; _; _; _; _; _; _; _; _; _; _; Rep p _; _; _; _; _; _; _; _; _; _], _) => p | _ => [] end.
Definition kk13_8 : list bool := Eval vm_compute in
  match as13 with Some ([_; _; _; _; _; _; _; _; _; _; _; _; _; _; _; Rep p _; _; _; _; _; _; _; _], _) => p | _ => [] end.
Definition kk13_9 : list bool := Eval vm_compute in
  match as13 with Some ([_; _; _; _; _; _; _; _; _; _; _; _; _; _; _; _; _; Rep p _; _; _; _; _; _], _) => p | _ => [] end.
Definition kk13_10 : list bool := Eval vm_compute in
  match as13 with Some ([_; _; _; _; _; _; _; _; _; _; _; _; _; _; _; _; _; _; _; Rep p _; _; _; _], _) => p | _ => [] end.
Definition kk13_11 : list bool := Eval vm_compute in
  match as13 with Some ([_; _; _; _; _; _; _; _; _; _; _; _; _; _; _; _; _; _; _; _; _; Rep p _; _], _) => p | _ => [] end.
Definition cB13 : Z := Eval vm_compute in match as13 with Some (_, c) => c | None => (-1)%Z end.

Lemma as13_ok : forall n1 n2 n3 n4 n5 n6 n7 n8 n9 n10 n11,
  asm 0 (segs13 n1 n2 n3 n4 n5 n6 n7 n8 n9 n10 n11) = Some ([Lit k13_0; Rep kk13_1 n1; Lit k13_1; Rep
    kk13_2 n2; Lit k13_2; Rep kk13_3 n3; Lit k13_3; Rep kk13_4 n4; Lit k13_4; Rep kk13_5 n5; Lit
    k13_5; Rep kk13_6 n6; Lit k13_6; Rep kk13_7 n7; Lit k13_7; Rep kk13_8 n8; Lit k13_8; Rep kk13_9
    n9; Lit k13_9; Rep kk13_10 n10; Lit k13_10; Rep kk13_11 n11; Lit k13_11], cB13).
Proof. intros n1 n2 n3 n4 n5 n6 n7 n8 n9 n10 n11. vm_compute. reflexivity. Qed.

(** ** The closing computation *)

Definition ec13 := Eval vm_compute in endcert 6000 (addpost Se13 Fw13).
Definition ae13 : Z := Eval vm_compute in match ec13 with Some (a, _, _, _) => a | None => 0%Z end.
Definition z1_13 : nat := Eval vm_compute in match ec13 with Some (_, z, _, _) => z | None => O end.
Definition z2_13 : nat := Eval vm_compute in match ec13 with Some (_, _, z, _) => z | None => O end.
Definition w14 : list bool := Eval vm_compute in match ec13 with Some (_, _, _, x) => x | None => [] end.
Definition la13 : nat := Eval vm_compute in (z1_13 + z2_13 - 1) / 3.
Definition tp13 : N := Eval vm_compute in Z.to_N ((cB13 + ae13) / 4 ^ Z.of_nat la13).
Definition ab13 : list bool := Eval vm_compute in
  zbits ((cB13 + ae13) mod 4 ^ Z.of_nat la13) (2 * la13).

Lemma ec13_ok : endcert 6000 (addpost Se13 Fw13) = Some (ae13, z1_13, z2_13, w14).
Proof. vm_compute. reflexivity. Qed.

Lemma cB13_nn : (0 <= cB13)%Z.
Proof. apply Z.leb_le. vm_compute. reflexivity. Qed.

Lemma ab13_val : (Z.of_N (bvalN ab13) + Z.of_N tp13 * pw4 la13 = cB13 + ae13)%Z.
Proof. vm_compute. reflexivity. Qed.

Lemma ab13_len : length ab13 = 2 * la13.
Proof. vm_compute. reflexivity. Qed.

Lemma z_13 : z1_13 + z2_13 = 3 * la13 + 1.
Proof. vm_compute. reflexivity. Qed.

Definition Cw13 (n1 n2 n3 n4 n5 n6 n7 n8 n9 n10 n11 : nat) : list bool :=
  den [Lit k13_0; Rep kk13_1 n1; Lit k13_1; Rep kk13_2 n2; Lit k13_2; Rep kk13_3 n3; Lit k13_3; Rep
    kk13_4 n4; Lit k13_4; Rep kk13_5 n5; Lit k13_5; Rep kk13_6 n6; Lit k13_6; Rep kk13_7 n7; Lit
    k13_7; Rep kk13_8 n8; Lit k13_8; Rep kk13_9 n9; Lit k13_9; Rep kk13_10 n10; Lit k13_10; Rep
    kk13_11 n11; Lit k13_11] ++ ab13.
Definition lc13 (n1 n2 n3 n4 n5 n6 n7 n8 n9 n10 n11 : nat) : nat := segSh (segs13 n1 n2 n3 n4 n5 n6 n7 n8 n9 n10 n11) + la13.

Lemma Cw13_len : forall n1 n2 n3 n4 n5 n6 n7 n8 n9 n10 n11, length (Cw13 n1 n2 n3 n4 n5 n6 n7 n8 n9 n10 n11) = 2 * lc13 n1 n2 n3 n4 n5 n6 n7 n8 n9 n10 n11.
Proof.
  intros n1 n2 n3 n4 n5 n6 n7 n8 n9 n10 n11.
  exact (proj1 (stageA st130 _ Se13 (segs13 n1 n2 n3 n4 n5 n6 n7 n8 n9 n10 n11) 6000 Fw13 ae13 z1_13 z2_13 w14 _ cB13 ab13 la13
              (Z.of_N tp13) (runA13 n1 n2 n3 n4 n5 n6 n7 n8 n9 n10 n11) ec13_ok (as13_ok n1 n2 n3 n4 n5 n6 n7 n8 n9 n10 n11) cB13_nn ab13_val ab13_len z_13)).
Qed.

Lemma end13 : forall n1 n2 n3 n4 n5 n6 n7 n8 n9 n10 n11 h k, (1 <= k)%nat -> exists n M',
  tickN 3 n (rep10 k ++ c1101 ++ repeat true (3 * h) ++ rep10 je13 ++ c1101 ++
             encb false (b13 (cc13_1 + (n1 * kq13_1 + jj13_1) + 1) (cc13_2 + (n2 * kq13_2 + jj13_2) + 1) (cc13_3
               + (n3 * kq13_3 + jj13_3) + 1) (cc13_4 + (n4 * kq13_4 + jj13_4) + 1) (cc13_5 + (n5 *
               kq13_5 + jj13_5) + 1) (cc13_6 + (n6 * kq13_6 + jj13_6) + 1) (cc13_7 + (n7 * kq13_7 +
               jj13_7) + 1) (cc13_8 + (n8 * kq13_8 + jj13_8) + 1) (cc13_9 + (n9 * kq13_9 + jj13_9) +
               1) (cc13_10 + (n10 * kq13_10 + jj13_10) + 1) (cc13_11 + (n11 * kq13_11 + jj13_11) +
               1)) ++ w13) =
    Some (Slev M' (3 * (h + lc13 n1 n2 n3 n4 n5 n6 n7 n8 n9 n10 n11) + 1) w14) /\
  Z.of_nat M' = (Z.of_nat k +
                 (Z.of_nat (bval (Cw13 n1 n2 n3 n4 n5 n6 n7 n8 n9 n10 n11)) + Z.of_N tp13 * pw4 (lc13 n1 n2 n3 n4 n5 n6 n7 n8 n9 n10 n11)) * pw4 h)%Z.
Proof.
  intros n1 n2 n3 n4 n5 n6 n7 n8 n9 n10 n11 h k Hk.
  destruct (stageA st130 _ Se13 (segs13 n1 n2 n3 n4 n5 n6 n7 n8 n9 n10 n11) 6000 Fw13 ae13 z1_13 z2_13 w14 _ cB13 ab13 la13
              (Z.of_N tp13) (runA13 n1 n2 n3 n4 n5 n6 n7 n8 n9 n10 n11) ec13_ok (as13_ok n1 n2 n3 n4 n5 n6 n7 n8 n9 n10 n11) cB13_nn ab13_val ab13_len z_13) as [_ H].
  destruct (H h k Hk) as [n [M' [E D]]]. exists n, M'. split; [| exact D].
  change (rep10 je13 ++ c1101 ++ encb false (b13 (cc13_1 + (n1 * kq13_1 + jj13_1) + 1) (cc13_2 + (n2 *
    kq13_2 + jj13_2) + 1) (cc13_3 + (n3 * kq13_3 + jj13_3) + 1) (cc13_4 + (n4 * kq13_4 + jj13_4) +
    1) (cc13_5 + (n5 * kq13_5 + jj13_5) + 1) (cc13_6 + (n6 * kq13_6 + jj13_6) + 1) (cc13_7 + (n7 *
    kq13_7 + jj13_7) + 1) (cc13_8 + (n8 * kq13_8 + jj13_8) + 1) (cc13_9 + (n9 * kq13_9 + jj13_9) +
    1) (cc13_10 + (n10 * kq13_10 + jj13_10) + 1) (cc13_11 + (n11 * kq13_11 + jj13_11) + 1)) ++ w13)
    with (cells13 (cc13_1 + (n1 * kq13_1 + jj13_1) + 1) (cc13_2 + (n2 * kq13_2 + jj13_2) + 1) (cc13_3 + (n3 * kq13_3 + jj13_3) + 1) (cc13_4 + (n4 * kq13_4 + jj13_4) + 1) (cc13_5 + (n5 * kq13_5 + jj13_5) + 1) (cc13_6 + (n6 * kq13_6 + jj13_6) + 1) (cc13_7 + (n7 * kq13_7 + jj13_7) + 1) (cc13_8 + (n8 * kq13_8 + jj13_8) + 1) (cc13_9 + (n9 * kq13_9 + jj13_9) + 1) (cc13_10 + (n10 * kq13_10 + jj13_10) + 1) (cc13_11 + (n11 * kq13_11 + jj13_11) + 1)).
  rewrite cells13_cut.
  cbv [st130 conc] in E. rewrite ?app_nil_r, <- ?app_assoc in E. rewrite ?app_nil_r, <- ?app_assoc.
  exact E.
Qed.

(** ** What the division needs: which blocks are tripled, and the residues of the counts *)

Definition cfg13_trip : list bool := Eval vm_compute in
  map (fun P => negb (N.eqb (bvalN P mod 3) 0)) [kk13_1; kk13_2; kk13_3; kk13_4; kk13_5; kk13_6; kk13_7; kk13_8; kk13_9; kk13_10; kk13_11].
Definition cfg13_rho : list N := Eval vm_compute in
  [(((rc13_1 + 1594323 - (N.of_nat cc13_1 + 1 + N.of_nat jj13_1)%N) * (N.of_nat kq13_1 mod 3)) mod 3)%N; (((rc13_2 + 1594323 - (N.of_nat cc13_2 + 1 + N.of_nat jj13_2)%N) * (N.of_nat kq13_2 mod 3)) mod 3)%N; (((rc13_3 + 1594323 - (N.of_nat cc13_3 + 1 + N.of_nat jj13_3)%N) * (N.of_nat kq13_3 mod 3)) mod 3)%N; (((rc13_4 + 1594323 - (N.of_nat cc13_4 + 1 + N.of_nat jj13_4)%N) * (N.of_nat kq13_4 mod 3)) mod 3)%N; (((rc13_5 + 1594323 - (N.of_nat cc13_5 + 1 + N.of_nat jj13_5)%N) * (N.of_nat kq13_5 mod 3)) mod 3)%N; (((rc13_6 + 1594323 - (N.of_nat cc13_6 + 1 + N.of_nat jj13_6)%N) * (N.of_nat kq13_6 mod 3)) mod 3)%N; (((rc13_7 + 1594323 - (N.of_nat cc13_7 + 1 + N.of_nat jj13_7)%N) * (N.of_nat kq13_7 mod 3)) mod 3)%N; (((rc13_8 + 1594323 - (N.of_nat cc13_8 + 1 + N.of_nat jj13_8)%N) * (N.of_nat kq13_8 mod 3)) mod 3)%N; (((rc13_9 + 1594323 - (N.of_nat cc13_9 + 1 + N.of_nat jj13_9)%N) * (N.of_nat kq13_9 mod 3)) mod 3)%N; (((rc13_10 + 1594323 - (N.of_nat cc13_10 + 1 + N.of_nat jj13_10)%N) * (N.of_nat kq13_10 mod 3)) mod 3)%N; (((rc13_11 + 1594323 - (N.of_nat cc13_11 + 1 + N.of_nat jj13_11)%N) * (N.of_nat kq13_11 mod 3)) mod 3)%N].
Definition cfg13_k : list nat := Eval vm_compute in [kq13_1; kq13_2; kq13_3; kq13_4; kq13_5; kq13_6; kq13_7; kq13_8; kq13_9; kq13_10; kq13_11].
Definition cfg13_j : list nat := Eval vm_compute in [jj13_1; jj13_2; jj13_3; jj13_4; jj13_5; jj13_6; jj13_7; jj13_8; jj13_9; jj13_10; jj13_11].
Definition cfg13_rhoT : Z := Eval vm_compute in ((2 * vT13) mod 3)%Z.

End L1314a.

Module L1314b.

(** * 1RB1LB_1RC0RD_0LA1RE_0RF1LC_1LA0RB_---1LC: from level 13 to level 14

    The division by 3 of [0100 (10)^(h-2) C] with the counts as variables, level 14 for the
    real counts, and the residues modulo 3^0 and lower bounds of the counts of level 14.
    Generated by a script. *)

Import Individual62.
Import T694_levels End694 Sym694 Lev694 Lvl1_694 Eng694 Cert694 Run694 Res694 Gen694.
Import L23 L34 L45 L56 L6i L67a L67b L78a L78b L89a L89b L910a L910b L1011a L1011b L1112a L1112b L1213a L1213b L1314a.
Import Lia Arith PeanoNat Bool NArith ZArith.
Import Coq.Lists.List.
Import ListNotations.

(** ** The division *)

Lemma Zl13_den : forall G x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11,
  [false; false; true; false] ++ rep01 (G * 3 + 2) ++ Cw13 x1 x2 x3 (x4 * 3 + 2) x5 (x6 * 3 + 1) (x7 * 3 + 2) x8 (x9 * 3 + 2) (x10 * 3 + 0) (x11 * 3 + 0) =
  den [Lit [false; false; true; false]; Rep (rp [false; true] 3) G; Lit (rp [false; true] 2 ++ k13_0);
    Rep kk13_1 x1; Lit (k13_1); Rep kk13_2 x2; Lit (k13_2); Rep kk13_3 x3; Lit (k13_3); Rep (rp
    kk13_4 3) x4; Lit (rp kk13_4 2 ++ k13_4); Rep kk13_5 x5; Lit (k13_5); Rep (rp kk13_6 3) x6; Lit
    (rp kk13_6 1 ++ k13_6); Rep (rp kk13_7 3) x7; Lit (rp kk13_7 2 ++ k13_7); Rep kk13_8 x8; Lit
    (k13_8); Rep (rp kk13_9 3) x9; Lit (rp kk13_9 2 ++ k13_9); Rep (rp kk13_10 3) x10; Lit (rp
    kk13_10 0 ++ k13_10); Rep (rp kk13_11 3) x11; Lit (rp kk13_11 0 ++ k13_11 ++ ab13)].
Proof.
  intros G x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11. unfold Cw13. cbn [den bden].
  change (rep01 (G * 3 + 2)) with (rp [false; true] (G * 3 + 2)).
  rewrite ?rp_add, ?rp_mul, ?app_nil_r, <- ?app_assoc. reflexivity.
Qed.

Definition dv13 := Eval vm_compute in
  dmB 3 [Lit [false; false; true; false]; Rep (rp [false; true] 3) O; Lit (rp [false; true] 2 ++
    k13_0); Rep kk13_1 O; Lit (k13_1); Rep kk13_2 O; Lit (k13_2); Rep kk13_3 O; Lit (k13_3); Rep (rp
    kk13_4 3) O; Lit (rp kk13_4 2 ++ k13_4); Rep kk13_5 O; Lit (k13_5); Rep (rp kk13_6 3) O; Lit (rp
    kk13_6 1 ++ k13_6); Rep (rp kk13_7 3) O; Lit (rp kk13_7 2 ++ k13_7); Rep kk13_8 O; Lit (k13_8);
    Rep (rp kk13_9 3) O; Lit (rp kk13_9 2 ++ k13_9); Rep (rp kk13_10 3) O; Lit (rp kk13_10 0 ++
    k13_10); Rep (rp kk13_11 3) O; Lit (rp kk13_11 0 ++ k13_11 ++ ab13)] tp13.
Definition a14_0 : list bool := Eval vm_compute in
  match dv13 with Some ([Lit a; _; _; _; _; _; _; _; _; _; _; _; _; _; _; _; _; _; _; _; _; _; _; _; _], _) => a | _ => [] end.
Definition a14_1 : list bool := Eval vm_compute in
  match dv13 with Some ([_; _; Lit a; _; _; _; _; _; _; _; _; _; _; _; _; _; _; _; _; _; _; _; _; _; _], _) => a | _ => [] end.
Definition a14_2 : list bool := Eval vm_compute in
  match dv13 with Some ([_; _; _; _; Lit a; _; _; _; _; _; _; _; _; _; _; _; _; _; _; _; _; _; _; _; _], _) => a | _ => [] end.
Definition a14_3 : list bool := Eval vm_compute in
  match dv13 with Some ([_; _; _; _; _; _; Lit a; _; _; _; _; _; _; _; _; _; _; _; _; _; _; _; _; _; _], _) => a | _ => [] end.
Definition a14_4 : list bool := Eval vm_compute in
  match dv13 with Some ([_; _; _; _; _; _; _; _; Lit a; _; _; _; _; _; _; _; _; _; _; _; _; _; _; _; _], _) => a | _ => [] end.
Definition a14_5 : list bool := Eval vm_compute in
  match dv13 with Some ([_; _; _; _; _; _; _; _; _; _; Lit a; _; _; _; _; _; _; _; _; _; _; _; _; _; _], _) => a | _ => [] end.
Definition a14_6 : list bool := Eval vm_compute in
  match dv13 with Some ([_; _; _; _; _; _; _; _; _; _; _; _; Lit a; _; _; _; _; _; _; _; _; _; _; _; _], _) => a | _ => [] end.
Definition a14_7 : list bool := Eval vm_compute in
  match dv13 with Some ([_; _; _; _; _; _; _; _; _; _; _; _; _; _; Lit a; _; _; _; _; _; _; _; _; _; _], _) => a | _ => [] end.
Definition a14_8 : list bool := Eval vm_compute in
  match dv13 with Some ([_; _; _; _; _; _; _; _; _; _; _; _; _; _; _; _; Lit a; _; _; _; _; _; _; _; _], _) => a | _ => [] end.
Definition a14_9 : list bool := Eval vm_compute in
  match dv13 with Some ([_; _; _; _; _; _; _; _; _; _; _; _; _; _; _; _; _; _; Lit a; _; _; _; _; _; _], _) => a | _ => [] end.
Definition a14_10 : list bool := Eval vm_compute in
  match dv13 with Some ([_; _; _; _; _; _; _; _; _; _; _; _; _; _; _; _; _; _; _; _; Lit a; _; _; _; _], _) => a | _ => [] end.
Definition a14_11 : list bool := Eval vm_compute in
  match dv13 with Some ([_; _; _; _; _; _; _; _; _; _; _; _; _; _; _; _; _; _; _; _; _; _; Lit a; _; _], _) => a | _ => [] end.
Definition a14_12 : list bool := Eval vm_compute in
  match dv13 with Some ([_; _; _; _; _; _; _; _; _; _; _; _; _; _; _; _; _; _; _; _; _; _; _; _; Lit a], _) => a | _ => [] end.
Definition P14_1 : list bool := Eval vm_compute in
  match dv13 with Some ([_; Rep p _; _; _; _; _; _; _; _; _; _; _; _; _; _; _; _; _; _; _; _; _; _; _; _], _) => p | _ => [] end.
Definition P14_2 : list bool := Eval vm_compute in
  match dv13 with Some ([_; _; _; Rep p _; _; _; _; _; _; _; _; _; _; _; _; _; _; _; _; _; _; _; _; _; _], _) => p | _ => [] end.
Definition P14_3 : list bool := Eval vm_compute in
  match dv13 with Some ([_; _; _; _; _; Rep p _; _; _; _; _; _; _; _; _; _; _; _; _; _; _; _; _; _; _; _], _) => p | _ => [] end.
Definition P14_4 : list bool := Eval vm_compute in
  match dv13 with Some ([_; _; _; _; _; _; _; Rep p _; _; _; _; _; _; _; _; _; _; _; _; _; _; _; _; _; _], _) => p | _ => [] end.
Definition P14_5 : list bool := Eval vm_compute in
  match dv13 with Some ([_; _; _; _; _; _; _; _; _; Rep p _; _; _; _; _; _; _; _; _; _; _; _; _; _; _; _], _) => p | _ => [] end.
Definition P14_6 : list bool := Eval vm_compute in
  match dv13 with Some ([_; _; _; _; _; _; _; _; _; _; _; Rep p _; _; _; _; _; _; _; _; _; _; _; _; _; _], _) => p | _ => [] end.
Definition P14_7 : list bool := Eval vm_compute in
  match dv13 with Some ([_; _; _; _; _; _; _; _; _; _; _; _; _; Rep p _; _; _; _; _; _; _; _; _; _; _; _], _) => p | _ => [] end.
Definition P14_8 : list bool := Eval vm_compute in
  match dv13 with Some ([_; _; _; _; _; _; _; _; _; _; _; _; _; _; _; Rep p _; _; _; _; _; _; _; _; _; _], _) => p | _ => [] end.
Definition P14_9 : list bool := Eval vm_compute in
  match dv13 with Some ([_; _; _; _; _; _; _; _; _; _; _; _; _; _; _; _; _; Rep p _; _; _; _; _; _; _; _], _) => p | _ => [] end.
Definition P14_10 : list bool := Eval vm_compute in
  match dv13 with Some ([_; _; _; _; _; _; _; _; _; _; _; _; _; _; _; _; _; _; _; Rep p _; _; _; _; _; _], _) => p | _ => [] end.
Definition P14_11 : list bool := Eval vm_compute in
  match dv13 with Some ([_; _; _; _; _; _; _; _; _; _; _; _; _; _; _; _; _; _; _; _; _; Rep p _; _; _; _], _) => p | _ => [] end.
Definition P14_12 : list bool := Eval vm_compute in
  match dv13 with Some ([_; _; _; _; _; _; _; _; _; _; _; _; _; _; _; _; _; _; _; _; _; _; _; Rep p _; _], _) => p | _ => [] end.
Definition r14 : N := Eval vm_compute in match dv13 with Some (_, r) => r | None => 9%N end.
Definition je14 : nat := Eval vm_compute in 3 + N.to_nat r14.

Lemma dv13_ok : forall G x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11,
  dmB 3 [Lit [false; false; true; false]; Rep (rp [false; true] 3) G; Lit (rp [false; true] 2 ++
    k13_0); Rep kk13_1 x1; Lit (k13_1); Rep kk13_2 x2; Lit (k13_2); Rep kk13_3 x3; Lit (k13_3); Rep
    (rp kk13_4 3) x4; Lit (rp kk13_4 2 ++ k13_4); Rep kk13_5 x5; Lit (k13_5); Rep (rp kk13_6 3) x6;
    Lit (rp kk13_6 1 ++ k13_6); Rep (rp kk13_7 3) x7; Lit (rp kk13_7 2 ++ k13_7); Rep kk13_8 x8; Lit
    (k13_8); Rep (rp kk13_9 3) x9; Lit (rp kk13_9 2 ++ k13_9); Rep (rp kk13_10 3) x10; Lit (rp
    kk13_10 0 ++ k13_10); Rep (rp kk13_11 3) x11; Lit (rp kk13_11 0 ++ k13_11 ++ ab13)] tp13 =
  Some ([Lit a14_0; Rep P14_1 G; Lit a14_1; Rep P14_2 x1; Lit a14_2; Rep P14_3 x2; Lit a14_3; Rep
    P14_4 x3; Lit a14_4; Rep P14_5 x4; Lit a14_5; Rep P14_6 x5; Lit a14_6; Rep P14_7 x6; Lit a14_7;
    Rep P14_8 x7; Lit a14_8; Rep P14_9 x8; Lit a14_9; Rep P14_10 x9; Lit a14_10; Rep P14_11 x10; Lit
    a14_11; Rep P14_12 x11; Lit a14_12], r14).
Proof. intros G x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11. vm_compute. reflexivity. Qed.

Lemma tp13_lt : (tp13 < 3)%N.
Proof. reflexivity. Qed.

(** ** Level 14 *)

Definition b14 (d1 d2 d3 d4 d5 d6 d7 d8 d9 d10 d11 d12 : nat) : list bool :=
  den [Lit a14_0; Rep P14_1 d1; Lit a14_1; Rep P14_2 d2; Lit a14_2; Rep P14_3 d3; Lit a14_3; Rep P14_4
    d4; Lit a14_4; Rep P14_5 d5; Lit a14_5; Rep P14_6 d6; Lit a14_6; Rep P14_7 d7; Lit a14_7; Rep
    P14_8 d8; Lit a14_8; Rep P14_9 d9; Lit a14_9; Rep P14_10 d10; Lit a14_10; Rep P14_11 d11; Lit
    a14_11; Rep P14_12 d12; Lit a14_12].

Definition c14_1 : nat := (2 * bval (b13 c13_1 c13_2 c13_3 c13_4 c13_5 c13_6 c13_7 c13_8 c13_9 c13_10 c13_11)) / 3.
Definition c14_2 : nat := ((c13_1 - (cc13_1 + 1 + jj13_1)) / kq13_1).
Definition c14_3 : nat := ((c13_2 - (cc13_2 + 1 + jj13_2)) / kq13_2).
Definition c14_4 : nat := ((c13_3 - (cc13_3 + 1 + jj13_3)) / kq13_3).
Definition c14_5 : nat := ((c13_4 - (cc13_4 + 1 + jj13_4)) / kq13_4) / 3.
Definition c14_6 : nat := ((c13_5 - (cc13_5 + 1 + jj13_5)) / kq13_5).
Definition c14_7 : nat := ((c13_6 - (cc13_6 + 1 + jj13_6)) / kq13_6) / 3.
Definition c14_8 : nat := ((c13_7 - (cc13_7 + 1 + jj13_7)) / kq13_7) / 3.
Definition c14_9 : nat := ((c13_8 - (cc13_8 + 1 + jj13_8)) / kq13_8).
Definition c14_10 : nat := ((c13_9 - (cc13_9 + 1 + jj13_9)) / kq13_9) / 3.
Definition c14_11 : nat := ((c13_10 - (cc13_10 + 1 + jj13_10)) / kq13_10) / 3.
Definition c14_12 : nat := ((c13_11 - (cc13_11 + 1 + jj13_11)) / kq13_11) / 3.

Lemma ET13 : 2 * bval (b13 c13_1 c13_2 c13_3 c13_4 c13_5 c13_6 c13_7 c13_8 c13_9 c13_10 c13_11) = c14_1 * 3 + 2.
Proof. pose proof T13_res as H. unfold vT13 in H. unfold c14_1. gl (bval (b13 c13_1 c13_2 c13_3 c13_4 c13_5 c13_6 c13_7 c13_8 c13_9 c13_10 c13_11)). Qed.

Lemma EC13_1 : c13_1 = cc13_1 + (c14_2 * kq13_1 + jj13_1) + 1.
Proof.
  pose proof c13_1_res as H. pose proof c13_1_res2 as H2. pose proof c13_1_lb as Hb.
  unfold rc13_1 in H. unfold rb13_1 in H2. unfold lb13_1 in Hb.
  unfold c14_2, cc13_1, kq13_1, jj13_1. cbn [Z.of_N] in H, H2, Hb. gl c13_1.
Qed.

Lemma EC13_2 : c13_2 = cc13_2 + (c14_3 * kq13_2 + jj13_2) + 1.
Proof.
  pose proof c13_2_res as H. pose proof c13_2_res2 as H2. pose proof c13_2_lb as Hb.
  unfold rc13_2 in H. unfold rb13_2 in H2. unfold lb13_2 in Hb.
  unfold c14_3, cc13_2, kq13_2, jj13_2. cbn [Z.of_N] in H, H2, Hb. gl c13_2.
Qed.

Lemma EC13_3 : c13_3 = cc13_3 + (c14_4 * kq13_3 + jj13_3) + 1.
Proof.
  pose proof c13_3_res as H. pose proof c13_3_res2 as H2. pose proof c13_3_lb as Hb.
  unfold rc13_3 in H. unfold rb13_3 in H2. unfold lb13_3 in Hb.
  unfold c14_4, cc13_3, kq13_3, jj13_3. cbn [Z.of_N] in H, H2, Hb. gl c13_3.
Qed.

Lemma EC13_4 : c13_4 = cc13_4 + ((c14_5 * 3 + 2) * kq13_4 + jj13_4) + 1.
Proof.
  pose proof c13_4_res as H. pose proof c13_4_res2 as H2. pose proof c13_4_lb as Hb.
  unfold rc13_4 in H. unfold rb13_4 in H2. unfold lb13_4 in Hb.
  unfold c14_5, cc13_4, kq13_4, jj13_4. cbn [Z.of_N] in H, H2, Hb. gl c13_4.
Qed.

Lemma EC13_5 : c13_5 = cc13_5 + (c14_6 * kq13_5 + jj13_5) + 1.
Proof.
  pose proof c13_5_res as H. pose proof c13_5_res2 as H2. pose proof c13_5_lb as Hb.
  unfold rc13_5 in H. unfold rb13_5 in H2. unfold lb13_5 in Hb.
  unfold c14_6, cc13_5, kq13_5, jj13_5. cbn [Z.of_N] in H, H2, Hb. gl c13_5.
Qed.

Lemma EC13_6 : c13_6 = cc13_6 + ((c14_7 * 3 + 1) * kq13_6 + jj13_6) + 1.
Proof.
  pose proof c13_6_res as H. pose proof c13_6_res2 as H2. pose proof c13_6_lb as Hb.
  unfold rc13_6 in H. unfold rb13_6 in H2. unfold lb13_6 in Hb.
  unfold c14_7, cc13_6, kq13_6, jj13_6. cbn [Z.of_N] in H, H2, Hb. gl c13_6.
Qed.

Lemma EC13_7 : c13_7 = cc13_7 + ((c14_8 * 3 + 2) * kq13_7 + jj13_7) + 1.
Proof.
  pose proof c13_7_res as H. pose proof c13_7_res2 as H2. pose proof c13_7_lb as Hb.
  unfold rc13_7 in H. unfold rb13_7 in H2. unfold lb13_7 in Hb.
  unfold c14_8, cc13_7, kq13_7, jj13_7. cbn [Z.of_N] in H, H2, Hb. gl c13_7.
Qed.

Lemma EC13_8 : c13_8 = cc13_8 + (c14_9 * kq13_8 + jj13_8) + 1.
Proof.
  pose proof c13_8_res as H. pose proof c13_8_res2 as H2. pose proof c13_8_lb as Hb.
  unfold rc13_8 in H. unfold rb13_8 in H2. unfold lb13_8 in Hb.
  unfold c14_9, cc13_8, kq13_8, jj13_8. cbn [Z.of_N] in H, H2, Hb. gl c13_8.
Qed.

Lemma EC13_9 : c13_9 = cc13_9 + ((c14_10 * 3 + 2) * kq13_9 + jj13_9) + 1.
Proof.
  pose proof c13_9_res as H. pose proof c13_9_res2 as H2. pose proof c13_9_lb as Hb.
  unfold rc13_9 in H. unfold rb13_9 in H2. unfold lb13_9 in Hb.
  unfold c14_10, cc13_9, kq13_9, jj13_9. cbn [Z.of_N] in H, H2, Hb. gl c13_9.
Qed.

Lemma EC13_10 : c13_10 = cc13_10 + ((c14_11 * 3 + 0) * kq13_10 + jj13_10) + 1.
Proof.
  pose proof c13_10_res as H. pose proof c13_10_res2 as H2. pose proof c13_10_lb as Hb.
  unfold rc13_10 in H. unfold rb13_10 in H2. unfold lb13_10 in Hb.
  unfold c14_11, cc13_10, kq13_10, jj13_10. cbn [Z.of_N] in H, H2, Hb. gl c13_10.
Qed.

Lemma EC13_11 : c13_11 = cc13_11 + ((c14_12 * 3 + 0) * kq13_11 + jj13_11) + 1.
Proof.
  pose proof c13_11_res as H. pose proof c13_11_res2 as H2. pose proof c13_11_lb as Hb.
  unfold rc13_11 in H. unfold rb13_11 in H2. unfold lb13_11 in Hb.
  unfold c14_12, cc13_11, kq13_11, jj13_11. cbn [Z.of_N] in H, H2, Hb. gl c13_11.
Qed.

Definition u14 : nat :=
  2 + 2 * bval (b13 (cc13_1 + (c14_2 * kq13_1 + jj13_1) + 1) (cc13_2 + (c14_3 * kq13_2 + jj13_2) + 1)
    (cc13_3 + (c14_4 * kq13_3 + jj13_3) + 1) (cc13_4 + ((c14_5 * 3 + 2) * kq13_4 + jj13_4) + 1)
    (cc13_5 + (c14_6 * kq13_5 + jj13_5) + 1) (cc13_6 + ((c14_7 * 3 + 1) * kq13_6 + jj13_6) + 1)
    (cc13_7 + ((c14_8 * 3 + 2) * kq13_7 + jj13_7) + 1) (cc13_8 + (c14_9 * kq13_8 + jj13_8) + 1)
    (cc13_9 + ((c14_10 * 3 + 2) * kq13_9 + jj13_9) + 1) (cc13_10 + ((c14_11 * 3 + 0) * kq13_10 +
    jj13_10) + 1) (cc13_11 + ((c14_12 * 3 + 0) * kq13_11 + jj13_11) + 1)) + lc13 c14_2 c14_3 c14_4
    (c14_5 * 3 + 2) c14_6 (c14_7 * 3 + 1) (c14_8 * 3 + 2) c14_9 (c14_10 * 3 + 2) (c14_11 * 3 + 0)
    (c14_12 * 3 + 0).

Theorem lvl14 : Lvl je14 (b14 c14_1 c14_2 c14_3 c14_4 c14_5 c14_6 c14_7 c14_8 c14_9 c14_10 c14_11 c14_12) u14 w14.
Proof.
  pose proof lvl13 as H. pose proof ET13 as HT.
  rewrite EC13_1 in H, HT.
  rewrite EC13_2 in H, HT.
  rewrite EC13_3 in H, HT.
  rewrite EC13_4 in H, HT.
  rewrite EC13_5 in H, HT.
  rewrite EC13_6 in H, HT.
  rewrite EC13_7 in H, HT.
  rewrite EC13_8 in H, HT.
  rewrite EC13_9 in H, HT.
  rewrite EC13_10 in H, HT.
  rewrite EC13_11 in H, HT.
  apply (level_next_top _ (b13 (cc13_1 + (c14_2 * kq13_1 + jj13_1) + 1) (cc13_2 + (c14_3 * kq13_2 +
    jj13_2) + 1) (cc13_3 + (c14_4 * kq13_3 + jj13_3) + 1) (cc13_4 + ((c14_5 * 3 + 2) * kq13_4 +
    jj13_4) + 1) (cc13_5 + (c14_6 * kq13_5 + jj13_5) + 1) (cc13_6 + ((c14_7 * 3 + 1) * kq13_6 +
    jj13_6) + 1) (cc13_7 + ((c14_8 * 3 + 2) * kq13_7 + jj13_7) + 1) (cc13_8 + (c14_9 * kq13_8 +
    jj13_8) + 1) (cc13_9 + ((c14_10 * 3 + 2) * kq13_9 + jj13_9) + 1) (cc13_10 + ((c14_11 * 3 + 0) *
    kq13_10 + jj13_10) + 1) (cc13_11 + ((c14_12 * 3 + 0) * kq13_11 + jj13_11) + 1)) _ w13 (Cw13
    c14_2 c14_3 c14_4 (c14_5 * 3 + 2) c14_6 (c14_7 * 3 + 1) (c14_8 * 3 + 2) c14_9 (c14_10 * 3 + 2)
    (c14_11 * 3 + 0) (c14_12 * 3 + 0)) (lc13 c14_2 c14_3 c14_4 (c14_5 * 3 + 2) c14_6 (c14_7 * 3 + 1)
    (c14_8 * 3 + 2) c14_9 (c14_10 * 3 + 2) (c14_11 * 3 + 0) (c14_12 * 3 + 0)) tp13 (b14 c14_1 c14_2
    c14_3 c14_4 c14_5 c14_6 c14_7 c14_8 c14_9 c14_10 c14_11 c14_12) r14 w14 H (Cw13_len _ _ _ _ _ _
    _ _ _ _ _) tp13_lt (fun k Hk => end13 _ _ _ _ _ _ _ _ _ _ _ _ k Hk)).
  rewrite HT, Zl13_den. apply dmB_sound. apply dv13_ok.
Qed.

(** ** The counts of level 14 modulo 3^0, and lower bounds *)

Definition rc14_1 : N := Eval vm_compute in Z.to_N (((2 * vT13 - 2) / 3) mod 1).
Lemma c14_1_res : (Z.of_nat c14_1 mod Z.of_N 1 = Z.of_N rc14_1)%Z.
Proof.
  pose proof T13_res as H. unfold vT13 in H. unfold c14_1, rc14_1. cbn [Z.of_N].
  gl (bval (b13 c13_1 c13_2 c13_3 c13_4 c13_5 c13_6 c13_7 c13_8 c13_9 c13_10 c13_11)).
Qed.
Definition lb14_1 : N := Eval vm_compute in ((2 * lbe13) / 3)%N.
Lemma c14_1_lb : (Z.of_N lb14_1 <= Z.of_nat c14_1)%Z.
Proof.
  pose proof (T13_lb c13_1 c13_2 c13_3 c13_4 c13_5 c13_6 c13_7 c13_8 c13_9 c13_10 c13_11) as H. unfold lbe13 in H. unfold c14_1, lb14_1.
  cbn [Z.of_N] in *. gl (bval (b13 c13_1 c13_2 c13_3 c13_4 c13_5 c13_6 c13_7 c13_8 c13_9 c13_10 c13_11)).
Qed.
Definition rb14_1 : N := Eval vm_compute in Z.to_N (((2 * Z.of_N t2_13 - 2) * 11) mod 32).
Lemma c14_1_res2 : (Z.of_nat c14_1 mod Z.of_N 32 = Z.of_N rb14_1)%Z.
Proof.
  pose proof T13_res as H. unfold vT13 in H.
  pose proof (T13_low c13_1 c13_2 c13_3 c13_4 c13_5 c13_6 c13_7 c13_8 c13_9 c13_10 c13_11) as H2. unfold t2_13 in H2.
  unfold c14_1, rb14_1. cbn [Z.of_N] in *. gl (bval (b13 c13_1 c13_2 c13_3 c13_4 c13_5 c13_6 c13_7 c13_8 c13_9 c13_10 c13_11)).
Qed.

Definition rc14_2 : N := Eval vm_compute in
  Z.to_N (((Z.of_N rc13_1 - (Z.of_nat cc13_1 + 1 + Z.of_nat jj13_1)) * 1) mod 1).
Definition lb14_2 : N := Eval vm_compute in ((lb13_1 - (N.of_nat cc13_1 + 1 + N.of_nat jj13_1)) / 1)%N.
Definition rb14_2 : N := Eval vm_compute in
  Z.to_N ((((Z.of_N rb13_1 - (Z.of_nat cc13_1 + 1 + Z.of_nat jj13_1)) mod 32) / 1) mod 32).
Lemma c14_2_res : (Z.of_nat c14_2 mod Z.of_N 1 = Z.of_N rc14_2)%Z.
Proof.
  pose proof c13_1_res as H. pose proof c13_1_res2 as H2. pose proof c13_1_lb as Hb.
  unfold rc13_1 in H. unfold rb13_1 in H2. unfold lb13_1 in Hb.
  unfold c14_2, rc14_2, cc13_1, kq13_1, jj13_1. cbn [Z.of_N] in *. gl c13_1.
Qed.
Lemma c14_2_res2 : (Z.of_nat c14_2 mod Z.of_N 32 = Z.of_N rb14_2)%Z.
Proof.
  pose proof c13_1_res as H. pose proof c13_1_res2 as H2. pose proof c13_1_lb as Hb.
  unfold rc13_1 in H. unfold rb13_1 in H2. unfold lb13_1 in Hb.
  unfold c14_2, rb14_2, cc13_1, kq13_1, jj13_1. cbn [Z.of_N] in *. gl c13_1.
Qed.
Lemma c14_2_lb : (Z.of_N lb14_2 <= Z.of_nat c14_2)%Z.
Proof.
  pose proof c13_1_res as H. pose proof c13_1_res2 as H2. pose proof c13_1_lb as Hb.
  unfold rc13_1 in H. unfold rb13_1 in H2. unfold lb13_1 in Hb.
  unfold c14_2, lb14_2, cc13_1, kq13_1, jj13_1. cbn [Z.of_N] in *. gl c13_1.
Qed.

Definition rc14_3 : N := Eval vm_compute in
  Z.to_N (((Z.of_N rc13_2 - (Z.of_nat cc13_2 + 1 + Z.of_nat jj13_2)) * 2) mod 1).
Definition lb14_3 : N := Eval vm_compute in ((lb13_2 - (N.of_nat cc13_2 + 1 + N.of_nat jj13_2)) / 2)%N.
Definition rb14_3 : N := Eval vm_compute in
  Z.to_N ((((Z.of_N rb13_2 - (Z.of_nat cc13_2 + 1 + Z.of_nat jj13_2)) mod 32) / 2) mod 16).
Lemma c14_3_res : (Z.of_nat c14_3 mod Z.of_N 1 = Z.of_N rc14_3)%Z.
Proof.
  pose proof c13_2_res as H. pose proof c13_2_res2 as H2. pose proof c13_2_lb as Hb.
  unfold rc13_2 in H. unfold rb13_2 in H2. unfold lb13_2 in Hb.
  unfold c14_3, rc14_3, cc13_2, kq13_2, jj13_2. cbn [Z.of_N] in *. gl c13_2.
Qed.
Lemma c14_3_res2 : (Z.of_nat c14_3 mod Z.of_N 16 = Z.of_N rb14_3)%Z.
Proof.
  pose proof c13_2_res as H. pose proof c13_2_res2 as H2. pose proof c13_2_lb as Hb.
  unfold rc13_2 in H. unfold rb13_2 in H2. unfold lb13_2 in Hb.
  unfold c14_3, rb14_3, cc13_2, kq13_2, jj13_2. cbn [Z.of_N] in *. gl c13_2.
Qed.
Lemma c14_3_lb : (Z.of_N lb14_3 <= Z.of_nat c14_3)%Z.
Proof.
  pose proof c13_2_res as H. pose proof c13_2_res2 as H2. pose proof c13_2_lb as Hb.
  unfold rc13_2 in H. unfold rb13_2 in H2. unfold lb13_2 in Hb.
  unfold c14_3, lb14_3, cc13_2, kq13_2, jj13_2. cbn [Z.of_N] in *. gl c13_2.
Qed.

Definition rc14_4 : N := Eval vm_compute in
  Z.to_N (((Z.of_N rc13_3 - (Z.of_nat cc13_3 + 1 + Z.of_nat jj13_3)) * 1) mod 1).
Definition lb14_4 : N := Eval vm_compute in ((lb13_3 - (N.of_nat cc13_3 + 1 + N.of_nat jj13_3)) / 1)%N.
Definition rb14_4 : N := Eval vm_compute in
  Z.to_N ((((Z.of_N rb13_3 - (Z.of_nat cc13_3 + 1 + Z.of_nat jj13_3)) mod 32) / 1) mod 32).
Lemma c14_4_res : (Z.of_nat c14_4 mod Z.of_N 1 = Z.of_N rc14_4)%Z.
Proof.
  pose proof c13_3_res as H. pose proof c13_3_res2 as H2. pose proof c13_3_lb as Hb.
  unfold rc13_3 in H. unfold rb13_3 in H2. unfold lb13_3 in Hb.
  unfold c14_4, rc14_4, cc13_3, kq13_3, jj13_3. cbn [Z.of_N] in *. gl c13_3.
Qed.
Lemma c14_4_res2 : (Z.of_nat c14_4 mod Z.of_N 32 = Z.of_N rb14_4)%Z.
Proof.
  pose proof c13_3_res as H. pose proof c13_3_res2 as H2. pose proof c13_3_lb as Hb.
  unfold rc13_3 in H. unfold rb13_3 in H2. unfold lb13_3 in Hb.
  unfold c14_4, rb14_4, cc13_3, kq13_3, jj13_3. cbn [Z.of_N] in *. gl c13_3.
Qed.
Lemma c14_4_lb : (Z.of_N lb14_4 <= Z.of_nat c14_4)%Z.
Proof.
  pose proof c13_3_res as H. pose proof c13_3_res2 as H2. pose proof c13_3_lb as Hb.
  unfold rc13_3 in H. unfold rb13_3 in H2. unfold lb13_3 in Hb.
  unfold c14_4, lb14_4, cc13_3, kq13_3, jj13_3. cbn [Z.of_N] in *. gl c13_3.
Qed.

Definition rc14_5 : N := Eval vm_compute in
  Z.to_N (((((Z.of_N rc13_4 - (Z.of_nat cc13_4 + 1 + Z.of_nat jj13_4)) * 1) mod 3) / 3) mod 1).
Definition lb14_5 : N := Eval vm_compute in (((lb13_4 - (N.of_nat cc13_4 + 1 + N.of_nat jj13_4)) / 1) / 3)%N.
Definition rb14_5 : N := Eval vm_compute in
  Z.to_N (((((Z.of_N rb13_4 - (Z.of_nat cc13_4 + 1 + Z.of_nat jj13_4)) mod 32) / 1 - 2) * 11) mod 32).
Lemma c14_5_res : (Z.of_nat c14_5 mod Z.of_N 1 = Z.of_N rc14_5)%Z.
Proof.
  pose proof c13_4_res as H. pose proof c13_4_res2 as H2. pose proof c13_4_lb as Hb.
  unfold rc13_4 in H. unfold rb13_4 in H2. unfold lb13_4 in Hb.
  unfold c14_5, rc14_5, cc13_4, kq13_4, jj13_4. cbn [Z.of_N] in *. gl c13_4.
Qed.
Lemma c14_5_res2 : (Z.of_nat c14_5 mod Z.of_N 32 = Z.of_N rb14_5)%Z.
Proof.
  pose proof c13_4_res as H. pose proof c13_4_res2 as H2. pose proof c13_4_lb as Hb.
  unfold rc13_4 in H. unfold rb13_4 in H2. unfold lb13_4 in Hb.
  unfold c14_5, rb14_5, cc13_4, kq13_4, jj13_4. cbn [Z.of_N] in *. gl c13_4.
Qed.
Lemma c14_5_lb : (Z.of_N lb14_5 <= Z.of_nat c14_5)%Z.
Proof.
  pose proof c13_4_res as H. pose proof c13_4_res2 as H2. pose proof c13_4_lb as Hb.
  unfold rc13_4 in H. unfold rb13_4 in H2. unfold lb13_4 in Hb.
  unfold c14_5, lb14_5, cc13_4, kq13_4, jj13_4. cbn [Z.of_N] in *. gl c13_4.
Qed.

Definition rc14_6 : N := Eval vm_compute in
  Z.to_N (((Z.of_N rc13_5 - (Z.of_nat cc13_5 + 1 + Z.of_nat jj13_5)) * 1) mod 1).
Definition lb14_6 : N := Eval vm_compute in ((lb13_5 - (N.of_nat cc13_5 + 1 + N.of_nat jj13_5)) / 1)%N.
Definition rb14_6 : N := Eval vm_compute in
  Z.to_N ((((Z.of_N rb13_5 - (Z.of_nat cc13_5 + 1 + Z.of_nat jj13_5)) mod 32) / 1) mod 32).
Lemma c14_6_res : (Z.of_nat c14_6 mod Z.of_N 1 = Z.of_N rc14_6)%Z.
Proof.
  pose proof c13_5_res as H. pose proof c13_5_res2 as H2. pose proof c13_5_lb as Hb.
  unfold rc13_5 in H. unfold rb13_5 in H2. unfold lb13_5 in Hb.
  unfold c14_6, rc14_6, cc13_5, kq13_5, jj13_5. cbn [Z.of_N] in *. gl c13_5.
Qed.
Lemma c14_6_res2 : (Z.of_nat c14_6 mod Z.of_N 32 = Z.of_N rb14_6)%Z.
Proof.
  pose proof c13_5_res as H. pose proof c13_5_res2 as H2. pose proof c13_5_lb as Hb.
  unfold rc13_5 in H. unfold rb13_5 in H2. unfold lb13_5 in Hb.
  unfold c14_6, rb14_6, cc13_5, kq13_5, jj13_5. cbn [Z.of_N] in *. gl c13_5.
Qed.
Lemma c14_6_lb : (Z.of_N lb14_6 <= Z.of_nat c14_6)%Z.
Proof.
  pose proof c13_5_res as H. pose proof c13_5_res2 as H2. pose proof c13_5_lb as Hb.
  unfold rc13_5 in H. unfold rb13_5 in H2. unfold lb13_5 in Hb.
  unfold c14_6, lb14_6, cc13_5, kq13_5, jj13_5. cbn [Z.of_N] in *. gl c13_5.
Qed.

Definition rc14_7 : N := Eval vm_compute in
  Z.to_N (((((Z.of_N rc13_6 - (Z.of_nat cc13_6 + 1 + Z.of_nat jj13_6)) * 1) mod 3) / 3) mod 1).
Definition lb14_7 : N := Eval vm_compute in (((lb13_6 - (N.of_nat cc13_6 + 1 + N.of_nat jj13_6)) / 1) / 3)%N.
Definition rb14_7 : N := Eval vm_compute in
  Z.to_N (((((Z.of_N rb13_6 - (Z.of_nat cc13_6 + 1 + Z.of_nat jj13_6)) mod 32) / 1 - 1) * 11) mod 32).
Lemma c14_7_res : (Z.of_nat c14_7 mod Z.of_N 1 = Z.of_N rc14_7)%Z.
Proof.
  pose proof c13_6_res as H. pose proof c13_6_res2 as H2. pose proof c13_6_lb as Hb.
  unfold rc13_6 in H. unfold rb13_6 in H2. unfold lb13_6 in Hb.
  unfold c14_7, rc14_7, cc13_6, kq13_6, jj13_6. cbn [Z.of_N] in *. gl c13_6.
Qed.
Lemma c14_7_res2 : (Z.of_nat c14_7 mod Z.of_N 32 = Z.of_N rb14_7)%Z.
Proof.
  pose proof c13_6_res as H. pose proof c13_6_res2 as H2. pose proof c13_6_lb as Hb.
  unfold rc13_6 in H. unfold rb13_6 in H2. unfold lb13_6 in Hb.
  unfold c14_7, rb14_7, cc13_6, kq13_6, jj13_6. cbn [Z.of_N] in *. gl c13_6.
Qed.
Lemma c14_7_lb : (Z.of_N lb14_7 <= Z.of_nat c14_7)%Z.
Proof.
  pose proof c13_6_res as H. pose proof c13_6_res2 as H2. pose proof c13_6_lb as Hb.
  unfold rc13_6 in H. unfold rb13_6 in H2. unfold lb13_6 in Hb.
  unfold c14_7, lb14_7, cc13_6, kq13_6, jj13_6. cbn [Z.of_N] in *. gl c13_6.
Qed.

Definition rc14_8 : N := Eval vm_compute in
  Z.to_N (((((Z.of_N rc13_7 - (Z.of_nat cc13_7 + 1 + Z.of_nat jj13_7)) * 1) mod 3) / 3) mod 1).
Definition lb14_8 : N := Eval vm_compute in (((lb13_7 - (N.of_nat cc13_7 + 1 + N.of_nat jj13_7)) / 1) / 3)%N.
Definition rb14_8 : N := Eval vm_compute in
  Z.to_N (((((Z.of_N rb13_7 - (Z.of_nat cc13_7 + 1 + Z.of_nat jj13_7)) mod 16) / 1 - 2) * 11) mod 16).
Lemma c14_8_res : (Z.of_nat c14_8 mod Z.of_N 1 = Z.of_N rc14_8)%Z.
Proof.
  pose proof c13_7_res as H. pose proof c13_7_res2 as H2. pose proof c13_7_lb as Hb.
  unfold rc13_7 in H. unfold rb13_7 in H2. unfold lb13_7 in Hb.
  unfold c14_8, rc14_8, cc13_7, kq13_7, jj13_7. cbn [Z.of_N] in *. gl c13_7.
Qed.
Lemma c14_8_res2 : (Z.of_nat c14_8 mod Z.of_N 16 = Z.of_N rb14_8)%Z.
Proof.
  pose proof c13_7_res as H. pose proof c13_7_res2 as H2. pose proof c13_7_lb as Hb.
  unfold rc13_7 in H. unfold rb13_7 in H2. unfold lb13_7 in Hb.
  unfold c14_8, rb14_8, cc13_7, kq13_7, jj13_7. cbn [Z.of_N] in *. gl c13_7.
Qed.
Lemma c14_8_lb : (Z.of_N lb14_8 <= Z.of_nat c14_8)%Z.
Proof.
  pose proof c13_7_res as H. pose proof c13_7_res2 as H2. pose proof c13_7_lb as Hb.
  unfold rc13_7 in H. unfold rb13_7 in H2. unfold lb13_7 in Hb.
  unfold c14_8, lb14_8, cc13_7, kq13_7, jj13_7. cbn [Z.of_N] in *. gl c13_7.
Qed.

Definition rc14_9 : N := Eval vm_compute in
  Z.to_N (((Z.of_N rc13_8 - (Z.of_nat cc13_8 + 1 + Z.of_nat jj13_8)) * 1) mod 1).
Definition lb14_9 : N := Eval vm_compute in ((lb13_8 - (N.of_nat cc13_8 + 1 + N.of_nat jj13_8)) / 1)%N.
Definition rb14_9 : N := Eval vm_compute in
  Z.to_N ((((Z.of_N rb13_8 - (Z.of_nat cc13_8 + 1 + Z.of_nat jj13_8)) mod 32) / 1) mod 32).
Lemma c14_9_res : (Z.of_nat c14_9 mod Z.of_N 1 = Z.of_N rc14_9)%Z.
Proof.
  pose proof c13_8_res as H. pose proof c13_8_res2 as H2. pose proof c13_8_lb as Hb.
  unfold rc13_8 in H. unfold rb13_8 in H2. unfold lb13_8 in Hb.
  unfold c14_9, rc14_9, cc13_8, kq13_8, jj13_8. cbn [Z.of_N] in *. gl c13_8.
Qed.
Lemma c14_9_res2 : (Z.of_nat c14_9 mod Z.of_N 32 = Z.of_N rb14_9)%Z.
Proof.
  pose proof c13_8_res as H. pose proof c13_8_res2 as H2. pose proof c13_8_lb as Hb.
  unfold rc13_8 in H. unfold rb13_8 in H2. unfold lb13_8 in Hb.
  unfold c14_9, rb14_9, cc13_8, kq13_8, jj13_8. cbn [Z.of_N] in *. gl c13_8.
Qed.
Lemma c14_9_lb : (Z.of_N lb14_9 <= Z.of_nat c14_9)%Z.
Proof.
  pose proof c13_8_res as H. pose proof c13_8_res2 as H2. pose proof c13_8_lb as Hb.
  unfold rc13_8 in H. unfold rb13_8 in H2. unfold lb13_8 in Hb.
  unfold c14_9, lb14_9, cc13_8, kq13_8, jj13_8. cbn [Z.of_N] in *. gl c13_8.
Qed.

Definition rc14_10 : N := Eval vm_compute in
  Z.to_N (((((Z.of_N rc13_9 - (Z.of_nat cc13_9 + 1 + Z.of_nat jj13_9)) * 1) mod 3) / 3) mod 1).
Definition lb14_10 : N := Eval vm_compute in (((lb13_9 - (N.of_nat cc13_9 + 1 + N.of_nat jj13_9)) / 1) / 3)%N.
Definition rb14_10 : N := Eval vm_compute in
  Z.to_N (((((Z.of_N rb13_9 - (Z.of_nat cc13_9 + 1 + Z.of_nat jj13_9)) mod 32) / 1 - 2) * 11) mod 32).
Lemma c14_10_res : (Z.of_nat c14_10 mod Z.of_N 1 = Z.of_N rc14_10)%Z.
Proof.
  pose proof c13_9_res as H. pose proof c13_9_res2 as H2. pose proof c13_9_lb as Hb.
  unfold rc13_9 in H. unfold rb13_9 in H2. unfold lb13_9 in Hb.
  unfold c14_10, rc14_10, cc13_9, kq13_9, jj13_9. cbn [Z.of_N] in *. gl c13_9.
Qed.
Lemma c14_10_res2 : (Z.of_nat c14_10 mod Z.of_N 32 = Z.of_N rb14_10)%Z.
Proof.
  pose proof c13_9_res as H. pose proof c13_9_res2 as H2. pose proof c13_9_lb as Hb.
  unfold rc13_9 in H. unfold rb13_9 in H2. unfold lb13_9 in Hb.
  unfold c14_10, rb14_10, cc13_9, kq13_9, jj13_9. cbn [Z.of_N] in *. gl c13_9.
Qed.
Lemma c14_10_lb : (Z.of_N lb14_10 <= Z.of_nat c14_10)%Z.
Proof.
  pose proof c13_9_res as H. pose proof c13_9_res2 as H2. pose proof c13_9_lb as Hb.
  unfold rc13_9 in H. unfold rb13_9 in H2. unfold lb13_9 in Hb.
  unfold c14_10, lb14_10, cc13_9, kq13_9, jj13_9. cbn [Z.of_N] in *. gl c13_9.
Qed.

Definition rc14_11 : N := Eval vm_compute in
  Z.to_N (((((Z.of_N rc13_10 - (Z.of_nat cc13_10 + 1 + Z.of_nat jj13_10)) * 1) mod 3) / 3) mod 1).
Definition lb14_11 : N := Eval vm_compute in (((lb13_10 - (N.of_nat cc13_10 + 1 + N.of_nat jj13_10)) / 1) / 3)%N.
Definition rb14_11 : N := Eval vm_compute in
  Z.to_N (((((Z.of_N rb13_10 - (Z.of_nat cc13_10 + 1 + Z.of_nat jj13_10)) mod 32) / 1 - 0) * 11) mod 32).
Lemma c14_11_res : (Z.of_nat c14_11 mod Z.of_N 1 = Z.of_N rc14_11)%Z.
Proof.
  pose proof c13_10_res as H. pose proof c13_10_res2 as H2. pose proof c13_10_lb as Hb.
  unfold rc13_10 in H. unfold rb13_10 in H2. unfold lb13_10 in Hb.
  unfold c14_11, rc14_11, cc13_10, kq13_10, jj13_10. cbn [Z.of_N] in *. gl c13_10.
Qed.
Lemma c14_11_res2 : (Z.of_nat c14_11 mod Z.of_N 32 = Z.of_N rb14_11)%Z.
Proof.
  pose proof c13_10_res as H. pose proof c13_10_res2 as H2. pose proof c13_10_lb as Hb.
  unfold rc13_10 in H. unfold rb13_10 in H2. unfold lb13_10 in Hb.
  unfold c14_11, rb14_11, cc13_10, kq13_10, jj13_10. cbn [Z.of_N] in *. gl c13_10.
Qed.
Lemma c14_11_lb : (Z.of_N lb14_11 <= Z.of_nat c14_11)%Z.
Proof.
  pose proof c13_10_res as H. pose proof c13_10_res2 as H2. pose proof c13_10_lb as Hb.
  unfold rc13_10 in H. unfold rb13_10 in H2. unfold lb13_10 in Hb.
  unfold c14_11, lb14_11, cc13_10, kq13_10, jj13_10. cbn [Z.of_N] in *. gl c13_10.
Qed.

Definition rc14_12 : N := Eval vm_compute in
  Z.to_N (((((Z.of_N rc13_11 - (Z.of_nat cc13_11 + 1 + Z.of_nat jj13_11)) * 1) mod 3) / 3) mod 1).
Definition lb14_12 : N := Eval vm_compute in (((lb13_11 - (N.of_nat cc13_11 + 1 + N.of_nat jj13_11)) / 1) / 3)%N.
Definition rb14_12 : N := Eval vm_compute in
  Z.to_N (((((Z.of_N rb13_11 - (Z.of_nat cc13_11 + 1 + Z.of_nat jj13_11)) mod 32) / 1 - 0) * 11) mod 32).
Lemma c14_12_res : (Z.of_nat c14_12 mod Z.of_N 1 = Z.of_N rc14_12)%Z.
Proof.
  pose proof c13_11_res as H. pose proof c13_11_res2 as H2. pose proof c13_11_lb as Hb.
  unfold rc13_11 in H. unfold rb13_11 in H2. unfold lb13_11 in Hb.
  unfold c14_12, rc14_12, cc13_11, kq13_11, jj13_11. cbn [Z.of_N] in *. gl c13_11.
Qed.
Lemma c14_12_res2 : (Z.of_nat c14_12 mod Z.of_N 32 = Z.of_N rb14_12)%Z.
Proof.
  pose proof c13_11_res as H. pose proof c13_11_res2 as H2. pose proof c13_11_lb as Hb.
  unfold rc13_11 in H. unfold rb13_11 in H2. unfold lb13_11 in Hb.
  unfold c14_12, rb14_12, cc13_11, kq13_11, jj13_11. cbn [Z.of_N] in *. gl c13_11.
Qed.
Lemma c14_12_lb : (Z.of_N lb14_12 <= Z.of_nat c14_12)%Z.
Proof.
  pose proof c13_11_res as H. pose proof c13_11_res2 as H2. pose proof c13_11_lb as Hb.
  unfold rc13_11 in H. unfold rb13_11 in H2. unfold lb13_11 in Hb.
  unfold c14_12, lb14_12, cc13_11, kq13_11, jj13_11. cbn [Z.of_N] in *. gl c13_11.
Qed.

(** ** The word of level 14 modulo 3^0 *)

Definition vT14 : Z := Eval vm_compute in
  gv (resW 1 [RL a14_0; RR P14_1 1 rc14_1; RL a14_1; RR P14_2 1 rc14_2; RL a14_2; RR P14_3 1 rc14_3;
    RL a14_3; RR P14_4 1 rc14_4; RL a14_4; RR P14_5 1 rc14_5; RL a14_5; RR P14_6 1 rc14_6; RL a14_6;
    RR P14_7 1 rc14_7; RL a14_7; RR P14_8 1 rc14_8; RL a14_8; RR P14_9 1 rc14_9; RL a14_9; RR P14_10
    1 rc14_10; RL a14_10; RR P14_11 1 rc14_11; RL a14_11; RR P14_12 1 rc14_12; RL a14_12]).

Lemma T14_res : (Z.of_nat (bval (b14 c14_1 c14_2 c14_3 c14_4 c14_5 c14_6 c14_7 c14_8 c14_9 c14_10 c14_11 c14_12)) mod 1 = vT14)%Z.
Proof.
  unfold b14.
  apply (resW_sound 1 [Lit a14_0; Rep P14_1 c14_1; Lit a14_1; Rep P14_2 c14_2; Lit a14_2; Rep P14_3
    c14_3; Lit a14_3; Rep P14_4 c14_4; Lit a14_4; Rep P14_5 c14_5; Lit a14_5; Rep P14_6 c14_6; Lit
    a14_6; Rep P14_7 c14_7; Lit a14_7; Rep P14_8 c14_8; Lit a14_8; Rep P14_9 c14_9; Lit a14_9; Rep
    P14_10 c14_10; Lit a14_10; Rep P14_11 c14_11; Lit a14_11; Rep P14_12 c14_12; Lit a14_12]
           [RL a14_0; RR P14_1 1 rc14_1; RL a14_1; RR P14_2 1 rc14_2; RL a14_2; RR P14_3 1 rc14_3; RL a14_3; RR
            P14_4 1 rc14_4; RL a14_4; RR P14_5 1 rc14_5; RL a14_5; RR P14_6 1 rc14_6; RL a14_6; RR
            P14_7 1 rc14_7; RL a14_7; RR P14_8 1 rc14_8; RL a14_8; RR P14_9 1 rc14_9; RL a14_9; RR
            P14_10 1 rc14_10; RL a14_10; RR P14_11 1 rc14_11; RL a14_11; RR P14_12 1 rc14_12; RL
            a14_12]);
    [lia | | vm_compute; reflexivity].
  exact (Forall2_cons _ _ (mL a14_0)
    (Forall2_cons _ _ (mR P14_1 c14_1 1%N rc14_1 c14_1_res)
    (Forall2_cons _ _ (mL a14_1)
    (Forall2_cons _ _ (mR P14_2 c14_2 1%N rc14_2 c14_2_res)
    (Forall2_cons _ _ (mL a14_2)
    (Forall2_cons _ _ (mR P14_3 c14_3 1%N rc14_3 c14_3_res)
    (Forall2_cons _ _ (mL a14_3)
    (Forall2_cons _ _ (mR P14_4 c14_4 1%N rc14_4 c14_4_res)
    (Forall2_cons _ _ (mL a14_4)
    (Forall2_cons _ _ (mR P14_5 c14_5 1%N rc14_5 c14_5_res)
    (Forall2_cons _ _ (mL a14_5)
    (Forall2_cons _ _ (mR P14_6 c14_6 1%N rc14_6 c14_6_res)
    (Forall2_cons _ _ (mL a14_6)
    (Forall2_cons _ _ (mR P14_7 c14_7 1%N rc14_7 c14_7_res)
    (Forall2_cons _ _ (mL a14_7)
    (Forall2_cons _ _ (mR P14_8 c14_8 1%N rc14_8 c14_8_res)
    (Forall2_cons _ _ (mL a14_8)
    (Forall2_cons _ _ (mR P14_9 c14_9 1%N rc14_9 c14_9_res)
    (Forall2_cons _ _ (mL a14_9)
    (Forall2_cons _ _ (mR P14_10 c14_10 1%N rc14_10 c14_10_res)
    (Forall2_cons _ _ (mL a14_10)
    (Forall2_cons _ _ (mR P14_11 c14_11 1%N rc14_11 c14_11_res)
    (Forall2_cons _ _ (mL a14_11)
    (Forall2_cons _ _ (mR P14_12 c14_12 1%N rc14_12 c14_12_res)
    (Forall2_cons _ _ (mL a14_12) (Forall2_nil _)))))))))))))))))))))))))).
Qed.

Definition lbe14 : N := Eval vm_compute in bvalN a14_12.

Lemma T14_lb : forall d1 d2 d3 d4 d5 d6 d7 d8 d9 d10 d11 d12, (Z.of_N lbe14 <= Z.of_nat (bval (b14 d1 d2 d3 d4 d5 d6 d7 d8 d9 d10 d11 d12)))%Z.
Proof.
  intros d1 d2 d3 d4 d5 d6 d7 d8 d9 d10 d11 d12. unfold b14. change lbe14 with (bvalN a14_12).
  exact (lbZ [Lit a14_0; Rep P14_1 d1; Lit a14_1; Rep P14_2 d2; Lit a14_2; Rep P14_3 d3; Lit a14_3;
    Rep P14_4 d4; Lit a14_4; Rep P14_5 d5; Lit a14_5; Rep P14_6 d6; Lit a14_6; Rep P14_7 d7; Lit
    a14_7; Rep P14_8 d8; Lit a14_8; Rep P14_9 d9; Lit a14_9; Rep P14_10 d10; Lit a14_10; Rep P14_11
    d11; Lit a14_11; Rep P14_12 d12] a14_12).
Qed.

Definition t2_14 : N := Eval vm_compute in bvalN a14_0.

Lemma T14_low : forall d1 d2 d3 d4 d5 d6 d7 d8 d9 d10 d11 d12, (Z.of_nat (bval (b14 d1 d2 d3 d4 d5 d6 d7 d8 d9 d10 d11 d12)) mod 16 = Z.of_N t2_14)%Z.
Proof.
  intros d1 d2 d3 d4 d5 d6 d7 d8 d9 d10 d11 d12. unfold b14.
  exact (bval_low_den a14_0 [Rep P14_1 d1; Lit a14_1; Rep P14_2 d2; Lit a14_2; Rep P14_3 d3; Lit
    a14_3; Rep P14_4 d4; Lit a14_4; Rep P14_5 d5; Lit a14_5; Rep P14_6 d6; Lit a14_6; Rep P14_7 d7;
    Lit a14_7; Rep P14_8 d8; Lit a14_8; Rep P14_9 d9; Lit a14_9; Rep P14_10 d10; Lit a14_10; Rep
    P14_11 d11; Lit a14_11; Rep P14_12 d12; Lit a14_12]).
Qed.

End L1314b.

Module Gate694.

(** * 1RB1LB_1RC0RD_0LA1RE_0RF1LC_1LA0RB_---1LC: the final gate

    From a level statement [Lvl je b u w] whose counter word ends (high bits) with a fixed top
    literal, the machine halts, provided the end phase of that level has been run (by the run
    engine) up to the cells of the top literal.  The last part, from the evaluator state at the
    top literal to the halt, is one computation of the symbolic evaluator [srun] of [Sym694]
    (sound for every hidden width).

    - [level_start]: from [Lvl] to the start of the end phase (bulk of the level);
    - [gate]: general form, any cut of the cells of the end phase into [Flo ++ Ftop];
    - [gate_top]: the cut at the top literal [tp] of [b = lo ++ tp] (low bits first);
    - [gate14]: [gate_top] with the level-14 top literal of the predicted chain ([top14], 104 bits);
    - [gate28], [gate28_state]: the cases that go through [prefix28_halts_all] literally;
    - [gate14_alone], [gate14_low]: the check of [gate14] run on two short words with the real
      top literal (a demonstration that the check succeeds, not a statement about the chain).

    Nothing here says that the chain reaches level 14. *)

Import Individual62.
Import T694_levels End694 Sym694 Lev694 Lvl1_694 Eng694 Cert694.
Import Lia Arith PeanoNat Bool NArith ZArith.
Import Coq.Lists.List.
Import ListNotations.

(** ** Runs without the value of the prefix *)

(** The evaluator state at the start of the end phase: the first counter [1^(3t)] behind
    [1101]. *)
Definition st0 : sst := (c1101, true, []).

Definition apost (st : sst) (F : list bool) : sst := let '(pre, x, post) := st in (pre, x, post ++ F).

Lemma conc_apost : forall t st F, conc t (apost st F) = conc t st ++ F.
Proof. intros t [[pre x] post] F. unfold apost, conc. rewrite <- ?app_assoc. reflexivity. Qed.

(** What the gate needs from a run: [Run694.Run st F st' sh a] without its second conjunct. *)
Definition RunW (st : sst) (F : list bool) (st' : sst) (sh : nat) : Prop :=
  forall t R k, exists n k',
    tickN 3 n (rep10 k ++ conc t st ++ F ++ R) = Some (rep10 k' ++ conc (t + sh) st' ++ R).

Lemma runw_of : forall (P : nat -> list bool -> nat -> nat -> Prop) st F st' sh,
  (forall t R k, exists n k',
     tickN 3 n (rep10 k ++ conc t st ++ F ++ R) = Some (rep10 k' ++ conc (t + sh) st' ++ R) /\
     P t R k k') ->
  RunW st F st' sh.
Proof.
  intros P st F st' sh H t R k. destruct (H t R k) as [n [k' [E _]]]. exists n, k'. exact E.
Qed.

(** The empty run: the cells [F] stay in the state. *)
Lemma runw_post : forall st F, RunW st F (apost st F) 0.
Proof.
  intros st F t R k. exists O, k. rewrite Nat.add_0_r, conc_apost, <- app_assoc. reflexivity.
Qed.

Lemma runw_comp : forall st F1 st1 sh1 F2 st2 sh2,
  RunW st F1 st1 sh1 -> RunW st1 F2 st2 sh2 -> RunW st (F1 ++ F2) st2 (sh1 + sh2).
Proof.
  intros st F1 st1 sh1 F2 st2 sh2 H1 H2 t R k.
  destruct (H1 t (F2 ++ R) k) as [n1 [k1 E1]]. destruct (H2 (t + sh1) R k1) as [n2 [k2 E2]].
  exists (n1 + n2), k2. rewrite <- app_assoc. apply (tickN_comp 3 n1 n2 _ _ _ E1).
  rewrite Nat.add_assoc. exact E2.
Qed.

(** ** From a level to its end phase *)

Theorem level_start : forall je b u w, Lvl je b u w -> exists n k,
  tickN 3 n D0 = Some (rep10 k ++ conc (2 + 2 * bval b) st0 ++ rep10 je ++ c1101 ++ encb false b ++ w).
Proof.
  intros je b u w [Hl [n0 H0]].
  assert (HT : bval b < 2 ^ (2 * u)) by (rewrite <- Hl; apply bval_lt).
  destruct (level_bulk_exact 3 je (bval b) u w HT) as [cnt [b' [Hb [Hv' [Hl' _]]]]].
  assert (Hbb : b' = b) by (apply bval_inj; lia). subst b'.
  exists (n0 + cnt), (kcyc 2 (bval b) 10).
  apply (tickN_comp 3 n0 cnt _ _ _ H0). rewrite Hb. unfold Ptape, conc, st0.
  replace (4 + 4 * bval b) with (2 * (2 + 2 * bval b)) by lia. rewrite encb_even2_nil.
  rewrite app_nil_r, <- ?app_assoc. reflexivity.
Qed.

(** ** The gate *)

Definition fin (o : option sst) : bool := match o with Some _ => true | None => false end.

Theorem gate : forall je b u w Flo Ftop S sh fuel,
  Lvl je b u w ->
  rep10 je ++ c1101 ++ encb false b ++ w = Flo ++ Ftop ->
  RunW st0 Flo S sh ->
  fin (srun fuel (apost S Ftop)) = true ->
  halts tm c0.
Proof.
  intros je b u w Flo Ftop S sh fuel HL Hc HR Hs.
  destruct (srun fuel (apost S Ftop)) as [S' |] eqn:E; [| discriminate].
  destruct (level_start je b u w HL) as [n0 [k0 H0]]. rewrite Hc in H0.
  destruct (HR (2 + 2 * bval b) Ftop k0) as [n1 [k1 H1]].
  destruct (srun_sound fuel _ _ E (2 + 2 * bval b + sh)) as [HRe HH].
  destruct (HRe k1) as [n2 [k2 H2]]. rewrite conc_apost in H2.
  apply (halt_from_ticks 3 (n0 + n1 + n2) (rep10 k2 ++ conc (2 + 2 * bval b + sh) S')).
  - apply (tickN_comp 3 (n0 + n1) n2 _ _ _ (tickN_comp 3 n0 n1 _ _ _ H0 H1) H2).
  - apply dpass_shift_halt. exact HH.
Qed.

Lemma par_even : forall lo l, length lo = 2 * l -> par false lo = false.
Proof.
  intros lo l Hl. rewrite (par_len lo (repeat false (2 * l) ++ [])).
  - rewrite par_rep2. reflexivity.
  - rewrite length_app, repeat_length. cbn [length]. lia.
Qed.

(** The cut at the top literal: [b = lo ++ tp] (low bits first), [lo] of even length; the run
    goes over the cells of [lo], the computation over those of [tp] and the tail [w]. *)
Theorem gate_top : forall je lo tp u w l S sh fuel,
  Lvl je (lo ++ tp) u w ->
  length lo = 2 * l ->
  RunW st0 (rep10 je ++ c1101 ++ encb false lo) S sh ->
  fin (srun fuel (apost S (encb false tp ++ w))) = true ->
  halts tm c0.
Proof.
  intros je lo tp u w l S sh fuel HL Hl HR Hs.
  apply (gate je (lo ++ tp) u w (rep10 je ++ c1101 ++ encb false lo) (encb false tp ++ w) S sh fuel HL);
    [| exact HR | exact Hs].
  rewrite encb_app, (par_even lo l Hl), <- ?app_assoc. reflexivity.
Qed.

(** ** Level 14 *)

(** The top literal of the level-14 word in the predicted chain, listed low bit first
    (the predicted chain, high bit first: 00 1^18 0^7 1 0100010100000110111010111101010001010110010110010111000100001001111011101011). *)
Definition top14 : list bool := [true; true; false; true; false; true; true; true; false; true; true; true; true; false; false; true; false; false; false; false; true; false; false; false; true; true; true; false; true; false; false; true; true; false; true; false; false; true; true; false; true; false; true; false; false; false; true; false; true; false; true; true; true; true; false; true; false; true; true; true; false; true; true; false; false; false; false; false; true; false; true; false; false; false; true; false; true; false; false; false; false; false; false; false; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; false; false].

Lemma top14_len : length top14 = 104.
Proof. reflexivity. Qed.

(** Its 28 high bits are [bits28] of [End694]. *)
Lemma top14_bits28 : skipn 76 top14 = bits28.
Proof. vm_compute. reflexivity. Qed.

Theorem gate14 : forall je lo u l S sh fuel,
  Lvl je (lo ++ top14) u [true] ->
  length lo = 2 * l ->
  RunW st0 (rep10 je ++ c1101 ++ encb false lo) S sh ->
  fin (srun fuel (apost S (encb false top14 ++ [true]))) = true ->
  halts tm c0.
Proof. intros je lo u l S sh fuel. apply gate_top. Qed.

(** ** Through [prefix28_halts_all] *)

(** A level-3 word that is just the 28 halting bits. *)
Theorem gate28 : forall u, Lvl 3 bits28 u [true] -> halts tm c0.
Proof.
  intros u HL. destruct (level_start 3 bits28 u [true] HL) as [n0 [k0 H0]].
  destruct (prefix28_halts_all (2 + 2 * bval bits28) k0) as [n1 [ds [E1 Hd]]].
  apply (halt_from_ticks 3 (n0 + n1) ds); [| exact Hd].
  apply (tickN_comp 3 n0 n1 _ _ _ H0). unfold start28, conc, st0 in *.
  rewrite app_nil_r, <- ?app_assoc in *. exact E1.
Qed.

(** A run that ends in the start shape of [start28] in front of the cells [encb false bits28 ++ [true]]. *)
Theorem gate28_state : forall je b u w Flo sh,
  Lvl je b u w ->
  rep10 je ++ c1101 ++ encb false b ++ w = Flo ++ encb false bits28 ++ [true] ->
  RunW st0 Flo (c1101, true, rep10 3 ++ c1101) sh ->
  halts tm c0.
Proof.
  intros je b u w Flo sh HL Hc HR.
  destruct (level_start je b u w HL) as [n0 [k0 H0]]. rewrite Hc in H0.
  destruct (HR (2 + 2 * bval b) (encb false bits28 ++ [true]) k0) as [n1 [k1 H1]].
  destruct (prefix28_halts_all (2 + 2 * bval b + sh) k1) as [n2 [ds [E2 Hd]]].
  apply (halt_from_ticks 3 (n0 + n1 + n2) ds); [| exact Hd].
  apply (tickN_comp 3 (n0 + n1) n2 _ _ _ (tickN_comp 3 n0 n1 _ _ _ H0 H1)).
  unfold start28, conc in *. rewrite <- ?app_assoc in *. exact E2.
Qed.

(** ** The check of [gate14] on two short words (demonstration) *)

(** The word is the top literal alone ([lo = []]). *)
Theorem gate14_alone : forall u, Lvl 3 top14 u [true] -> halts tm c0.
Proof.
  intros u HL.
  apply (gate14 3 [] u 0 (apost st0 (rep10 3 ++ c1101 ++ encb false [])) 0 2000 HL eq_refl
           (runw_post _ _)).
  vm_compute. reflexivity.
Qed.

(** A 228-bit low part made of the seven lowest blocks of the level-14 word of the predicted chain
    (counts 6, 6 and 2), below the top literal. *)
Definition low14 : list bool := [false; false; true; true; false; false; false; true; true; true; false; false; false; true; true; true; false; false; false; true; true; true; false; false; false; true; true; true; false; false; false; true; true; true; false; false; false; true; true; false; false; false; true; false; true; false; true; false; true; false; false; true; true; false; true; false; false; true; true; false; true; false; false; true; true; false; true; false; false; true; true; false; true; false; false; true; true; false; true; false; false; true; true; false; true; false; false; false; true; true; true; false; false; false; false; false; true; true; true; true; false; false; true; false; false; false; true; false; false; false; true; false; true; true; true; true; true; false; true; false; true; false; false; false; true; true; true; false; false; false; false; false; true; true; true; true; false; false; true; false; false; false; true; false; false; false; true; false; true; true; true; true; true; false; true; false; true; false; false; false; true; true; true; false; false; false; false; false; true; true; true; true; false; false; true; false; false; false; true; false; false; false; true; false; true; true; true; true; true; false; true; false; true; false; true; false; false; true; true; false; true; false; false; true; false; true; true; false; true; false; true; false; false; false; true; false; true; false; false; true; false; false; true; false; true; false; false; false].

Theorem gate14_low : forall u, Lvl 3 (low14 ++ top14) u [true] -> halts tm c0.
Proof.
  intros u HL.
  apply (gate14 3 low14 u 114 (apost st0 (rep10 3 ++ c1101 ++ encb false low14)) 0 2000 HL eq_refl
           (runw_post _ _)).
  vm_compute. reflexivity.
Qed.

End Gate694.

Module L14h.

(** * 1RB1LB_1RC0RD_0LA1RE_0RF1LC_1LA0RB_---1LC: the end phase of level 14

    Level 14 has class 3 and a counter word with 12 repeated blocks.  The end phase is
    certified round by round ([crun_run]): a run to the first block, then for each block a
    cycle per copy and a run across the next junction, and a closing computation.  The cuts
    are computed from the rounds of one instance.  Generated by a script. *)

Import Individual62.
Import T694_levels End694 Sym694 Lev694 Lvl1_694 Eng694 Cert694 Run694 Res694 Gen694.
Import L23 L34 L45 L56 L6i L67a L67b L78a L78b L89a L89b L910a L910b L1011a L1011b L1112a L1112b L1213a L1213b L1314a L1314b Gate694.
Import Lia Arith PeanoNat Bool NArith ZArith.
Import Coq.Lists.List.
Import ListNotations.

(** ** The cells of the counter word *)

Definition pa14_0 : bool := Eval vm_compute in par false a14_0.
Lemma pa14_0_eq : par false a14_0 = pa14_0.
Proof. vm_compute. reflexivity. Qed.
Definition pa14_1 : bool := Eval vm_compute in par pa14_0 a14_1.
Lemma pa14_1_eq : par pa14_0 a14_1 = pa14_1.
Proof. vm_compute. reflexivity. Qed.
Definition pa14_2 : bool := Eval vm_compute in par pa14_1 a14_2.
Lemma pa14_2_eq : par pa14_1 a14_2 = pa14_2.
Proof. vm_compute. reflexivity. Qed.
Definition pa14_3 : bool := Eval vm_compute in par pa14_2 a14_3.
Lemma pa14_3_eq : par pa14_2 a14_3 = pa14_3.
Proof. vm_compute. reflexivity. Qed.
Definition pa14_4 : bool := Eval vm_compute in par pa14_3 a14_4.
Lemma pa14_4_eq : par pa14_3 a14_4 = pa14_4.
Proof. vm_compute. reflexivity. Qed.
Definition pa14_5 : bool := Eval vm_compute in par pa14_4 a14_5.
Lemma pa14_5_eq : par pa14_4 a14_5 = pa14_5.
Proof. vm_compute. reflexivity. Qed.
Definition pa14_6 : bool := Eval vm_compute in par pa14_5 a14_6.
Lemma pa14_6_eq : par pa14_5 a14_6 = pa14_6.
Proof. vm_compute. reflexivity. Qed.
Definition pa14_7 : bool := Eval vm_compute in par pa14_6 a14_7.
Lemma pa14_7_eq : par pa14_6 a14_7 = pa14_7.
Proof. vm_compute. reflexivity. Qed.
Definition pa14_8 : bool := Eval vm_compute in par pa14_7 a14_8.
Lemma pa14_8_eq : par pa14_7 a14_8 = pa14_8.
Proof. vm_compute. reflexivity. Qed.
Definition pa14_9 : bool := Eval vm_compute in par pa14_8 a14_9.
Lemma pa14_9_eq : par pa14_8 a14_9 = pa14_9.
Proof. vm_compute. reflexivity. Qed.
Definition pa14_10 : bool := Eval vm_compute in par pa14_9 a14_10.
Lemma pa14_10_eq : par pa14_9 a14_10 = pa14_10.
Proof. vm_compute. reflexivity. Qed.
Definition pa14_11 : bool := Eval vm_compute in par pa14_10 a14_11.
Lemma pa14_11_eq : par pa14_10 a14_11 = pa14_11.
Proof. vm_compute. reflexivity. Qed.
Lemma pp14_1 : par pa14_0 P14_1 = pa14_0.
Proof. vm_compute. reflexivity. Qed.
Lemma pp14_2 : par pa14_1 P14_2 = pa14_1.
Proof. vm_compute. reflexivity. Qed.
Lemma pp14_3 : par pa14_2 P14_3 = pa14_2.
Proof. vm_compute. reflexivity. Qed.
Lemma pp14_4 : par pa14_3 P14_4 = pa14_3.
Proof. vm_compute. reflexivity. Qed.
Lemma pp14_5 : par pa14_4 P14_5 = pa14_4.
Proof. vm_compute. reflexivity. Qed.
Lemma pp14_6 : par pa14_5 P14_6 = pa14_5.
Proof. vm_compute. reflexivity. Qed.
Lemma pp14_7 : par pa14_6 P14_7 = pa14_6.
Proof. vm_compute. reflexivity. Qed.
Lemma pp14_8 : par pa14_7 P14_8 = pa14_7.
Proof. vm_compute. reflexivity. Qed.
Lemma pp14_9 : par pa14_8 P14_9 = pa14_8.
Proof. vm_compute. reflexivity. Qed.
Lemma pp14_10 : par pa14_9 P14_10 = pa14_9.
Proof. vm_compute. reflexivity. Qed.
Lemma pp14_11 : par pa14_10 P14_11 = pa14_10.
Proof. vm_compute. reflexivity. Qed.
Lemma pp14_12 : par pa14_11 P14_12 = pa14_11.
Proof. vm_compute. reflexivity. Qed.

Definition Hd14 : list bool := rep10 je14 ++ c1101 ++ encb false a14_0.
Definition E14_1 : list bool := encb pa14_0 P14_1.
Definition J14_1 : list bool := encb pa14_0 a14_1.
Definition E14_2 : list bool := encb pa14_1 P14_2.
Definition J14_2 : list bool := encb pa14_1 a14_2.
Definition E14_3 : list bool := encb pa14_2 P14_3.
Definition J14_3 : list bool := encb pa14_2 a14_3.
Definition E14_4 : list bool := encb pa14_3 P14_4.
Definition J14_4 : list bool := encb pa14_3 a14_4.
Definition E14_5 : list bool := encb pa14_4 P14_5.
Definition J14_5 : list bool := encb pa14_4 a14_5.
Definition E14_6 : list bool := encb pa14_5 P14_6.
Definition J14_6 : list bool := encb pa14_5 a14_6.
Definition E14_7 : list bool := encb pa14_6 P14_7.
Definition J14_7 : list bool := encb pa14_6 a14_7.
Definition E14_8 : list bool := encb pa14_7 P14_8.
Definition J14_8 : list bool := encb pa14_7 a14_8.
Definition E14_9 : list bool := encb pa14_8 P14_9.
Definition J14_9 : list bool := encb pa14_8 a14_9.
Definition E14_10 : list bool := encb pa14_9 P14_10.
Definition J14_10 : list bool := encb pa14_9 a14_10.
Definition E14_11 : list bool := encb pa14_10 P14_11.
Definition J14_11 : list bool := encb pa14_10 a14_11.
Definition E14_12 : list bool := encb pa14_11 P14_12.
Definition J14_12 : list bool := encb pa14_11 a14_12.

Definition cells14 (c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12 : nat) : list bool :=
  rep10 je14 ++ c1101 ++ encb false (b14 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12) ++ w14.

Lemma cells14_eq : forall c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12,
  cells14 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12 = Hd14 ++ rp E14_1 c1 ++ J14_1 ++ rp E14_2 c2 ++
    J14_2 ++ rp E14_3 c3 ++ J14_3 ++ rp E14_4 c4 ++ J14_4 ++ rp E14_5 c5 ++ J14_5 ++ rp E14_6 c6 ++
    J14_6 ++ rp E14_7 c7 ++ J14_7 ++ rp E14_8 c8 ++ J14_8 ++ rp E14_9 c9 ++ J14_9 ++ rp E14_10 c10
    ++ J14_10 ++ rp E14_11 c11 ++ J14_11 ++ rp E14_12 c12 ++ J14_12 ++ w14.
Proof.
  intros c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12. unfold cells14, b14, Hd14, E14_1, J14_1, E14_2, J14_2, E14_3, J14_3, E14_4, J14_4, E14_5, J14_5, E14_6, J14_6, E14_7, J14_7, E14_8, J14_8, E14_9, J14_9, E14_10, J14_10, E14_11, J14_11, E14_12, J14_12.
  cbn [den bden]. rewrite app_nil_r.
  rewrite (encb_app a14_0), pa14_0_eq.
  rewrite (encb_rp P14_1 pa14_0 pp14_1), (encb_app a14_1), pa14_1_eq.
  rewrite (encb_rp P14_2 pa14_1 pp14_2), (encb_app a14_2), pa14_2_eq.
  rewrite (encb_rp P14_3 pa14_2 pp14_3), (encb_app a14_3), pa14_3_eq.
  rewrite (encb_rp P14_4 pa14_3 pp14_4), (encb_app a14_4), pa14_4_eq.
  rewrite (encb_rp P14_5 pa14_4 pp14_5), (encb_app a14_5), pa14_5_eq.
  rewrite (encb_rp P14_6 pa14_5 pp14_6), (encb_app a14_6), pa14_6_eq.
  rewrite (encb_rp P14_7 pa14_6 pp14_7), (encb_app a14_7), pa14_7_eq.
  rewrite (encb_rp P14_8 pa14_7 pp14_8), (encb_app a14_8), pa14_8_eq.
  rewrite (encb_rp P14_9 pa14_8 pp14_9), (encb_app a14_9), pa14_9_eq.
  rewrite (encb_rp P14_10 pa14_9 pp14_10), (encb_app a14_10), pa14_10_eq.
  rewrite (encb_rp P14_11 pa14_10 pp14_11), (encb_app a14_11), pa14_11_eq.
  rewrite (encb_rp P14_12 pa14_11 pp14_12).
  rewrite <- ?app_assoc. reflexivity.
Qed.

(** ** Boundaries, computed from the rounds of one instance *)

Definition look14_1 : nat := 36.
Definition dep14_1 : nat := 1.
Definition p14_1 : nat := Eval vm_compute in length E14_1.
Definition N14_1 : nat := Eval vm_compute in
  let b0 := (look14_1 / p14_1 + dep14_1 + 4)%nat in
  (b0 + N.to_nat ((rb14_1 + 4 * 1024 - N.of_nat b0) mod 4)%N)%nat.
Definition look14_2 : nat := 36.
Definition dep14_2 : nat := 1.
Definition p14_2 : nat := Eval vm_compute in length E14_2.
Definition N14_2 : nat := Eval vm_compute in
  let b0 := (look14_2 / p14_2 + dep14_2 + 4)%nat in
  (b0 + N.to_nat ((rb14_2 + 4 * 1024 - N.of_nat b0) mod 4)%N)%nat.
Definition look14_3 : nat := 36.
Definition dep14_3 : nat := 1.
Definition p14_3 : nat := Eval vm_compute in length E14_3.
Definition N14_3 : nat := Eval vm_compute in
  let b0 := (look14_3 / p14_3 + dep14_3 + 4)%nat in
  (b0 + N.to_nat ((rb14_3 + 4 * 1024 - N.of_nat b0) mod 4)%N)%nat.
Definition look14_4 : nat := 36.
Definition dep14_4 : nat := 1.
Definition p14_4 : nat := Eval vm_compute in length E14_4.
Definition N14_4 : nat := Eval vm_compute in
  let b0 := (look14_4 / p14_4 + dep14_4 + 4)%nat in
  (b0 + N.to_nat ((rb14_4 + 4 * 1024 - N.of_nat b0) mod 4)%N)%nat.
Definition look14_5 : nat := 36.
Definition dep14_5 : nat := 1.
Definition p14_5 : nat := Eval vm_compute in length E14_5.
Definition N14_5 : nat := Eval vm_compute in
  let b0 := (look14_5 / p14_5 + dep14_5 + 4)%nat in
  (b0 + N.to_nat ((rb14_5 + 4 * 1024 - N.of_nat b0) mod 4)%N)%nat.
Definition look14_6 : nat := 36.
Definition dep14_6 : nat := 1.
Definition p14_6 : nat := Eval vm_compute in length E14_6.
Definition N14_6 : nat := Eval vm_compute in
  let b0 := (look14_6 / p14_6 + dep14_6 + 4)%nat in
  (b0 + N.to_nat ((rb14_6 + 4 * 1024 - N.of_nat b0) mod 4)%N)%nat.
Definition look14_7 : nat := 36.
Definition dep14_7 : nat := 1.
Definition p14_7 : nat := Eval vm_compute in length E14_7.
Definition N14_7 : nat := Eval vm_compute in
  let b0 := (look14_7 / p14_7 + dep14_7 + 4)%nat in
  (b0 + N.to_nat ((rb14_7 + 4 * 1024 - N.of_nat b0) mod 4)%N)%nat.
Definition look14_8 : nat := 36.
Definition dep14_8 : nat := 1.
Definition p14_8 : nat := Eval vm_compute in length E14_8.
Definition N14_8 : nat := Eval vm_compute in
  let b0 := (look14_8 / p14_8 + dep14_8 + 4)%nat in
  (b0 + N.to_nat ((rb14_8 + 4 * 1024 - N.of_nat b0) mod 4)%N)%nat.
Definition look14_9 : nat := 36.
Definition dep14_9 : nat := 1.
Definition p14_9 : nat := Eval vm_compute in length E14_9.
Definition N14_9 : nat := Eval vm_compute in
  let b0 := (look14_9 / p14_9 + dep14_9 + 4)%nat in
  (b0 + N.to_nat ((rb14_9 + 4 * 1024 - N.of_nat b0) mod 4)%N)%nat.
Definition look14_10 : nat := 36.
Definition dep14_10 : nat := 1.
Definition p14_10 : nat := Eval vm_compute in length E14_10.
Definition N14_10 : nat := Eval vm_compute in
  let b0 := (look14_10 / p14_10 + dep14_10 + 4)%nat in
  (b0 + N.to_nat ((rb14_10 + 4 * 1024 - N.of_nat b0) mod 4)%N)%nat.
Definition look14_11 : nat := 36.
Definition dep14_11 : nat := 1.
Definition p14_11 : nat := Eval vm_compute in length E14_11.
Definition N14_11 : nat := Eval vm_compute in
  let b0 := (look14_11 / p14_11 + dep14_11 + 4)%nat in
  (b0 + N.to_nat ((rb14_11 + 4 * 1024 - N.of_nat b0) mod 4)%N)%nat.
Definition look14_12 : nat := 36.
Definition dep14_12 : nat := 1.
Definition p14_12 : nat := Eval vm_compute in length E14_12.
Definition N14_12 : nat := Eval vm_compute in
  let b0 := (look14_12 / p14_12 + dep14_12 + 4)%nat in
  (b0 + N.to_nat ((rb14_12 + 4 * 1024 - N.of_nat b0) mod 4)%N)%nat.
Definition looke14 : nat := 36.
Definition inst14 : list bool := cells14 N14_1 N14_2 N14_3 N14_4 N14_5 N14_6 N14_7 N14_8 N14_9 N14_10 N14_11 N14_12.
Definition s14_1 : N := Eval vm_compute in N.of_nat (length Hd14).
Definition s14_2 : N := Eval vm_compute in
  (s14_1 + N.of_nat (N14_1 * p14_1 + length J14_1))%N.
Definition s14_3 : N := Eval vm_compute in
  (s14_2 + N.of_nat (N14_2 * p14_2 + length J14_2))%N.
Definition s14_4 : N := Eval vm_compute in
  (s14_3 + N.of_nat (N14_3 * p14_3 + length J14_3))%N.
Definition s14_5 : N := Eval vm_compute in
  (s14_4 + N.of_nat (N14_4 * p14_4 + length J14_4))%N.
Definition s14_6 : N := Eval vm_compute in
  (s14_5 + N.of_nat (N14_5 * p14_5 + length J14_5))%N.
Definition s14_7 : N := Eval vm_compute in
  (s14_6 + N.of_nat (N14_6 * p14_6 + length J14_6))%N.
Definition s14_8 : N := Eval vm_compute in
  (s14_7 + N.of_nat (N14_7 * p14_7 + length J14_7))%N.
Definition s14_9 : N := Eval vm_compute in
  (s14_8 + N.of_nat (N14_8 * p14_8 + length J14_8))%N.
Definition s14_10 : N := Eval vm_compute in
  (s14_9 + N.of_nat (N14_9 * p14_9 + length J14_9))%N.
Definition s14_11 : N := Eval vm_compute in
  (s14_10 + N.of_nat (N14_10 * p14_10 + length J14_10))%N.
Definition s14_12 : N := Eval vm_compute in
  (s14_11 + N.of_nat (N14_11 * p14_11 + length J14_11))%N.
Definition s14_13 : N := Eval vm_compute in
  (s14_12 + N.of_nat (N14_12 * p14_12 + length J14_12))%N.
Definition fall14 : list (N * N * N * N) * (N * N) * nat := Eval vm_compute in
  let tr := gtrace 36 (length inst14) 0 0 0 (c1101, true, inst14) in
  (gfindk (N.of_nat p14_1) (s14_1 + N.of_nat (dep14_1 * p14_1))
         (s14_1 + N.of_nat (N14_1 * p14_1) - N.of_nat look14_1) (1%N :: 2%N :: 4%N :: nil) tr ::
   gfindk (N.of_nat p14_2) (s14_2 + N.of_nat (dep14_2 * p14_2))
         (s14_2 + N.of_nat (N14_2 * p14_2) - N.of_nat look14_2) (1%N :: 2%N :: 4%N :: nil) tr ::
   gfindk (N.of_nat p14_3) (s14_3 + N.of_nat (dep14_3 * p14_3))
         (s14_3 + N.of_nat (N14_3 * p14_3) - N.of_nat look14_3) (1%N :: 2%N :: 4%N :: nil) tr ::
   gfindk (N.of_nat p14_4) (s14_4 + N.of_nat (dep14_4 * p14_4))
         (s14_4 + N.of_nat (N14_4 * p14_4) - N.of_nat look14_4) (1%N :: 2%N :: 4%N :: nil) tr ::
   gfindk (N.of_nat p14_5) (s14_5 + N.of_nat (dep14_5 * p14_5))
         (s14_5 + N.of_nat (N14_5 * p14_5) - N.of_nat look14_5) (1%N :: 2%N :: 4%N :: nil) tr ::
   gfindk (N.of_nat p14_6) (s14_6 + N.of_nat (dep14_6 * p14_6))
         (s14_6 + N.of_nat (N14_6 * p14_6) - N.of_nat look14_6) (1%N :: 2%N :: 4%N :: nil) tr ::
   gfindk (N.of_nat p14_7) (s14_7 + N.of_nat (dep14_7 * p14_7))
         (s14_7 + N.of_nat (N14_7 * p14_7) - N.of_nat look14_7) (1%N :: 2%N :: 4%N :: nil) tr ::
   gfindk (N.of_nat p14_8) (s14_8 + N.of_nat (dep14_8 * p14_8))
         (s14_8 + N.of_nat (N14_8 * p14_8) - N.of_nat look14_8) (1%N :: 2%N :: 4%N :: nil) tr ::
   gfindk (N.of_nat p14_9) (s14_9 + N.of_nat (dep14_9 * p14_9))
         (s14_9 + N.of_nat (N14_9 * p14_9) - N.of_nat look14_9) (1%N :: 2%N :: 4%N :: nil) tr ::
   gfindk (N.of_nat p14_10) (s14_10 + N.of_nat (dep14_10 * p14_10))
         (s14_10 + N.of_nat (N14_10 * p14_10) - N.of_nat look14_10) (1%N :: 2%N :: 4%N :: nil) tr ::
   gfindk (N.of_nat p14_11) (s14_11 + N.of_nat (dep14_11 * p14_11))
         (s14_11 + N.of_nat (N14_11 * p14_11) - N.of_nat look14_11) (1%N :: 2%N :: 4%N :: nil) tr ::
   gfindk (N.of_nat p14_12) (s14_12 + N.of_nat (dep14_12 * p14_12))
         (s14_12 + N.of_nat (N14_12 * p14_12) - N.of_nat look14_12) (1%N :: 2%N :: 4%N :: nil) tr ::
   nil,
   glast (s14_13 - N.of_nat (looke14 + 300)) tr (0, 0)%N, length tr).
Definition f14_1 : N * N * N * N := Eval vm_compute in
  nth 0 (fst (fst fall14)) (0, 0, 0, 1)%N.
Definition rr14_1 : nat := Eval vm_compute in N.to_nat (fst (fst (fst f14_1))).
Definition R14_1 : nat := Eval vm_compute in N.to_nat (snd (fst f14_1)).
Definition kq14_1 : nat := Eval vm_compute in N.to_nat (snd f14_1).
Definition cc14_1 : nat := Eval vm_compute in N.to_nat ((snd (fst (fst f14_1)) + N.of_nat look14_1 - s14_1) / N.of_nat p14_1).
Definition uu14_1 : nat := Eval vm_compute in N.to_nat ((snd (fst (fst f14_1)) + N.of_nat look14_1 - s14_1) mod N.of_nat p14_1).
Definition jj14_1 : nat := Eval vm_compute in (N14_1 - cc14_1 - 1) mod kq14_1.
Definition S14_1 : sst := Eval vm_compute in
  gcut look14_1 (grst rr14_1 (c1101, true, inst14)).
Definition f14_2 : N * N * N * N := Eval vm_compute in
  nth 1 (fst (fst fall14)) (0, 0, 0, 1)%N.
Definition rr14_2 : nat := Eval vm_compute in N.to_nat (fst (fst (fst f14_2))).
Definition R14_2 : nat := Eval vm_compute in N.to_nat (snd (fst f14_2)).
Definition kq14_2 : nat := Eval vm_compute in N.to_nat (snd f14_2).
Definition cc14_2 : nat := Eval vm_compute in N.to_nat ((snd (fst (fst f14_2)) + N.of_nat look14_2 - s14_2) / N.of_nat p14_2).
Definition uu14_2 : nat := Eval vm_compute in N.to_nat ((snd (fst (fst f14_2)) + N.of_nat look14_2 - s14_2) mod N.of_nat p14_2).
Definition jj14_2 : nat := Eval vm_compute in (N14_2 - cc14_2 - 1) mod kq14_2.
Definition S14_2 : sst := Eval vm_compute in
  gcut look14_2 (grst rr14_2 (c1101, true, inst14)).
Definition f14_3 : N * N * N * N := Eval vm_compute in
  nth 2 (fst (fst fall14)) (0, 0, 0, 1)%N.
Definition rr14_3 : nat := Eval vm_compute in N.to_nat (fst (fst (fst f14_3))).
Definition R14_3 : nat := Eval vm_compute in N.to_nat (snd (fst f14_3)).
Definition kq14_3 : nat := Eval vm_compute in N.to_nat (snd f14_3).
Definition cc14_3 : nat := Eval vm_compute in N.to_nat ((snd (fst (fst f14_3)) + N.of_nat look14_3 - s14_3) / N.of_nat p14_3).
Definition uu14_3 : nat := Eval vm_compute in N.to_nat ((snd (fst (fst f14_3)) + N.of_nat look14_3 - s14_3) mod N.of_nat p14_3).
Definition jj14_3 : nat := Eval vm_compute in (N14_3 - cc14_3 - 1) mod kq14_3.
Definition S14_3 : sst := Eval vm_compute in
  gcut look14_3 (grst rr14_3 (c1101, true, inst14)).
Definition f14_4 : N * N * N * N := Eval vm_compute in
  nth 3 (fst (fst fall14)) (0, 0, 0, 1)%N.
Definition rr14_4 : nat := Eval vm_compute in N.to_nat (fst (fst (fst f14_4))).
Definition R14_4 : nat := Eval vm_compute in N.to_nat (snd (fst f14_4)).
Definition kq14_4 : nat := Eval vm_compute in N.to_nat (snd f14_4).
Definition cc14_4 : nat := Eval vm_compute in N.to_nat ((snd (fst (fst f14_4)) + N.of_nat look14_4 - s14_4) / N.of_nat p14_4).
Definition uu14_4 : nat := Eval vm_compute in N.to_nat ((snd (fst (fst f14_4)) + N.of_nat look14_4 - s14_4) mod N.of_nat p14_4).
Definition jj14_4 : nat := Eval vm_compute in (N14_4 - cc14_4 - 1) mod kq14_4.
Definition S14_4 : sst := Eval vm_compute in
  gcut look14_4 (grst rr14_4 (c1101, true, inst14)).
Definition f14_5 : N * N * N * N := Eval vm_compute in
  nth 4 (fst (fst fall14)) (0, 0, 0, 1)%N.
Definition rr14_5 : nat := Eval vm_compute in N.to_nat (fst (fst (fst f14_5))).
Definition R14_5 : nat := Eval vm_compute in N.to_nat (snd (fst f14_5)).
Definition kq14_5 : nat := Eval vm_compute in N.to_nat (snd f14_5).
Definition cc14_5 : nat := Eval vm_compute in N.to_nat ((snd (fst (fst f14_5)) + N.of_nat look14_5 - s14_5) / N.of_nat p14_5).
Definition uu14_5 : nat := Eval vm_compute in N.to_nat ((snd (fst (fst f14_5)) + N.of_nat look14_5 - s14_5) mod N.of_nat p14_5).
Definition jj14_5 : nat := Eval vm_compute in (N14_5 - cc14_5 - 1) mod kq14_5.
Definition S14_5 : sst := Eval vm_compute in
  gcut look14_5 (grst rr14_5 (c1101, true, inst14)).
Definition f14_6 : N * N * N * N := Eval vm_compute in
  nth 5 (fst (fst fall14)) (0, 0, 0, 1)%N.
Definition rr14_6 : nat := Eval vm_compute in N.to_nat (fst (fst (fst f14_6))).
Definition R14_6 : nat := Eval vm_compute in N.to_nat (snd (fst f14_6)).
Definition kq14_6 : nat := Eval vm_compute in N.to_nat (snd f14_6).
Definition cc14_6 : nat := Eval vm_compute in N.to_nat ((snd (fst (fst f14_6)) + N.of_nat look14_6 - s14_6) / N.of_nat p14_6).
Definition uu14_6 : nat := Eval vm_compute in N.to_nat ((snd (fst (fst f14_6)) + N.of_nat look14_6 - s14_6) mod N.of_nat p14_6).
Definition jj14_6 : nat := Eval vm_compute in (N14_6 - cc14_6 - 1) mod kq14_6.
Definition S14_6 : sst := Eval vm_compute in
  gcut look14_6 (grst rr14_6 (c1101, true, inst14)).
Definition f14_7 : N * N * N * N := Eval vm_compute in
  nth 6 (fst (fst fall14)) (0, 0, 0, 1)%N.
Definition rr14_7 : nat := Eval vm_compute in N.to_nat (fst (fst (fst f14_7))).
Definition R14_7 : nat := Eval vm_compute in N.to_nat (snd (fst f14_7)).
Definition kq14_7 : nat := Eval vm_compute in N.to_nat (snd f14_7).
Definition cc14_7 : nat := Eval vm_compute in N.to_nat ((snd (fst (fst f14_7)) + N.of_nat look14_7 - s14_7) / N.of_nat p14_7).
Definition uu14_7 : nat := Eval vm_compute in N.to_nat ((snd (fst (fst f14_7)) + N.of_nat look14_7 - s14_7) mod N.of_nat p14_7).
Definition jj14_7 : nat := Eval vm_compute in (N14_7 - cc14_7 - 1) mod kq14_7.
Definition S14_7 : sst := Eval vm_compute in
  gcut look14_7 (grst rr14_7 (c1101, true, inst14)).
Definition f14_8 : N * N * N * N := Eval vm_compute in
  nth 7 (fst (fst fall14)) (0, 0, 0, 1)%N.
Definition rr14_8 : nat := Eval vm_compute in N.to_nat (fst (fst (fst f14_8))).
Definition R14_8 : nat := Eval vm_compute in N.to_nat (snd (fst f14_8)).
Definition kq14_8 : nat := Eval vm_compute in N.to_nat (snd f14_8).
Definition cc14_8 : nat := Eval vm_compute in N.to_nat ((snd (fst (fst f14_8)) + N.of_nat look14_8 - s14_8) / N.of_nat p14_8).
Definition uu14_8 : nat := Eval vm_compute in N.to_nat ((snd (fst (fst f14_8)) + N.of_nat look14_8 - s14_8) mod N.of_nat p14_8).
Definition jj14_8 : nat := Eval vm_compute in (N14_8 - cc14_8 - 1) mod kq14_8.
Definition S14_8 : sst := Eval vm_compute in
  gcut look14_8 (grst rr14_8 (c1101, true, inst14)).
Definition f14_9 : N * N * N * N := Eval vm_compute in
  nth 8 (fst (fst fall14)) (0, 0, 0, 1)%N.
Definition rr14_9 : nat := Eval vm_compute in N.to_nat (fst (fst (fst f14_9))).
Definition R14_9 : nat := Eval vm_compute in N.to_nat (snd (fst f14_9)).
Definition kq14_9 : nat := Eval vm_compute in N.to_nat (snd f14_9).
Definition cc14_9 : nat := Eval vm_compute in N.to_nat ((snd (fst (fst f14_9)) + N.of_nat look14_9 - s14_9) / N.of_nat p14_9).
Definition uu14_9 : nat := Eval vm_compute in N.to_nat ((snd (fst (fst f14_9)) + N.of_nat look14_9 - s14_9) mod N.of_nat p14_9).
Definition jj14_9 : nat := Eval vm_compute in (N14_9 - cc14_9 - 1) mod kq14_9.
Definition S14_9 : sst := Eval vm_compute in
  gcut look14_9 (grst rr14_9 (c1101, true, inst14)).
Definition f14_10 : N * N * N * N := Eval vm_compute in
  nth 9 (fst (fst fall14)) (0, 0, 0, 1)%N.
Definition rr14_10 : nat := Eval vm_compute in N.to_nat (fst (fst (fst f14_10))).
Definition R14_10 : nat := Eval vm_compute in N.to_nat (snd (fst f14_10)).
Definition kq14_10 : nat := Eval vm_compute in N.to_nat (snd f14_10).
Definition cc14_10 : nat := Eval vm_compute in N.to_nat ((snd (fst (fst f14_10)) + N.of_nat look14_10 - s14_10) / N.of_nat p14_10).
Definition uu14_10 : nat := Eval vm_compute in N.to_nat ((snd (fst (fst f14_10)) + N.of_nat look14_10 - s14_10) mod N.of_nat p14_10).
Definition jj14_10 : nat := Eval vm_compute in (N14_10 - cc14_10 - 1) mod kq14_10.
Definition S14_10 : sst := Eval vm_compute in
  gcut look14_10 (grst rr14_10 (c1101, true, inst14)).
Definition f14_11 : N * N * N * N := Eval vm_compute in
  nth 10 (fst (fst fall14)) (0, 0, 0, 1)%N.
Definition rr14_11 : nat := Eval vm_compute in N.to_nat (fst (fst (fst f14_11))).
Definition R14_11 : nat := Eval vm_compute in N.to_nat (snd (fst f14_11)).
Definition kq14_11 : nat := Eval vm_compute in N.to_nat (snd f14_11).
Definition cc14_11 : nat := Eval vm_compute in N.to_nat ((snd (fst (fst f14_11)) + N.of_nat look14_11 - s14_11) / N.of_nat p14_11).
Definition uu14_11 : nat := Eval vm_compute in N.to_nat ((snd (fst (fst f14_11)) + N.of_nat look14_11 - s14_11) mod N.of_nat p14_11).
Definition jj14_11 : nat := Eval vm_compute in (N14_11 - cc14_11 - 1) mod kq14_11.
Definition S14_11 : sst := Eval vm_compute in
  gcut look14_11 (grst rr14_11 (c1101, true, inst14)).
Definition f14_12 : N * N * N * N := Eval vm_compute in
  nth 11 (fst (fst fall14)) (0, 0, 0, 1)%N.
Definition rr14_12 : nat := Eval vm_compute in N.to_nat (fst (fst (fst f14_12))).
Definition R14_12 : nat := Eval vm_compute in N.to_nat (snd (fst f14_12)).
Definition kq14_12 : nat := Eval vm_compute in N.to_nat (snd f14_12).
Definition cc14_12 : nat := Eval vm_compute in N.to_nat ((snd (fst (fst f14_12)) + N.of_nat look14_12 - s14_12) / N.of_nat p14_12).
Definition uu14_12 : nat := Eval vm_compute in N.to_nat ((snd (fst (fst f14_12)) + N.of_nat look14_12 - s14_12) mod N.of_nat p14_12).
Definition jj14_12 : nat := Eval vm_compute in (N14_12 - cc14_12 - 1) mod kq14_12.
Definition S14_12 : sst := Eval vm_compute in
  gcut look14_12 (grst rr14_12 (c1101, true, inst14)).
Definition fe14 : N * N := Eval vm_compute in snd (fst fall14).
Definition rre14 : nat := Eval vm_compute in N.to_nat (fst fe14).
Definition ue14 : nat := Eval vm_compute in
  N.to_nat (snd fe14 + N.of_nat looke14 - (s14_12 + N.of_nat (N14_12 * p14_12))).
Definition Se14 : sst := Eval vm_compute in gcut looke14 (grst rre14 (c1101, true, inst14)).
Definition Rj14_0 : nat := rr14_1.
Definition Rj14_1 : nat := Eval vm_compute in
  rr14_2 - rr14_1 - R14_1 * ((N14_1 - cc14_1 - 1 - jj14_1) / kq14_1).
Definition Rj14_2 : nat := Eval vm_compute in
  rr14_3 - rr14_2 - R14_2 * ((N14_2 - cc14_2 - 1 - jj14_2) / kq14_2).
Definition Rj14_3 : nat := Eval vm_compute in
  rr14_4 - rr14_3 - R14_3 * ((N14_3 - cc14_3 - 1 - jj14_3) / kq14_3).
Definition Rj14_4 : nat := Eval vm_compute in
  rr14_5 - rr14_4 - R14_4 * ((N14_4 - cc14_4 - 1 - jj14_4) / kq14_4).
Definition Rj14_5 : nat := Eval vm_compute in
  rr14_6 - rr14_5 - R14_5 * ((N14_5 - cc14_5 - 1 - jj14_5) / kq14_5).
Definition Rj14_6 : nat := Eval vm_compute in
  rr14_7 - rr14_6 - R14_6 * ((N14_6 - cc14_6 - 1 - jj14_6) / kq14_6).
Definition Rj14_7 : nat := Eval vm_compute in
  rr14_8 - rr14_7 - R14_7 * ((N14_7 - cc14_7 - 1 - jj14_7) / kq14_7).
Definition Rj14_8 : nat := Eval vm_compute in
  rr14_9 - rr14_8 - R14_8 * ((N14_8 - cc14_8 - 1 - jj14_8) / kq14_8).
Definition Rj14_9 : nat := Eval vm_compute in
  rr14_10 - rr14_9 - R14_9 * ((N14_9 - cc14_9 - 1 - jj14_9) / kq14_9).
Definition Rj14_10 : nat := Eval vm_compute in
  rr14_11 - rr14_10 - R14_10 * ((N14_10 - cc14_10 - 1 - jj14_10) / kq14_10).
Definition Rj14_11 : nat := Eval vm_compute in
  rr14_12 - rr14_11 - R14_11 * ((N14_11 - cc14_11 - 1 - jj14_11) / kq14_11).
Definition Rj14_12 : nat := Eval vm_compute in
  rre14 - rr14_12 - R14_12 * ((N14_12 - cc14_12 - 1 - jj14_12) / kq14_12).

(** ** The cuts *)

Definition u14_1 : list bool := firstn uu14_1 E14_1.
Definition v14_1 : list bool := skipn uu14_1 E14_1.
Definition u14_2 : list bool := firstn uu14_2 E14_2.
Definition v14_2 : list bool := skipn uu14_2 E14_2.
Definition u14_3 : list bool := firstn uu14_3 E14_3.
Definition v14_3 : list bool := skipn uu14_3 E14_3.
Definition u14_4 : list bool := firstn uu14_4 E14_4.
Definition v14_4 : list bool := skipn uu14_4 E14_4.
Definition u14_5 : list bool := firstn uu14_5 E14_5.
Definition v14_5 : list bool := skipn uu14_5 E14_5.
Definition u14_6 : list bool := firstn uu14_6 E14_6.
Definition v14_6 : list bool := skipn uu14_6 E14_6.
Definition u14_7 : list bool := firstn uu14_7 E14_7.
Definition v14_7 : list bool := skipn uu14_7 E14_7.
Definition u14_8 : list bool := firstn uu14_8 E14_8.
Definition v14_8 : list bool := skipn uu14_8 E14_8.
Definition u14_9 : list bool := firstn uu14_9 E14_9.
Definition v14_9 : list bool := skipn uu14_9 E14_9.
Definition u14_10 : list bool := firstn uu14_10 E14_10.
Definition v14_10 : list bool := skipn uu14_10 E14_10.
Definition u14_11 : list bool := firstn uu14_11 E14_11.
Definition v14_11 : list bool := skipn uu14_11 E14_11.
Definition u14_12 : list bool := firstn uu14_12 E14_12.
Definition v14_12 : list bool := skipn uu14_12 E14_12.
Definition F14_0 : list bool := Hd14 ++ rp E14_1 cc14_1 ++ u14_1.
Definition C14_1 : list bool := v14_1 ++ u14_1.
Definition K14_1 : list bool := rp C14_1 kq14_1.
Lemma tl14_1 : rp E14_1 (jj14_1 + 1) = u14_1 ++ rp C14_1 jj14_1 ++ v14_1.
Proof. vm_compute. reflexivity. Qed.
Definition F14_1 : list bool :=
  (rp C14_1 jj14_1 ++ v14_1) ++ J14_1 ++ rp E14_2 cc14_2 ++ u14_2.
Definition C14_2 : list bool := v14_2 ++ u14_2.
Definition K14_2 : list bool := rp C14_2 kq14_2.
Lemma tl14_2 : rp E14_2 (jj14_2 + 1) = u14_2 ++ rp C14_2 jj14_2 ++ v14_2.
Proof. vm_compute. reflexivity. Qed.
Definition F14_2 : list bool :=
  (rp C14_2 jj14_2 ++ v14_2) ++ J14_2 ++ rp E14_3 cc14_3 ++ u14_3.
Definition C14_3 : list bool := v14_3 ++ u14_3.
Definition K14_3 : list bool := rp C14_3 kq14_3.
Lemma tl14_3 : rp E14_3 (jj14_3 + 1) = u14_3 ++ rp C14_3 jj14_3 ++ v14_3.
Proof. vm_compute. reflexivity. Qed.
Definition F14_3 : list bool :=
  (rp C14_3 jj14_3 ++ v14_3) ++ J14_3 ++ rp E14_4 cc14_4 ++ u14_4.
Definition C14_4 : list bool := v14_4 ++ u14_4.
Definition K14_4 : list bool := rp C14_4 kq14_4.
Lemma tl14_4 : rp E14_4 (jj14_4 + 1) = u14_4 ++ rp C14_4 jj14_4 ++ v14_4.
Proof. vm_compute. reflexivity. Qed.
Definition F14_4 : list bool :=
  (rp C14_4 jj14_4 ++ v14_4) ++ J14_4 ++ rp E14_5 cc14_5 ++ u14_5.
Definition C14_5 : list bool := v14_5 ++ u14_5.
Definition K14_5 : list bool := rp C14_5 kq14_5.
Lemma tl14_5 : rp E14_5 (jj14_5 + 1) = u14_5 ++ rp C14_5 jj14_5 ++ v14_5.
Proof. vm_compute. reflexivity. Qed.
Definition F14_5 : list bool :=
  (rp C14_5 jj14_5 ++ v14_5) ++ J14_5 ++ rp E14_6 cc14_6 ++ u14_6.
Definition C14_6 : list bool := v14_6 ++ u14_6.
Definition K14_6 : list bool := rp C14_6 kq14_6.
Lemma tl14_6 : rp E14_6 (jj14_6 + 1) = u14_6 ++ rp C14_6 jj14_6 ++ v14_6.
Proof. vm_compute. reflexivity. Qed.
Definition F14_6 : list bool :=
  (rp C14_6 jj14_6 ++ v14_6) ++ J14_6 ++ rp E14_7 cc14_7 ++ u14_7.
Definition C14_7 : list bool := v14_7 ++ u14_7.
Definition K14_7 : list bool := rp C14_7 kq14_7.
Lemma tl14_7 : rp E14_7 (jj14_7 + 1) = u14_7 ++ rp C14_7 jj14_7 ++ v14_7.
Proof. vm_compute. reflexivity. Qed.
Definition F14_7 : list bool :=
  (rp C14_7 jj14_7 ++ v14_7) ++ J14_7 ++ rp E14_8 cc14_8 ++ u14_8.
Definition C14_8 : list bool := v14_8 ++ u14_8.
Definition K14_8 : list bool := rp C14_8 kq14_8.
Lemma tl14_8 : rp E14_8 (jj14_8 + 1) = u14_8 ++ rp C14_8 jj14_8 ++ v14_8.
Proof. vm_compute. reflexivity. Qed.
Definition F14_8 : list bool :=
  (rp C14_8 jj14_8 ++ v14_8) ++ J14_8 ++ rp E14_9 cc14_9 ++ u14_9.
Definition C14_9 : list bool := v14_9 ++ u14_9.
Definition K14_9 : list bool := rp C14_9 kq14_9.
Lemma tl14_9 : rp E14_9 (jj14_9 + 1) = u14_9 ++ rp C14_9 jj14_9 ++ v14_9.
Proof. vm_compute. reflexivity. Qed.
Definition F14_9 : list bool :=
  (rp C14_9 jj14_9 ++ v14_9) ++ J14_9 ++ rp E14_10 cc14_10 ++ u14_10.
Definition C14_10 : list bool := v14_10 ++ u14_10.
Definition K14_10 : list bool := rp C14_10 kq14_10.
Lemma tl14_10 : rp E14_10 (jj14_10 + 1) = u14_10 ++ rp C14_10 jj14_10 ++ v14_10.
Proof. vm_compute. reflexivity. Qed.
Definition F14_10 : list bool :=
  (rp C14_10 jj14_10 ++ v14_10) ++ J14_10 ++ rp E14_11 cc14_11 ++ u14_11.
Definition C14_11 : list bool := v14_11 ++ u14_11.
Definition K14_11 : list bool := rp C14_11 kq14_11.
Lemma tl14_11 : rp E14_11 (jj14_11 + 1) = u14_11 ++ rp C14_11 jj14_11 ++ v14_11.
Proof. vm_compute. reflexivity. Qed.
Definition F14_11 : list bool :=
  (rp C14_11 jj14_11 ++ v14_11) ++ J14_11 ++ rp E14_12 cc14_12 ++ u14_12.
Definition C14_12 : list bool := v14_12 ++ u14_12.
Definition K14_12 : list bool := rp C14_12 kq14_12.
Lemma tl14_12 : rp E14_12 (jj14_12 + 1) = u14_12 ++ rp C14_12 jj14_12 ++ v14_12.
Proof. vm_compute. reflexivity. Qed.
Definition F14_12 : list bool := (rp C14_12 jj14_12 ++ v14_12) ++ firstn ue14 J14_12.
Definition Fw14 : list bool := skipn ue14 J14_12 ++ w14.

Lemma cells14_cut : forall n1 n2 n3 n4 n5 n6 n7 n8 n9 n10 n11 n12,
  cells14 (cc14_1 + (n1 * kq14_1 + jj14_1) + 1) (cc14_2 + (n2 * kq14_2 + jj14_2) + 1) (cc14_3 + (n3 *
    kq14_3 + jj14_3) + 1) (cc14_4 + (n4 * kq14_4 + jj14_4) + 1) (cc14_5 + (n5 * kq14_5 + jj14_5) +
    1) (cc14_6 + (n6 * kq14_6 + jj14_6) + 1) (cc14_7 + (n7 * kq14_7 + jj14_7) + 1) (cc14_8 + (n8 *
    kq14_8 + jj14_8) + 1) (cc14_9 + (n9 * kq14_9 + jj14_9) + 1) (cc14_10 + (n10 * kq14_10 + jj14_10)
    + 1) (cc14_11 + (n11 * kq14_11 + jj14_11) + 1) (cc14_12 + (n12 * kq14_12 + jj14_12) + 1) =
    (F14_0 ++ rp K14_1 n1 ++ F14_1 ++ rp K14_2 n2 ++ F14_2 ++ rp K14_3 n3 ++ F14_3 ++ rp K14_4 n4 ++
    F14_4 ++ rp K14_5 n5 ++ F14_5 ++ rp K14_6 n6 ++ F14_6 ++ rp K14_7 n7 ++ F14_7 ++ rp K14_8 n8 ++
    F14_8 ++ rp K14_9 n9 ++ F14_9 ++ rp K14_10 n10 ++ F14_10 ++ rp K14_11 n11 ++ F14_11 ++ rp K14_12
    n12 ++ F14_12 ++ []) ++ Fw14.
Proof.
  intros n1 n2 n3 n4 n5 n6 n7 n8 n9 n10 n11 n12. rewrite cells14_eq.
  replace (cc14_1 + (n1 * kq14_1 + jj14_1) + 1) with (cc14_1 + n1 * kq14_1 + (jj14_1 + 1)) by lia.
  rewrite (rp_recut E14_1 u14_1 v14_1 (n1 * kq14_1) cc14_1 (jj14_1 + 1) (rp C14_1 jj14_1 ++ v14_1)
             (eq_sym (firstn_skipn uu14_1 E14_1)) tl14_1).
  rewrite (rp_mul (v14_1 ++ u14_1) kq14_1 n1).
  replace (cc14_2 + (n2 * kq14_2 + jj14_2) + 1) with (cc14_2 + n2 * kq14_2 + (jj14_2 + 1)) by lia.
  rewrite (rp_recut E14_2 u14_2 v14_2 (n2 * kq14_2) cc14_2 (jj14_2 + 1) (rp C14_2 jj14_2 ++ v14_2)
             (eq_sym (firstn_skipn uu14_2 E14_2)) tl14_2).
  rewrite (rp_mul (v14_2 ++ u14_2) kq14_2 n2).
  replace (cc14_3 + (n3 * kq14_3 + jj14_3) + 1) with (cc14_3 + n3 * kq14_3 + (jj14_3 + 1)) by lia.
  rewrite (rp_recut E14_3 u14_3 v14_3 (n3 * kq14_3) cc14_3 (jj14_3 + 1) (rp C14_3 jj14_3 ++ v14_3)
             (eq_sym (firstn_skipn uu14_3 E14_3)) tl14_3).
  rewrite (rp_mul (v14_3 ++ u14_3) kq14_3 n3).
  replace (cc14_4 + (n4 * kq14_4 + jj14_4) + 1) with (cc14_4 + n4 * kq14_4 + (jj14_4 + 1)) by lia.
  rewrite (rp_recut E14_4 u14_4 v14_4 (n4 * kq14_4) cc14_4 (jj14_4 + 1) (rp C14_4 jj14_4 ++ v14_4)
             (eq_sym (firstn_skipn uu14_4 E14_4)) tl14_4).
  rewrite (rp_mul (v14_4 ++ u14_4) kq14_4 n4).
  replace (cc14_5 + (n5 * kq14_5 + jj14_5) + 1) with (cc14_5 + n5 * kq14_5 + (jj14_5 + 1)) by lia.
  rewrite (rp_recut E14_5 u14_5 v14_5 (n5 * kq14_5) cc14_5 (jj14_5 + 1) (rp C14_5 jj14_5 ++ v14_5)
             (eq_sym (firstn_skipn uu14_5 E14_5)) tl14_5).
  rewrite (rp_mul (v14_5 ++ u14_5) kq14_5 n5).
  replace (cc14_6 + (n6 * kq14_6 + jj14_6) + 1) with (cc14_6 + n6 * kq14_6 + (jj14_6 + 1)) by lia.
  rewrite (rp_recut E14_6 u14_6 v14_6 (n6 * kq14_6) cc14_6 (jj14_6 + 1) (rp C14_6 jj14_6 ++ v14_6)
             (eq_sym (firstn_skipn uu14_6 E14_6)) tl14_6).
  rewrite (rp_mul (v14_6 ++ u14_6) kq14_6 n6).
  replace (cc14_7 + (n7 * kq14_7 + jj14_7) + 1) with (cc14_7 + n7 * kq14_7 + (jj14_7 + 1)) by lia.
  rewrite (rp_recut E14_7 u14_7 v14_7 (n7 * kq14_7) cc14_7 (jj14_7 + 1) (rp C14_7 jj14_7 ++ v14_7)
             (eq_sym (firstn_skipn uu14_7 E14_7)) tl14_7).
  rewrite (rp_mul (v14_7 ++ u14_7) kq14_7 n7).
  replace (cc14_8 + (n8 * kq14_8 + jj14_8) + 1) with (cc14_8 + n8 * kq14_8 + (jj14_8 + 1)) by lia.
  rewrite (rp_recut E14_8 u14_8 v14_8 (n8 * kq14_8) cc14_8 (jj14_8 + 1) (rp C14_8 jj14_8 ++ v14_8)
             (eq_sym (firstn_skipn uu14_8 E14_8)) tl14_8).
  rewrite (rp_mul (v14_8 ++ u14_8) kq14_8 n8).
  replace (cc14_9 + (n9 * kq14_9 + jj14_9) + 1) with (cc14_9 + n9 * kq14_9 + (jj14_9 + 1)) by lia.
  rewrite (rp_recut E14_9 u14_9 v14_9 (n9 * kq14_9) cc14_9 (jj14_9 + 1) (rp C14_9 jj14_9 ++ v14_9)
             (eq_sym (firstn_skipn uu14_9 E14_9)) tl14_9).
  rewrite (rp_mul (v14_9 ++ u14_9) kq14_9 n9).
  replace (cc14_10 + (n10 * kq14_10 + jj14_10) + 1) with (cc14_10 + n10 * kq14_10 + (jj14_10 + 1)) by lia.
  rewrite (rp_recut E14_10 u14_10 v14_10 (n10 * kq14_10) cc14_10 (jj14_10 + 1) (rp C14_10 jj14_10 ++ v14_10)
             (eq_sym (firstn_skipn uu14_10 E14_10)) tl14_10).
  rewrite (rp_mul (v14_10 ++ u14_10) kq14_10 n10).
  replace (cc14_11 + (n11 * kq14_11 + jj14_11) + 1) with (cc14_11 + n11 * kq14_11 + (jj14_11 + 1)) by lia.
  rewrite (rp_recut E14_11 u14_11 v14_11 (n11 * kq14_11) cc14_11 (jj14_11 + 1) (rp C14_11 jj14_11 ++ v14_11)
             (eq_sym (firstn_skipn uu14_11 E14_11)) tl14_11).
  rewrite (rp_mul (v14_11 ++ u14_11) kq14_11 n11).
  replace (cc14_12 + (n12 * kq14_12 + jj14_12) + 1) with (cc14_12 + n12 * kq14_12 + (jj14_12 + 1)) by lia.
  rewrite (rp_recut E14_12 u14_12 v14_12 (n12 * kq14_12) cc14_12 (jj14_12 + 1) (rp C14_12 jj14_12 ++ v14_12)
             (eq_sym (firstn_skipn uu14_12 E14_12)) tl14_12).
  rewrite (rp_mul (v14_12 ++ u14_12) kq14_12 n12).
  rewrite <- (firstn_skipn ue14 J14_12) at 1.
  unfold F14_0, K14_1, F14_1, C14_1, K14_2, F14_2, C14_2, K14_3, F14_3, C14_3, K14_4, F14_4, C14_4, K14_5, F14_5, C14_5, K14_6, F14_6, C14_6, K14_7, F14_7, C14_7, K14_8, F14_8, C14_8, K14_9, F14_9, C14_9, K14_10, F14_10, C14_10, K14_11, F14_11, C14_11, K14_12, F14_12, C14_12, Fw14.
  rewrite ?app_nil_r, <- ?app_assoc. reflexivity.
Qed.

(** ** Runs and cycles, round by round *)

Definition st140 : sst := (c1101, true, []).
Definition lF14_0 : list (Z * nat) := Eval vm_compute in grl Rj14_0 st140 F14_0.
Lemma RF14_0 : Run st140 F14_0 S14_1 (pSh lF14_0) (pV lF14_0).
Proof. apply (crun_run Rj14_0 4). vm_compute. reflexivity. Qed.
Definition lC14_1 : list (Z * nat) := Eval vm_compute in grl R14_1 S14_1 K14_1.
Lemma RC14_1 : Run S14_1 K14_1 S14_1 (pSh lC14_1) (pV lC14_1).
Proof. apply (crun_run R14_1 4). vm_compute. reflexivity. Qed.
Definition lF14_1 : list (Z * nat) := Eval vm_compute in grl Rj14_1 S14_1 F14_1.
Lemma RF14_1 : Run S14_1 F14_1 S14_2 (pSh lF14_1) (pV lF14_1).
Proof. apply (crun_run Rj14_1 4). vm_compute. reflexivity. Qed.
Definition lC14_2 : list (Z * nat) := Eval vm_compute in grl R14_2 S14_2 K14_2.
Lemma RC14_2 : Run S14_2 K14_2 S14_2 (pSh lC14_2) (pV lC14_2).
Proof. apply (crun_run R14_2 4). vm_compute. reflexivity. Qed.
Definition lF14_2 : list (Z * nat) := Eval vm_compute in grl Rj14_2 S14_2 F14_2.
Lemma RF14_2 : Run S14_2 F14_2 S14_3 (pSh lF14_2) (pV lF14_2).
Proof. apply (crun_run Rj14_2 4). vm_compute. reflexivity. Qed.
Definition lC14_3 : list (Z * nat) := Eval vm_compute in grl R14_3 S14_3 K14_3.
Lemma RC14_3 : Run S14_3 K14_3 S14_3 (pSh lC14_3) (pV lC14_3).
Proof. apply (crun_run R14_3 4). vm_compute. reflexivity. Qed.
Definition lF14_3 : list (Z * nat) := Eval vm_compute in grl Rj14_3 S14_3 F14_3.
Lemma RF14_3 : Run S14_3 F14_3 S14_4 (pSh lF14_3) (pV lF14_3).
Proof. apply (crun_run Rj14_3 4). vm_compute. reflexivity. Qed.
Definition lC14_4 : list (Z * nat) := Eval vm_compute in grl R14_4 S14_4 K14_4.
Lemma RC14_4 : Run S14_4 K14_4 S14_4 (pSh lC14_4) (pV lC14_4).
Proof. apply (crun_run R14_4 4). vm_compute. reflexivity. Qed.
Definition lF14_4 : list (Z * nat) := Eval vm_compute in grl Rj14_4 S14_4 F14_4.
Lemma RF14_4 : Run S14_4 F14_4 S14_5 (pSh lF14_4) (pV lF14_4).
Proof. apply (crun_run Rj14_4 4). vm_compute. reflexivity. Qed.
Definition lC14_5 : list (Z * nat) := Eval vm_compute in grl R14_5 S14_5 K14_5.
Lemma RC14_5 : Run S14_5 K14_5 S14_5 (pSh lC14_5) (pV lC14_5).
Proof. apply (crun_run R14_5 4). vm_compute. reflexivity. Qed.
Definition lF14_5 : list (Z * nat) := Eval vm_compute in grl Rj14_5 S14_5 F14_5.
Lemma RF14_5 : Run S14_5 F14_5 S14_6 (pSh lF14_5) (pV lF14_5).
Proof. apply (crun_run Rj14_5 4). vm_compute. reflexivity. Qed.
Definition lC14_6 : list (Z * nat) := Eval vm_compute in grl R14_6 S14_6 K14_6.
Lemma RC14_6 : Run S14_6 K14_6 S14_6 (pSh lC14_6) (pV lC14_6).
Proof. apply (crun_run R14_6 4). vm_compute. reflexivity. Qed.
Definition lF14_6 : list (Z * nat) := Eval vm_compute in grl Rj14_6 S14_6 F14_6.
Lemma RF14_6 : Run S14_6 F14_6 S14_7 (pSh lF14_6) (pV lF14_6).
Proof. apply (crun_run Rj14_6 4). vm_compute. reflexivity. Qed.
Definition lC14_7 : list (Z * nat) := Eval vm_compute in grl R14_7 S14_7 K14_7.
Lemma RC14_7 : Run S14_7 K14_7 S14_7 (pSh lC14_7) (pV lC14_7).
Proof. apply (crun_run R14_7 4). vm_compute. reflexivity. Qed.
Definition lF14_7 : list (Z * nat) := Eval vm_compute in grl Rj14_7 S14_7 F14_7.
Lemma RF14_7 : Run S14_7 F14_7 S14_8 (pSh lF14_7) (pV lF14_7).
Proof. apply (crun_run Rj14_7 4). vm_compute. reflexivity. Qed.
Definition lC14_8 : list (Z * nat) := Eval vm_compute in grl R14_8 S14_8 K14_8.
Lemma RC14_8 : Run S14_8 K14_8 S14_8 (pSh lC14_8) (pV lC14_8).
Proof. apply (crun_run R14_8 4). vm_compute. reflexivity. Qed.
Definition lF14_8 : list (Z * nat) := Eval vm_compute in grl Rj14_8 S14_8 F14_8.
Lemma RF14_8 : Run S14_8 F14_8 S14_9 (pSh lF14_8) (pV lF14_8).
Proof. apply (crun_run Rj14_8 4). vm_compute. reflexivity. Qed.
Definition lC14_9 : list (Z * nat) := Eval vm_compute in grl R14_9 S14_9 K14_9.
Lemma RC14_9 : Run S14_9 K14_9 S14_9 (pSh lC14_9) (pV lC14_9).
Proof. apply (crun_run R14_9 4). vm_compute. reflexivity. Qed.
Definition lF14_9 : list (Z * nat) := Eval vm_compute in grl Rj14_9 S14_9 F14_9.
Lemma RF14_9 : Run S14_9 F14_9 S14_10 (pSh lF14_9) (pV lF14_9).
Proof. apply (crun_run Rj14_9 4). vm_compute. reflexivity. Qed.
Definition lC14_10 : list (Z * nat) := Eval vm_compute in grl R14_10 S14_10 K14_10.
Lemma RC14_10 : Run S14_10 K14_10 S14_10 (pSh lC14_10) (pV lC14_10).
Proof. apply (crun_run R14_10 4). vm_compute. reflexivity. Qed.
Definition lF14_10 : list (Z * nat) := Eval vm_compute in grl Rj14_10 S14_10 F14_10.
Lemma RF14_10 : Run S14_10 F14_10 S14_11 (pSh lF14_10) (pV lF14_10).
Proof. apply (crun_run Rj14_10 4). vm_compute. reflexivity. Qed.
Definition lC14_11 : list (Z * nat) := Eval vm_compute in grl R14_11 S14_11 K14_11.
Lemma RC14_11 : Run S14_11 K14_11 S14_11 (pSh lC14_11) (pV lC14_11).
Proof. apply (crun_run R14_11 4). vm_compute. reflexivity. Qed.
Definition lF14_11 : list (Z * nat) := Eval vm_compute in grl Rj14_11 S14_11 F14_11.
Lemma RF14_11 : Run S14_11 F14_11 S14_12 (pSh lF14_11) (pV lF14_11).
Proof. apply (crun_run Rj14_11 4). vm_compute. reflexivity. Qed.
Definition lC14_12 : list (Z * nat) := Eval vm_compute in grl R14_12 S14_12 K14_12.
Lemma RC14_12 : Run S14_12 K14_12 S14_12 (pSh lC14_12) (pV lC14_12).
Proof. apply (crun_run R14_12 4). vm_compute. reflexivity. Qed.
Definition lF14_12 : list (Z * nat) := Eval vm_compute in grl Rj14_12 S14_12 F14_12.
Lemma RF14_12 : Run S14_12 F14_12 Se14 (pSh lF14_12) (pV lF14_12).
Proof. apply (crun_run Rj14_12 4). vm_compute. reflexivity. Qed.

Definition segs14 (n1 n2 n3 n4 n5 n6 n7 n8 n9 n10 n11 n12 : nat) : list seg :=
  [SP lF14_0; SK lC14_1 n1; SP lF14_1; SK lC14_2 n2; SP lF14_2; SK lC14_3 n3; SP lF14_3; SK lC14_4 n4;
    SP lF14_4; SK lC14_5 n5; SP lF14_5; SK lC14_6 n6; SP lF14_6; SK lC14_7 n7; SP lF14_7; SK lC14_8
    n8; SP lF14_8; SK lC14_9 n9; SP lF14_9; SK lC14_10 n10; SP lF14_10; SK lC14_11 n11; SP lF14_11;
    SK lC14_12 n12; SP lF14_12].

Lemma runA14 : forall n1 n2 n3 n4 n5 n6 n7 n8 n9 n10 n11 n12,
  Run st140 (F14_0 ++ rp K14_1 n1 ++ F14_1 ++ rp K14_2 n2 ++ F14_2 ++ rp K14_3 n3 ++ F14_3 ++ rp K14_4
    n4 ++ F14_4 ++ rp K14_5 n5 ++ F14_5 ++ rp K14_6 n6 ++ F14_6 ++ rp K14_7 n7 ++ F14_7 ++ rp K14_8
    n8 ++ F14_8 ++ rp K14_9 n9 ++ F14_9 ++ rp K14_10 n10 ++ F14_10 ++ rp K14_11 n11 ++ F14_11 ++ rp
    K14_12 n12 ++ F14_12 ++ []) Se14
      (segSh (segs14 n1 n2 n3 n4 n5 n6 n7 n8 n9 n10 n11 n12)) (segV (segs14 n1 n2 n3 n4 n5 n6 n7 n8 n9 n10 n11 n12)).
Proof.
  intros n1 n2 n3 n4 n5 n6 n7 n8 n9 n10 n11 n12. unfold segs14.
  exact (run_SP _ _ _ _ _ _ _ RF14_0
    (run_SK _ _ _ _ _ _ _ RC14_1
    (run_SP _ _ _ _ _ _ _ RF14_1 (run_SK _ _ _ _ _ _ _ RC14_2
    (run_SP _ _ _ _ _ _ _ RF14_2 (run_SK _ _ _ _ _ _ _ RC14_3
    (run_SP _ _ _ _ _ _ _ RF14_3 (run_SK _ _ _ _ _ _ _ RC14_4
    (run_SP _ _ _ _ _ _ _ RF14_4 (run_SK _ _ _ _ _ _ _ RC14_5
    (run_SP _ _ _ _ _ _ _ RF14_5 (run_SK _ _ _ _ _ _ _ RC14_6
    (run_SP _ _ _ _ _ _ _ RF14_6 (run_SK _ _ _ _ _ _ _ RC14_7
    (run_SP _ _ _ _ _ _ _ RF14_7 (run_SK _ _ _ _ _ _ _ RC14_8
    (run_SP _ _ _ _ _ _ _ RF14_8 (run_SK _ _ _ _ _ _ _ RC14_9
    (run_SP _ _ _ _ _ _ _ RF14_9 (run_SK _ _ _ _ _ _ _ RC14_10
    (run_SP _ _ _ _ _ _ _ RF14_10 (run_SK _ _ _ _ _ _ _ RC14_11
    (run_SP _ _ _ _ _ _ _ RF14_11 (run_SK _ _ _ _ _ _ _ RC14_12
    (run_SP _ _ _ _ _ _ _ RF14_12 (run_end _)))))))))))))))))))))))))).
Qed.

(** ** The halt *)

Lemma fin14 : fin (srun (N.to_nat 200000) (apost Se14 Fw14)) = true.
Proof. vm_compute. reflexivity. Qed.

Lemma halt14_gen : forall n1 n2 n3 n4 n5 n6 n7 n8 n9 n10 n11 n12 u,
  Lvl je14 (b14 (cc14_1 + (n1 * kq14_1 + jj14_1) + 1) (cc14_2 + (n2 * kq14_2 + jj14_2) + 1) (cc14_3 +
    (n3 * kq14_3 + jj14_3) + 1) (cc14_4 + (n4 * kq14_4 + jj14_4) + 1) (cc14_5 + (n5 * kq14_5 +
    jj14_5) + 1) (cc14_6 + (n6 * kq14_6 + jj14_6) + 1) (cc14_7 + (n7 * kq14_7 + jj14_7) + 1) (cc14_8
    + (n8 * kq14_8 + jj14_8) + 1) (cc14_9 + (n9 * kq14_9 + jj14_9) + 1) (cc14_10 + (n10 * kq14_10 +
    jj14_10) + 1) (cc14_11 + (n11 * kq14_11 + jj14_11) + 1) (cc14_12 + (n12 * kq14_12 + jj14_12) +
    1)) u w14 -> halts tm c0.
Proof.
  intros n1 n2 n3 n4 n5 n6 n7 n8 n9 n10 n11 n12 u H.
  apply (gate je14 (b14 (cc14_1 + (n1 * kq14_1 + jj14_1) + 1) (cc14_2 + (n2 * kq14_2 + jj14_2) + 1)
    (cc14_3 + (n3 * kq14_3 + jj14_3) + 1) (cc14_4 + (n4 * kq14_4 + jj14_4) + 1) (cc14_5 + (n5 *
    kq14_5 + jj14_5) + 1) (cc14_6 + (n6 * kq14_6 + jj14_6) + 1) (cc14_7 + (n7 * kq14_7 + jj14_7) +
    1) (cc14_8 + (n8 * kq14_8 + jj14_8) + 1) (cc14_9 + (n9 * kq14_9 + jj14_9) + 1) (cc14_10 + (n10 *
    kq14_10 + jj14_10) + 1) (cc14_11 + (n11 * kq14_11 + jj14_11) + 1) (cc14_12 + (n12 * kq14_12 +
    jj14_12) + 1)) u w14 (F14_0 ++ rp K14_1 n1 ++ F14_1 ++ rp K14_2 n2 ++ F14_2 ++ rp K14_3 n3 ++
    F14_3 ++ rp K14_4 n4 ++ F14_4 ++ rp K14_5 n5 ++ F14_5 ++ rp K14_6 n6 ++ F14_6 ++ rp K14_7 n7 ++
    F14_7 ++ rp K14_8 n8 ++ F14_8 ++ rp K14_9 n9 ++ F14_9 ++ rp K14_10 n10 ++ F14_10 ++ rp K14_11
    n11 ++ F14_11 ++ rp K14_12 n12 ++ F14_12 ++ []) Fw14 Se14 (segSh (segs14 n1 n2 n3 n4 n5 n6 n7 n8
    n9 n10 n11 n12)) (N.to_nat 200000) H).
  - change (rep10 je14 ++ c1101 ++ encb false (b14 (cc14_1 + (n1 * kq14_1 + jj14_1) + 1) (cc14_2 + (n2 *
    kq14_2 + jj14_2) + 1) (cc14_3 + (n3 * kq14_3 + jj14_3) + 1) (cc14_4 + (n4 * kq14_4 + jj14_4) +
    1) (cc14_5 + (n5 * kq14_5 + jj14_5) + 1) (cc14_6 + (n6 * kq14_6 + jj14_6) + 1) (cc14_7 + (n7 *
    kq14_7 + jj14_7) + 1) (cc14_8 + (n8 * kq14_8 + jj14_8) + 1) (cc14_9 + (n9 * kq14_9 + jj14_9) +
    1) (cc14_10 + (n10 * kq14_10 + jj14_10) + 1) (cc14_11 + (n11 * kq14_11 + jj14_11) + 1) (cc14_12
    + (n12 * kq14_12 + jj14_12) + 1)) ++ w14)
      with (cells14 (cc14_1 + (n1 * kq14_1 + jj14_1) + 1) (cc14_2 + (n2 * kq14_2 + jj14_2) + 1) (cc14_3 + (n3 * kq14_3 + jj14_3) + 1) (cc14_4 + (n4 * kq14_4 + jj14_4) + 1) (cc14_5 + (n5 * kq14_5 + jj14_5) + 1) (cc14_6 + (n6 * kq14_6 + jj14_6) + 1) (cc14_7 + (n7 * kq14_7 + jj14_7) + 1) (cc14_8 + (n8 * kq14_8 + jj14_8) + 1) (cc14_9 + (n9 * kq14_9 + jj14_9) + 1) (cc14_10 + (n10 * kq14_10 + jj14_10) + 1) (cc14_11 + (n11 * kq14_11 + jj14_11) + 1) (cc14_12 + (n12 * kq14_12 + jj14_12) + 1)).
    apply cells14_cut.
  - unfold RunW. intros t R k. destruct (runA14 n1 n2 n3 n4 n5 n6 n7 n8 n9 n10 n11 n12 t R k) as [m [k2 [E _]]].
    exists m, k2. exact E.
  - exact fin14.
Qed.

Definition h14_1 : nat := (c14_1 - (cc14_1 + 1 + jj14_1)) / kq14_1.
Lemma EH14_1 : c14_1 = cc14_1 + (h14_1 * kq14_1 + jj14_1) + 1.
Proof.
  pose proof c14_1_res2 as H2. pose proof c14_1_lb as Hb.
  unfold rb14_1 in H2. unfold lb14_1 in Hb.
  unfold h14_1, cc14_1, kq14_1, jj14_1. cbn [Z.of_N] in H2, Hb. gl c14_1.
Qed.

Definition h14_2 : nat := (c14_2 - (cc14_2 + 1 + jj14_2)) / kq14_2.
Lemma EH14_2 : c14_2 = cc14_2 + (h14_2 * kq14_2 + jj14_2) + 1.
Proof.
  pose proof c14_2_res2 as H2. pose proof c14_2_lb as Hb.
  unfold rb14_2 in H2. unfold lb14_2 in Hb.
  unfold h14_2, cc14_2, kq14_2, jj14_2. cbn [Z.of_N] in H2, Hb. gl c14_2.
Qed.

Definition h14_3 : nat := (c14_3 - (cc14_3 + 1 + jj14_3)) / kq14_3.
Lemma EH14_3 : c14_3 = cc14_3 + (h14_3 * kq14_3 + jj14_3) + 1.
Proof.
  pose proof c14_3_res2 as H2. pose proof c14_3_lb as Hb.
  unfold rb14_3 in H2. unfold lb14_3 in Hb.
  unfold h14_3, cc14_3, kq14_3, jj14_3. cbn [Z.of_N] in H2, Hb. gl c14_3.
Qed.

Definition h14_4 : nat := (c14_4 - (cc14_4 + 1 + jj14_4)) / kq14_4.
Lemma EH14_4 : c14_4 = cc14_4 + (h14_4 * kq14_4 + jj14_4) + 1.
Proof.
  pose proof c14_4_res2 as H2. pose proof c14_4_lb as Hb.
  unfold rb14_4 in H2. unfold lb14_4 in Hb.
  unfold h14_4, cc14_4, kq14_4, jj14_4. cbn [Z.of_N] in H2, Hb. gl c14_4.
Qed.

Definition h14_5 : nat := (c14_5 - (cc14_5 + 1 + jj14_5)) / kq14_5.
Lemma EH14_5 : c14_5 = cc14_5 + (h14_5 * kq14_5 + jj14_5) + 1.
Proof.
  pose proof c14_5_res2 as H2. pose proof c14_5_lb as Hb.
  unfold rb14_5 in H2. unfold lb14_5 in Hb.
  unfold h14_5, cc14_5, kq14_5, jj14_5. cbn [Z.of_N] in H2, Hb. gl c14_5.
Qed.

Definition h14_6 : nat := (c14_6 - (cc14_6 + 1 + jj14_6)) / kq14_6.
Lemma EH14_6 : c14_6 = cc14_6 + (h14_6 * kq14_6 + jj14_6) + 1.
Proof.
  pose proof c14_6_res2 as H2. pose proof c14_6_lb as Hb.
  unfold rb14_6 in H2. unfold lb14_6 in Hb.
  unfold h14_6, cc14_6, kq14_6, jj14_6. cbn [Z.of_N] in H2, Hb. gl c14_6.
Qed.

Definition h14_7 : nat := (c14_7 - (cc14_7 + 1 + jj14_7)) / kq14_7.
Lemma EH14_7 : c14_7 = cc14_7 + (h14_7 * kq14_7 + jj14_7) + 1.
Proof.
  pose proof c14_7_res2 as H2. pose proof c14_7_lb as Hb.
  unfold rb14_7 in H2. unfold lb14_7 in Hb.
  unfold h14_7, cc14_7, kq14_7, jj14_7. cbn [Z.of_N] in H2, Hb. gl c14_7.
Qed.

Definition h14_8 : nat := (c14_8 - (cc14_8 + 1 + jj14_8)) / kq14_8.
Lemma EH14_8 : c14_8 = cc14_8 + (h14_8 * kq14_8 + jj14_8) + 1.
Proof.
  pose proof c14_8_res2 as H2. pose proof c14_8_lb as Hb.
  unfold rb14_8 in H2. unfold lb14_8 in Hb.
  unfold h14_8, cc14_8, kq14_8, jj14_8. cbn [Z.of_N] in H2, Hb. gl c14_8.
Qed.

Definition h14_9 : nat := (c14_9 - (cc14_9 + 1 + jj14_9)) / kq14_9.
Lemma EH14_9 : c14_9 = cc14_9 + (h14_9 * kq14_9 + jj14_9) + 1.
Proof.
  pose proof c14_9_res2 as H2. pose proof c14_9_lb as Hb.
  unfold rb14_9 in H2. unfold lb14_9 in Hb.
  unfold h14_9, cc14_9, kq14_9, jj14_9. cbn [Z.of_N] in H2, Hb. gl c14_9.
Qed.

Definition h14_10 : nat := (c14_10 - (cc14_10 + 1 + jj14_10)) / kq14_10.
Lemma EH14_10 : c14_10 = cc14_10 + (h14_10 * kq14_10 + jj14_10) + 1.
Proof.
  pose proof c14_10_res2 as H2. pose proof c14_10_lb as Hb.
  unfold rb14_10 in H2. unfold lb14_10 in Hb.
  unfold h14_10, cc14_10, kq14_10, jj14_10. cbn [Z.of_N] in H2, Hb. gl c14_10.
Qed.

Definition h14_11 : nat := (c14_11 - (cc14_11 + 1 + jj14_11)) / kq14_11.
Lemma EH14_11 : c14_11 = cc14_11 + (h14_11 * kq14_11 + jj14_11) + 1.
Proof.
  pose proof c14_11_res2 as H2. pose proof c14_11_lb as Hb.
  unfold rb14_11 in H2. unfold lb14_11 in Hb.
  unfold h14_11, cc14_11, kq14_11, jj14_11. cbn [Z.of_N] in H2, Hb. gl c14_11.
Qed.

Definition h14_12 : nat := (c14_12 - (cc14_12 + 1 + jj14_12)) / kq14_12.
Lemma EH14_12 : c14_12 = cc14_12 + (h14_12 * kq14_12 + jj14_12) + 1.
Proof.
  pose proof c14_12_res2 as H2. pose proof c14_12_lb as Hb.
  unfold rb14_12 in H2. unfold lb14_12 in Hb.
  unfold h14_12, cc14_12, kq14_12, jj14_12. cbn [Z.of_N] in H2, Hb. gl c14_12.
Qed.

Theorem halt14 : halts tm c0.
Proof.
  pose proof lvl14 as H.
  rewrite EH14_1 in H.
  rewrite EH14_2 in H.
  rewrite EH14_3 in H.
  rewrite EH14_4 in H.
  rewrite EH14_5 in H.
  rewrite EH14_6 in H.
  rewrite EH14_7 in H.
  rewrite EH14_8 in H.
  rewrite EH14_9 in H.
  rewrite EH14_10 in H.
  rewrite EH14_11 in H.
  rewrite EH14_12 in H.
  exact (halt14_gen h14_1 h14_2 h14_3 h14_4 h14_5 h14_6 h14_7 h14_8 h14_9 h14_10 h14_11 h14_12 _ H).
Qed.

End L14h.

Theorem halt : halts tm c0.
Proof. exact L14h.halt14. Qed.
