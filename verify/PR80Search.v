From BusyCoq Require Import Individual62.
From Coq Require Import Bool List Lists.Streams Arith Lia NArith String.
From BusyCoq Require Import PR80Core PR80Closure.
Import ListNotations PR80Core.TM1.
Close Scope sym_scope.
Open Scope list_scope.
Open Scope bool_scope.
Open Scope nat_scope.

Local Definition zeroVars := v5 0 0 0 0 0.
Definition InAttractor (cfg : Q * tape) : Prop :=
  exists m z c k, InvM m z c k /\ cfg = mCfg m z c k.

Definition checkEntry (m z c a b : nat) : bool :=
  let k := b / 3 in
  (a =? 6 * k + 7) && (b =? 3 * k) &&
  (k <=? 5) && (1 <=? z) && (33 <=? m) &&
  (9 * m <=? c) && (2100 <=? c).

Lemma checkEntry_sound m z c a b :
  checkEntry m z c a b = true ->
  a = 6 * (b / 3) + 7 /\ b = 3 * (b / 3) /\ InvM m z c (b / 3).
Proof.
  unfold checkEntry, InvM. rewrite !andb_true_iff, !Nat.eqb_eq, !Nat.leb_le.
  tauto.
Qed.

Definition symAttractor (s : SymState) : bool :=
  let val := evalSymN zeroVars in
  match s with
  | (mA, [sl_pair 1 0 x; sl_mid m; sl_pair 1 1 y; sl_pair 1 0 w],
    [sr_pair 0 0 u; sr_pair 1 1 a; mid; sr_pair 1 1 b;
      sr_pair 1 2 v; sr_pair 1 1 c; sr_pair 1 0 t]) =>
    (symIsZero x && symIsZero y && symIsZero w &&
     symIsZero u && symIsZero v && symIsZero t) &&
    match mid with
    | sr_mid z => symIsZero z &&
        checkEntry (val m + 1) 1 (val c + 1) (val a + 3) (val b)
    | sr_pair 2 0 z =>
        checkEntry (val m + 1) (val z + 1) (val c + 1) (val a + 1) (val b)
    | _ => false
    end
  | _ => false
  end.

Lemma symAttractor_sound s :
  symAttractor s = true -> InAttractor (evalSym zeroVars s).
Proof.
  assert (symIsZero_eq : forall x, symIsZero x = true -> x = symZero).
  { intros []. unfold symIsZero, symIsConst. cbn.
    rewrite !andb_true_iff, !N.eqb_eq.
    intros (((((-> & ->) & ->) & ->) & ->) & ->). reflexivity. }
  destruct s as [[mode ls] rs]; destruct mode; try discriminate.
  destruct ls as [| [[| [| ?]] [| ?] x | ?] ls]; try discriminate.
  destruct ls as [| [ ? ? ? | m] ls]; try discriminate.
  destruct ls as [| [[| [| ?]] [| [| ?]] y | ?] ls]; try discriminate.
  destruct ls as [| [[| [| ?]] [| ?] w | ?] [| ? ?]]; try discriminate.
  destruct rs as [| [[| ?] [| ?] u | ?] rs]; try discriminate.
  destruct rs as [| [[| [| ?]] [| [| ?]] a | ?] rs]; try discriminate.
  destruct rs as [| mid rs]; try discriminate.
  destruct rs as [| [[| [| ?]] [| [| ?]] b | ?] rs]; try discriminate.
  destruct rs as [| [[| [| ?]] [| [| [| ?]]] v | ?] rs]; try discriminate.
  destruct rs as [| [[| [| ?]] [| [| ?]] c | ?] rs]; try discriminate.
  destruct rs as [| [[| [| ?]] [| ?] t | ?] [| ? ?]]; try discriminate.
  destruct mid as [[| [| [| ?]]] [| ?] z | z]; try discriminate;
    cbn [symAttractor];
    rewrite !andb_true_iff;
    intros ((((((Hx & Hy) & Hw) & Hu) & Hv) & Ht) & H); try discriminate H.
  all: apply symIsZero_eq in Hx, Hy, Hw, Hu, Hv, Ht; subst.
  - apply checkEntry_sound in H as (Ha & Hb & Hi).
    do 4 eexists. split; [exact Hi |].
    apply eval_mCfg_z2; [reflexivity | exact Ha | reflexivity | now rewrite <- Hb | reflexivity].
  - destruct H as (Hz & H). apply symIsZero_eq in Hz. subst.
    apply checkEntry_sound in H as (Ha & Hb & Hi).
    do 4 eexists. split; [exact Hi |].
    apply eval_mCfg_z1; [reflexivity | exact Ha | now rewrite <- Hb | reflexivity].
Qed.

(* The fuel bounds computation only. Membership is checked at every state. *)
Fixpoint seekEntry (fuel : nat) (s : SymState) : option SymState :=
  if symAttractor s then Some s else
  match fuel with
  | 0 => None
  | S fuel' =>
    match symStep s with
    | Some t => seekEntry fuel' t
    | None => None
    end
  end.

Lemma seekEntry_sound fuel s t :
  seekEntry fuel s = Some t ->
  evalSym zeroVars s -[ tm ]->* evalSym zeroVars t /\
  InAttractor (evalSym zeroVars t).
Proof.
  revert s. induction fuel as [|fuel IH]; intros s H;
    cbn [seekEntry] in H;
    destruct (symAttractor s) eqn:Hentry.
  - inversion H; subst. split; [apply evstep_refl | now apply symAttractor_sound].
  - discriminate.
  - inversion H; subst. split; [apply evstep_refl | now apply symAttractor_sound].
  - destruct (symStep s) as [u|] eqn:Hstep; [|discriminate].
    apply IH in H as (Hreach & Hattr).
    exact (conj (etrans (pev (symStep_sound zeroVars Hstep)) Hreach) Hattr).
Qed.

Local Definition searchOK (s : SymState) : bool :=
  match seekEntry 3000 s with Some _ => true | None => false end.

Lemma nonhalt_from_search (other : TM) (f : Q * tape -> Q * tape)
  (fstep : forall a b, a -[ tm ]-> b -> f a -[ other ]-> f b)
  (s : SymState) (hstart : f (evalSym zeroVars s) = c0)
  (hsearch : searchOK s = true) :
  ~ halts other c0.
Proof.
  assert (fstar : forall a b, a -[ tm ]->* b -> f a -[ other ]->* f b).
  { intros a b H. induction H; eauto. }
  assert (fplus : forall a b, a -[ tm ]->+ b -> f a -[ other ]->+ f b).
  { intros a b H. induction H; eauto. }
  unfold searchOK in hsearch.
  destruct (seekEntry 3000 s) as [t|] eqn:Hr; [|discriminate].
  pose proof (seekEntry_sound _ _ _ Hr) as (Hreach & Hentry).
  apply fstar in Hreach. rewrite hstart in Hreach.
  apply (multistep_nonhalt other c0 _ Hreach).
  set (A := fun q => exists p, InAttractor p /\ q = f p).
  apply (progress_nonhalt other A).
  - intros q (p & (m & z & c & k & Hin & ->) & ->).
    destruct (invM_step Hin) as (m' & z' & c' & k' & Hin' & Hstep).
    exists (f (mCfg m' z' c' k')). split.
    + exists (mCfg m' z' c' k'). split; [|reflexivity].
      now exists m', z', c', k'.
    + now apply fplus.
  - now exists (evalSym zeroVars t).
Qed.

Module TM1.
Definition tm := Eval compute in
  (TM_from_str "1RB1RE_1LC0RA_1LA0LD_1LB0LF_0RB0LE_0LA---").

Theorem nonhalt : ~ halts tm c0.
Proof.
  apply (nonhalt_from_search tm (fun x => x) (fun _ _ H => H) (mA, [], [])).
  - unfold evalSym, cfgA, encSL, encSR, c0.
    cbn [Streams.hd]. rewrite tl_const. reflexivity.
  - vm_compute. reflexivity.
Qed.
End TM1.

Module TM2.
Definition tm := Eval compute in
  (TM_from_str "1RB0RF_1RC0LD_1RD0RA_1LB1LE_0LB0RE_0RD---").

Definition mirrorState (q : Q) : Q :=
  match q with A => D | B => B | C => C | D => A | E => E | F => F end.

Definition mirrorCfg (c : Q * tape) : Q * tape :=
  match c with (q, l {{s}} r) => (mirrorState q, r {{s}} l) end.

Lemma mirror_step (c c' : Q * tape) :
  c -[ TM1.tm ]-> c' -> mirrorCfg c -[ tm ]-> mirrorCfg c'.
Proof.
  intros H. inversion H; subst;
    destruct q, s; try discriminate;
    inversion H0; subst;
    destruct l as [sl l'], r as [sr r'];
    cbn [mirrorCfg move_left move_right];
    (apply @step_left; reflexivity) || (apply @step_right; reflexivity).
Qed.

Theorem nonhalt : ~ halts tm c0.
Proof.
  apply (nonhalt_from_search tm mirrorCfg mirror_step (mD, [], [])).
  - unfold evalSym, cfgD, encSL, encSR, mirrorCfg, mirrorState, c0.
    cbn [Streams.hd]. rewrite tl_const. reflexivity.
  - vm_compute. reflexivity.
Qed.
End TM2.

Print Assumptions TM1.nonhalt.
Print Assumptions TM2.nonhalt.
