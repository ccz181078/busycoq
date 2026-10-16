(* 1RB1RA_1LC1LE_0LD0LB_0RA0RF_0LC0RA_1RD--- never halts. *)

From BusyCoq Require Import Individual62.
From Coq Require Import Lia ZifyNat PeanoNat String List.
Import ListNotations.

Open Scope list.
Open Scope sym.

Definition tm := Eval compute in
  (TM_from_str "1RB1RA_1LC1LE_0LD0LB_0RA0RF_0LC0RA_1RD---").

Notation "c --> c'" := (c -[ tm ]-> c')   (at level 40).
Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Open Scope nat_scope.

(* ---------- Tape encodings and stream identities ---------- *)

Lemma default_eq_0 : 0%sym >> 0inf%sym = 0inf%sym.
Proof. solve_const0_eq. Qed.

Fixpoint encL (w : list nat) : side :=
  match w with
  | [] => 1%sym >> 0inf%sym
  | 0 :: w' => 1%sym >> 1%sym >> 0%sym >> encL w'
  | S n :: w' => 1%sym >> ([0]%sym^^(S n) *> encL w')
  end.

Lemma encL_unfold (w : list nat) :
  encL w = 1%sym >> Streams.tl (encL w).
Proof.
  destruct w as [| [| n] w']; reflexivity.
Qed.

Definition bumpW (w : list nat) : list nat :=
  match w with
  | [] => []
  | 0 :: w' => 1 :: 1 :: w'
  | S n :: w' => S (S n) :: w'
  end.

Lemma encL_bumpW (w : list nat) :
  1%sym >> 0%sym >> Streams.tl (encL w) = encL (bumpW w).
Proof.
  destruct w as [| [| n] w'].
  - cbn. rewrite default_eq_0. reflexivity.
  - reflexivity.
  - reflexivity.
Qed.

Inductive RTag : Type := R0 | R1 | R2.

Fixpoint encR (v : list RTag) : side :=
  match v with
  | [] => 0inf%sym
  | R0 :: v' => 0%sym >> encR v'
  | R1 :: v' => 1%sym >> 0%sym >> encR v'
  | R2 :: v' => 1%sym >> 1%sym >> 0%sym >> encR v'
  end.

(* ---------- Symbolic invariants ---------- *)

Inductive GoodVA : nat -> list RTag -> Prop :=
  | GVA_zero : GoodVA 0 [R0]
  | GVA_z001 (a : nat) (v : list RTag) :
      GoodVA a (R0 :: v) -> GoodVA 0 (R0 :: R0 :: R1 :: v)
  | GVA_z01 (a : nat) (v : list RTag) :
      GoodVA a (R0 :: v) -> GoodVA (S a) (R0 :: R1 :: v)
  | GVA_z02 (a : nat) (v : list RTag) :
      GoodVA a (R0 :: v) -> GoodVA 0 (R0 :: R2 :: v).

Inductive GoodCD : nat -> list RTag -> Prop :=
  | GCD_nil : GoodCD 0 []
  | GCD_z01 (a : nat) (v : list RTag) :
      GoodVA a (R0 :: v) -> GoodCD 0 (R0 :: R1 :: v)
  | GCD_z1 (b : nat) (v : list RTag) :
      GoodCD b v -> GoodCD (S b) (R1 :: v).

Lemma GoodVA_cons0 {b : nat} {v : list RTag} (H : GoodCD b v) :
  GoodVA b (R0 :: v).
Proof.
  induction H as [| a v Hv | b v Hv IH].
  - exact GVA_zero.
  - exact (GVA_z001 a v Hv).
  - exact (GVA_z01 b v IH).
Qed.

Inductive SafeW : nat -> list nat -> Prop :=
  | SW_nil (b : nat) : SafeW b []
  | SW_z0 (b : nat) (w : list nat) :
      SafeW 0 w -> SafeW b (0 :: w)
  | SW_z1 (b : nat) (w : list nat) :
      SafeW (S b) w -> SafeW b (1 :: w)
  | SW_z2 (b : nat) (w : list nat) :
      SafeW b w -> SafeW b (2 :: w)
  | SW_z3 (b k : nat) (w : list nat) :
      SafeW b (S (S k) :: w) -> SafeW (S b) (S (S (S k)) :: w).

Lemma SafeW_mono {b : nat} {w : list nat} (H : SafeW b w) :
  forall d : nat, b <= d -> SafeW d w.
Proof.
  induction H as [b | b w Hw _ | b w Hw IH | b w Hw IH | b k w Hw IH];
    intros d Hle.
  - apply SW_nil.
  - apply SW_z0, Hw.
  - apply SW_z1, IH; lia.
  - apply SW_z2, IH; lia.
  - destruct d as [| d']; [lia |].
    apply SW_z3, IH; lia.
Qed.

Lemma bumpW_safe {b : nat} {w : list nat} (H : SafeW b w) :
  SafeW (S b) (bumpW w).
Proof.
  inverts H as H0.
  - apply SW_nil.
  - apply SW_z1, SW_z1. eapply SafeW_mono; [exact H0 | lia].
  - apply SW_z2, H0.
  - apply (SW_z3 b 0), SW_z2, H0.
  - apply (SW_z3 (S b0) (S k)), SW_z3, H0.
Qed.

Inductive SafeWA : nat -> list nat -> Prop :=
  | SWA_nil (a : nat) : SafeWA a []
  | SWA_z0 (a : nat) (w : list nat) :
      SafeW 0 w -> SafeWA a (0 :: w)
  | SWA_z1 (a : nat) (w : list nat) :
      SafeW a w -> SafeWA a (1 :: w).

Lemma SafeWA_succ_to_SafeW {a : nat} {w : list nat} (H : SafeWA (S a) w) :
  SafeW a w.
Proof.
  inverts H as H0.
  - apply SW_nil.
  - apply SW_z0, H0.
  - apply SW_z1, H0.
Qed.

Lemma SafeWA_zero_to_SafeW0 {w : list nat} (H : SafeWA 0 w) :
  SafeW 0 w.
Proof.
  inverts H as H0.
  - apply SW_nil.
  - apply SW_z0, H0.
  - apply SW_z1. eapply SafeW_mono; [exact H0 | lia].
Qed.

Inductive SymMode : Type := modeC | modeD | modeA.

Definition evalSym (m : SymMode) (w : list nat) (v : list RTag) : Q * tape :=
  match m with
  | modeC => (encL w) <{{C}} (encR v)
  | modeD => (1%sym >> encL w) <{{D}} (0%sym >> encR v)
  | modeA => (encL w) {{A}}> (encR v)
  end.

Inductive GoodSym : Q * tape -> Prop :=
  | GS_C (b : nat) (w : list nat) (v : list RTag) :
      SafeW b w -> GoodCD b v -> GoodSym (evalSym modeC w v)
  | GS_D (b : nat) (w : list nat) (v : list RTag) :
      SafeW (S b) w -> GoodCD b v -> GoodSym (evalSym modeD w v)
  | GS_A (a : nat) (w : list nat) (v : list RTag) :
      SafeWA a w -> GoodVA a v -> GoodSym (evalSym modeA w v).

(* ---------- Macro-step transitions ---------- *)

Ltac step_n n :=
  eapply progress_intro; [prove_step | simpl_tape];
  do n step;
  finish.

Lemma step_C_nil (v : list RTag) :
  evalSym modeC [] v -->+ evalSym modeA [] (R0 :: v).
Proof.
  unfold evalSym; cbn [encL encR].
  eapply progress_intro; [prove_step | simpl_tape].
  do 7 step.
  repeat rewrite default_eq_0.
  finish.
Qed.

Lemma step_C_z0 (w' : list nat) (v : list RTag) :
  evalSym modeC (0 :: w') v -->+ evalSym modeC w' (R0 :: R1 :: v).
Proof.
  unfold evalSym; cbn [encL encR].
  eapply progress_intro; [prove_step | simpl_tape].
  do 2 step.
  finish.
Qed.

Lemma step_C_z1 (w' : list nat) (v : list RTag) :
  evalSym modeC (1 :: w') v -->+ evalSym modeC w' (R1 :: v).
Proof.
  unfold evalSym; cbn [encL encR lpow Str_app].
  eapply progress_intro; [prove_step | simpl_tape].
  step.
  finish.
Qed.

Lemma step_C_z2 (w' : list nat) (v : list RTag) :
  evalSym modeC (2 :: w') v -->+ evalSym modeD (bumpW w') v.
Proof.
  unfold evalSym; cbn [encL encR lpow Str_app].
  rewrite (encL_unfold w') at 1.
  eapply progress_intro; [prove_step | simpl_tape].
  do 4 step.
  rewrite encL_bumpW.
  finish.
Qed.

Lemma step_C_z3 (k : nat) (w' : list nat) (vt : list RTag) :
  evalSym modeC (S (S (S k)) :: w') (R1 :: vt) -->+
  evalSym modeA (1 :: S (S k) :: w') (R0 :: vt).
Proof.
  unfold evalSym; cbn [encL encR lpow Str_app].
  eapply progress_intro; [prove_step | simpl_tape].
  do 11 step.
  finish.
Qed.

Lemma step_D_nil (w : list nat) :
  evalSym modeD w [] -->+ evalSym modeC (1 :: w) [R1; R1].
Proof.
  unfold evalSym; cbn [encL encR lpow Str_app].
  eapply progress_intro; [prove_step | simpl_tape].
  do 6 step.
  finish.
Qed.

Lemma step_D_z01 (w : list nat) (vt : list RTag) :
  evalSym modeD w (R0 :: R1 :: vt) -->+ evalSym modeA (1 :: 1 :: w) (R0 :: vt).
Proof.
  unfold evalSym; cbn [encL encR lpow Str_app].
  eapply progress_intro; [prove_step | simpl_tape].
  do 3 step.
  finish.
Qed.

Lemma step_D_z1 (w : list nat) (vt : list RTag) :
  evalSym modeD w (R1 :: vt) -->+ evalSym modeD (1 :: w) vt.
Proof.
  unfold evalSym; cbn [encL encR lpow Str_app].
  eapply progress_intro; [prove_step | simpl_tape].
  step.
  finish.
Qed.

Lemma step_A_z01 (w : list nat) (vt : list RTag) :
  evalSym modeA w (R0 :: R1 :: vt) -->+ evalSym modeA (1 :: w) (R0 :: vt).
Proof.
  unfold evalSym; cbn [encL encR lpow Str_app].
  eapply progress_intro; [prove_step | simpl_tape].
  do 3 step.
  finish.
Qed.

Lemma step_A_z02 (w : list nat) (vt : list RTag) :
  evalSym modeA w (R0 :: R2 :: vt) -->+ evalSym modeA (0 :: w) (R0 :: vt).
Proof.
  unfold evalSym; cbn [encL encR lpow Str_app].
  eapply progress_intro; [prove_step | simpl_tape].
  do 4 step.
  finish.
Qed.

Lemma step_A_zero_nil :
  evalSym modeA [] [R0] -->+ evalSym modeA [] [R0; R2; R1].
Proof.
  unfold evalSym; cbn [encL encR lpow Str_app].
  eapply progress_intro; [prove_step | simpl_tape].
  do 16 step.
  repeat rewrite default_eq_0.
  finish.
Qed.

Lemma step_A_zero_z0 (w' : list nat) :
  evalSym modeA (0 :: w') [R0] -->+ evalSym modeA (1 :: 2 :: w') [R0].
Proof.
  unfold evalSym; cbn [encL encR lpow Str_app].
  eapply progress_intro; [prove_step | simpl_tape].
  do 9 step.
  repeat rewrite default_eq_0.
  finish.
Qed.

Lemma step_A_zero_z1 (w' : list nat) :
  evalSym modeA (1 :: w') [R0] -->+ evalSym modeC w' [R0; R1; R1].
Proof.
  unfold evalSym; cbn [encL encR lpow Str_app].
  eapply progress_intro; [prove_step | simpl_tape].
  do 4 step.
  repeat rewrite default_eq_0.
  finish.
Qed.

Lemma step_A_z001_nil (vt : list RTag) :
  evalSym modeA [] (R0 :: R0 :: R1 :: vt) -->+
  evalSym modeA [] (R0 :: R2 :: R2 :: vt).
Proof.
  unfold evalSym; cbn [encL encR lpow Str_app].
  eapply progress_intro; [prove_step | simpl_tape].
  do 16 step.
  repeat rewrite default_eq_0.
  finish.
Qed.

Lemma step_A_z001_z0 (w' : list nat) (vt : list RTag) :
  evalSym modeA (0 :: w') (R0 :: R0 :: R1 :: vt) -->+
  evalSym modeA (0 :: 2 :: w') (R0 :: vt).
Proof.
  unfold evalSym; cbn [encL encR lpow Str_app].
  eapply progress_intro; [prove_step | simpl_tape].
  do 10 step.
  finish.
Qed.

Lemma step_A_z001_z1 (w' : list nat) (vt : list RTag) :
  evalSym modeA (1 :: w') (R0 :: R0 :: R1 :: vt) -->+
  evalSym modeC w' (R0 :: R1 :: R2 :: vt).
Proof.
  unfold evalSym; cbn [encL encR lpow Str_app].
  eapply progress_intro; [prove_step | simpl_tape].
  do 4 step.
  finish.
Qed.

(* ---------- Closure and non-halting ---------- *)

Lemma step_sym_closed (c : Q * tape) (H : GoodSym c) :
  exists c' : Q * tape, GoodSym c' /\ c -->+ c'.
Proof.
  destruct H as [b w v Hw Hv | b w v Hw Hv | a w v Hw Hv].
  - inverts Hw as Hw'.
    + eexists. split; [| apply step_C_nil].
      eapply GS_A; [apply SWA_nil | exact (GoodVA_cons0 Hv)].
    + eexists. split; [| apply step_C_z0].
      eapply GS_C; [exact Hw' | eapply GCD_z01; exact (GoodVA_cons0 Hv)].
    + eexists. split; [| apply step_C_z1].
      eapply GS_C; [exact Hw' | apply GCD_z1, Hv].
    + eexists. split; [| apply step_C_z2].
      eapply GS_D; [apply bumpW_safe, Hw' | exact Hv].
    + inverts Hv as Hvt.
      eexists. split; [| apply step_C_z3].
      eapply GS_A; [apply SWA_z1, Hw' | exact (GoodVA_cons0 Hvt)].
  - inverts Hv as Hvt.
    + eexists. split; [| apply step_D_nil].
      apply (GS_C 2).
      * apply SW_z1. eapply SafeW_mono; [exact Hw | lia].
      * apply GCD_z1, GCD_z1, GCD_nil.
    + eexists. split; [| apply step_D_z01].
      eapply GS_A; [| exact Hvt].
      apply SWA_z1. eapply SafeW_mono; [apply SW_z1, Hw | lia].
    + eexists. split; [| apply step_D_z1].
      eapply GS_D; [apply SW_z1, Hw | exact Hvt].
  - inverts Hv as Hvt.
    + inverts Hw as Hw'.
      * eexists. split; [| apply step_A_zero_nil].
        apply (GS_A 0); [apply SWA_nil | eapply GVA_z02; eapply GVA_z01; exact GVA_zero].
      * eexists. split; [| apply step_A_zero_z0].
        apply (GS_A 0); [apply SWA_z1, SW_z2, Hw' | exact GVA_zero].
      * eexists. split; [| apply step_A_zero_z1].
        apply (GS_C 0); [exact Hw' | eapply GCD_z01; eapply GVA_z01; exact GVA_zero].
    + inverts Hw as Hw'.
      * eexists. split; [| apply step_A_z001_nil].
        apply (GS_A 0); [apply SWA_nil | eapply GVA_z02; eapply GVA_z02; exact Hvt].
      * eexists. split; [| apply step_A_z001_z0].
        eapply GS_A; [apply SWA_z0, SW_z2, Hw' | exact Hvt].
      * eexists. split; [| apply step_A_z001_z1].
        apply (GS_C 0); [exact Hw' | eapply GCD_z01; eapply GVA_z02; exact Hvt].
    + eexists. split; [| apply step_A_z01].
      eapply GS_A; [apply SWA_z1, SafeWA_succ_to_SafeW, Hw | exact Hvt].
    + eexists. split; [| apply step_A_z02].
      eapply GS_A; [apply SWA_z0, SafeWA_zero_to_SafeW0, Hw | exact Hvt].
Qed.

Definition c_init : Q * tape := evalSym modeC [] [R1].

Lemma start : c0 -->* c_init.
Proof.
  unfold c_init, evalSym; cbn [encL encR].
  change ((1%sym >> 0inf%sym) <{{C}} (1%sym >> 0%sym >> 0inf%sym))
    with ((0inf%sym <* [1]%sym) <{{C}} (1%sym >> 0%sym >> 0inf%sym)).
  solve_init.
Qed.

Lemma nonhalt : ~ halts tm c0.
Proof.
  eapply multistep_nonhalt with (c' := c_init).
  - exact start.
  - apply progress_nonhalt with (P := GoodSym).
    + exact step_sym_closed.
    + unfold c_init. apply (GS_C 1 [] [R1] (SW_nil 1) (GCD_z1 0 [] GCD_nil)).
Qed.

Print Assumptions nonhalt.
