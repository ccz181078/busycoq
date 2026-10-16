(* 1RB0RF_1RC1RF_1LD0RE_---0LE_1LA0LE_0RA0LC never halts.
   Bell eats counter with a residue (sheet class Bell eats counter). The hub is
   K(a,b,X) = 0^inf (110)^a 0 (011)^b C> X 0^inf. A bounce moves the 0 marker one block to
   the right and applies the local pass LP to the counter word X; at b = 1 the low digit of
   X is eaten. One bounce can run a whole sub-epoch on the rest of the word (rule D6).
   The marker bounce is FractalBEC's RInc; the local pass, the eats and the nested
   sub-epoch are new.
   Sections 1-4: finite runs (es), a word syntax with an encoding into tapes, the local pass
   LP and the epoch map Phi as mutually inductive relations, soundness (every derivation is a
   TM run), one epoch K(1,N,y) -->+ K(1,k+1,y').
   Sections 5-6: a computable model (lpf/phif) and counter words (gw, ginc, gval).
   Sections 7-9: GPhi (the epoch map on counter words), the digestion of a residue (DigP/DigT,
   with the nested levels of D6), its existence, and potential bounds over positions: the
   Q potential bounds the created positions (write-up Lemma C), a weighted potential bounds the
   cost (digestion bounces) and the merged block exponents (write-up D.1-D.3).
   Sections 10-11: the orbit invariant (number of blocks, weighted exponent masses, prefix
   exponent, budget), the threshold N >= 17705 (computed for kappa <= 13, induction above),
   the finite part (the model from K(1,8,t2) to epoch 694, N = 17713, by vm_compute) and nonhalt.
   The invariant is a simpler variant of the write-up's D.6: two weighted masses
   (weights 2^((q+1)/2) and 2^(q+1)) in place of the excess profile.
   Adapted from verify/FractalBEC.v, tm10 (its RInc, mirrored).
   Informal proof: the accompanying write-up (1RB0RF_1RC1RF_1LD0RE_---0LE_1LA0LE_0RA0LC_writeup.md).
   Formalized with Claude Code (AI-assisted).
   Checked: compiles against unmodified busycoq BB6 (commit 0940bb9) with Coq 8.20.1;
   Print Assumptions nonhalt: Closed under the global context. *)

From BusyCoq Require Import Individual62.
Require Import Lia.
Require Import String.
Require Import List.
Require Import Arith.

Definition tm := Eval compute in (TM_from_str "1RB0RF_1RC1RF_1LD0RE_---0LE_1LA0LE_0RA0LC").

Notation "c --> c'" := (c -[ tm ]-> c')   (at level 40).
Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Open Scope list.

(* ===================================================================== *)
(* Section 1. Finite runs (write-up 3.1-3.7), each one plain es.          *)
(* Left sides are written nearest-cell-first (<[...] reverses a literal). *)
(* ===================================================================== *)

(* LP0: 011 C> 0 r -> <A 100 1 r *)
Lemma LP0 l r : l <* <[0;1;1] {{C}}> [0] *> r -->+ l <{{A}} [1;0;0;1] *> r.
Proof. es. Qed.

Lemma LP0z l : l <* <[0;1;1] {{C}}> 0inf -->+ l <{{A}} [1;0;0;1] *> 0inf.
Proof. es. Qed.

(* LP11: 011 C> 110 r -> <A 101 000 r *)
Lemma LP11 l r : l <* <[0;1;1] {{C}}> [1;1;0] *> r -->+ l <{{A}} [1;0;1;0;0;0] *> r.
Proof. es. Qed.

(* LPC (carry), right pass: 011 C> 101 (001)^e 000 r -> 011 111 (011)^e 011 C> r *)
Lemma LPCr l e r : l <* <[0;1;1] {{C}}> [1;0;1] *> [0;0;1]^^e *> [0;0;0] *> r -->+
  l <* <[0;1;1;1;1;1] <* <[0;1;1]^^e <* <[0;1;1] {{C}}> r.
Proof. es. Qed.

(* LPC, left pass after an exit with d = 0 / d = 1 *)
Lemma LPCl0 l e r : l <* <[0;1;1;1;1;1] <* <[0;1;1]^^e <{{A}} [1;0;0] *> r -->+
  l <{{A}} [1;0;0;0;0;1] *> [0;0;1]^^e *> [0;0;0] *> r.
Proof. es. Qed.

Lemma LPCl1 l e r : l <* <[0;1;1;1;1;1] <* <[0;1;1]^^e <{{A}} [1;0;1;0;0;0] *> r -->+
  l <{{A}} [1;0;0;0;0;1] *> [0;0;1]^^(S e) *> [0;0;0] *> r.
Proof. es. Qed.

(* LP5 (D5): 011 C> 10 001 (001)^e 000 r -> 011 11 (011)^(e+1) 011 C> r, and back *)
Lemma LP5r l e r : l <* <[0;1;1] {{C}}> [1;0;0;0;1] *> [0;0;1]^^e *> [0;0;0] *> r -->+
  l <* <[0;1;1;1;1] <* <[0;1;1]^^(S e) <* <[0;1;1] {{C}}> r.
Proof. es. Qed.

Lemma LP5l0 l e r : l <* <[0;1;1;1;1] <* <[0;1;1]^^(S e) <{{A}} [1;0;0] *> r -->+
  l <{{A}} [1;0;0;0;1] *> [0;0;1]^^(S e) *> [0;0;0] *> r.
Proof. es. Qed.

Lemma LP5l1 l e r : l <* <[0;1;1;1;1] <* <[0;1;1]^^(S e) <{{A}} [1;0;1;0;0;0] *> r -->+
  l <{{A}} [1;0;0;0;1] *> [0;0;1]^^(S (S e)) *> [0;0;0] *> r.
Proof. es. Qed.

(* LP6 (D6), right pass: builds the sub-hub 011 1 . 110 0 (011)^(e+1) C> r *)
Lemma LP6r l e r : l <* <[0;1;1] {{C}}> [1;0;1;0;1] *> [0;0;1]^^e *> [0;0;0] *> r -->+
  l <* <[0;1;1;1] <* <[1;1;0] <* [0] <* <[0;1;1]^^(S e) {{C}}> r.
Proof. es. Qed.

(* W10, the D6 exit: 011 E> 1 r -> <A 100 0 r *)
Lemma W10 l r : l <* <[0;1;1;1] <{{E}} r -->+ l <{{A}} [1;0;0;0] *> r.
Proof. es. Qed.

(* RP0 / RP1: the region pass (FractalBEC's RInc) *)
Lemma RP0 l n r : l <* [0] <* <[0;1;1]^^(S n) <{{A}} [1;0;0] *> r -->+
  l <* <[1;1;0] <* [0] <* <[0;1;1]^^(S n) {{C}}> r.
Proof. es. Qed.

Lemma RP1 l n r : l <* [0] <* <[0;1;1]^^(S n) <{{A}} [1;0;1;0;0;0] *> r -->+
  l <* <[1;1;0] <* [0] <* <[0;1;1]^^(S (S n)) {{C}}> r.
Proof. es. Qed.

(* Eats at b = 1 *)
Lemma E1r l a e r : l <* <[1;1;0]^^a <* [0] <* <[0;1;1] {{C}}> [0;0;1]^^(S e) *> [0;0;0] *> r -->+
  l <* <[1;1;0]^^(S (S a)) <* [0] <* <[0;1;1]^^(S e) {{C}}> r.
Proof. es. Qed.

Lemma E2l0 l a e r : l <* <[1;1;0]^^a <* [0] <* <[0;1;1;1;1;1] <* <[0;1;1]^^e <{{A}} [1;0;0] *> r -->+
  l <{{E}} [0;1] *> [0;0;1]^^a *> [0;0;0;1;1] *> [0;0;1]^^e *> [0;0;0] *> r.
Proof. es. Qed.

Lemma E2l1 l a e r : l <* <[1;1;0]^^a <* [0] <* <[0;1;1;1;1;1] <* <[0;1;1]^^e <{{A}} [1;0;1;0;0;0] *> r -->+
  l <{{E}} [0;1] *> [0;0;1]^^a *> [0;0;0;1;1] *> [0;0;1]^^(S e) *> [0;0;0] *> r.
Proof. es. Qed.

Lemma Et0 l a : l <* <[1;1;0]^^a <* [0] <* <[0;1;1] {{C}}> 0inf -->+
  l <{{E}} [0;1] *> [0;0;1]^^(S a) *> [0;0;0;1] *> 0inf.
Proof. es. Qed.

Lemma Et1 l a : l <* <[1;1;0]^^a <* [0] <* <[0;1;1] {{C}}> [1] *> 0inf -->+
  l <{{E}} [0;1] *> [0;0;1]^^a *> [0;0;0;0;1;0;0;1;0;0;0;1] *> 0inf.
Proof. es. Qed.

Lemma Et2 l a : l <* <[1;1;0]^^a <* [0] <* <[0;1;1] {{C}}> [0;1;0;0;0;1] *> 0inf -->+
  l <{{E}} [0;1] *> [0;0;1]^^a *> [0;0;0;1;0;0;0;0;1;0;0;0;1] *> 0inf.
Proof. es. Qed.

Lemma Et3 l a : l <* <[1;1;0]^^a <* [0] <* <[0;1;1] {{C}}> [1;1;0;0;0;1] *> 0inf -->+
  l <* <[1;1;0]^^(S a) <* [0] <* <[0;1;1] {{C}}> [0;0;1] *> 0inf.
Proof. es. Qed.

(* Restart from a pre-record (write-up 3.7, plus the step L' -> L) *)
Lemma Rst k r : const 0 <{{E}} [0;1] *> [0;0;1]^^k *> [0;0;0] *> r -->+
  const 0 <* <[1;1;0] <* [0] <* <[0;1;1]^^(S k) {{C}}> r.
Proof. rewrite (const_unfold _ S0) at 1. es. Qed.

(* LPT: the constant end words *)
Lemma LPT1 l : l <* <[0;1;1] {{C}}> [1] *> 0inf -->+ l <{{A}} [1;0;0;0;1;0;0;0;1] *> 0inf.
Proof. es. Qed.

Lemma LPT2 l : l <* <[0;1;1] {{C}}> [1;0;0;1;0;0;0;1] *> 0inf -->+
  l <{{A}} [1;0;0] *> [0;1;0;0;1;0;0;0;0;1;0;0;1;0;0;0;1] *> 0inf.
Proof. es. Qed.

Lemma LPT3 l : l <* <[0;1;1] {{C}}> [1;0;1;1;0;0;0;1] *> 0inf -->+
  l <{{A}} [1;0;0] *> [0;0;0;1;0;0;0;0;1;0;0;0;1] *> 0inf.
Proof. es. Qed.

Lemma LPT4 l : l <* <[0;1;1] {{C}}> [1;0;0;0;0;1;0;0;0;1] *> 0inf -->+
  l <{{A}} [1;0;0] *> [0;1;0;0;0;0;1;0;0;1;0;0;0;1] *> 0inf.
Proof. es. Qed.

Lemma LPT5 l : l <* <[0;1;1] {{C}}> [1;0;0;1;0;0;0;0;1;0;0;0;1] *> 0inf -->+
  l <{{A}} [1;0;0] *> [0;1;0;0;1;0;0;0;1;0;0;0;0;1;0;0;0;1] *> 0inf.
Proof. es. Qed.

Lemma LPT6 l : l <* <[0;1;1] {{C}}> [1;0;0;1;0;0;1;0;0;0;1] *> 0inf -->+
  l <{{A}} [1;0;0] *> [0;1;0;0;1;0;0;1;0;0;0;1;0;0;0;0;1;0;0;0;1] *> 0inf.
Proof. es. Qed.

Lemma z3 : [0;0;0] *> const 0 = const 0.
Proof. cbn. rewrite <- !const_unfold. reflexivity. Qed.

(* ===================================================================== *)
(* Section 2. Words, the local pass LP and the epoch map Phi.             *)
(* ===================================================================== *)

(* blk d e w = d01 (001)^e 000 w;  p11 x w = 11 (001)^x 000 w;  p01 x w = 01 (001)^x 000 w;
   p00 w = 00 w;  p10 w = 10 w;  tails t0 = '', t1 = 1, t2 = 010001, t3 = 110001. *)
Inductive word : Type :=
| t0 | t1 | t2 | t3
| blk (d : bool) (e : nat) (w : word)
| p11 (x : nat) (w : word)
| p01 (x : nat) (w : word)
| p00 (w : word)
| p10 (w : word).

Definition dsym (d : bool) : Sym := if d then S1 else S0.

Fixpoint enc (w : word) : side :=
  match w with
  | t0 => const 0
  | t1 => [1] *> const 0
  | t2 => [0;1;0;0;0;1] *> const 0
  | t3 => [1;1;0;0;0;1] *> const 0
  | blk d e w => [dsym d; 0; 1] *> [0;0;1]^^e *> [0;0;0] *> enc w
  | p11 x w => [1;1] *> [0;0;1]^^x *> [0;0;0] *> enc w
  | p01 x w => [0;1] *> [0;0;1]^^x *> [0;0;0] *> enc w
  | p00 w => [0;0] *> enc w
  | p10 w => [1;0] *> enc w
  end.

Definition addb (e : nat) (d : bool) : nat := if d then S e else e.

(* LP w w' d: the local pass maps w to w', d = true if it absorbs one 011 block.
   Phi a b w k y: the epoch map from the hub (110)^a 0 (011)^b C> w to the pre-record
   E> . 01 (001)^k 000 y (write-up 3.8). *)
Inductive LP : word -> word -> bool -> Prop :=
| LP_a e w : LP (blk false e w) (blk true e w) false
| LP_b e w w' d : LP w w' d -> LP (blk true e w) (blk false (addb e d) w') false
| LP_t0 : LP t0 t1 false
| LP_t1 : LP t1 t2 false
| LP_t2 : LP t2 t3 false
| LP_t3 : LP t3 (blk false 0 t0) true
| LP_11S x w : LP (p11 (S x) w) (p01 x w) true
| LP_110 w : LP (p11 0 w) (p00 w) true
| LP_01 x w : LP (p01 x w) (p11 x w) false
| LP_00 w : LP (p00 w) (p10 w) false
| LP_5 e w w' d : LP w w' d -> LP (p10 (blk false e w)) (p01 (S (addb e d)) w') false
| LP_6 e w k y : Phi 1 (S e) w k y -> LP (p10 (blk true e w)) (blk false k y) false
| LP_T2 : LP (p10 t2) (p01 1 (p01 1 t1)) false
| LP_T3 : LP (p10 t3) (p00 (p01 0 t2)) false
| LP_T4 : LP (p10 (p00 t2)) (p01 0 (p01 1 t1)) false
| LP_T5 : LP (p10 (p01 0 t2)) (p01 1 (p10 (p00 t2))) false
| LP_T6 : LP (p10 (p01 1 t1)) (p01 2 (p10 (p00 t2))) false
| LP_eq w1 w2 w' d : enc w1 = enc w2 -> LP w2 w' d -> LP w1 w' d
with Phi : nat -> nat -> word -> nat -> word -> Prop :=
| Phi_B a b w w' d k y : LP w w' d -> Phi (S a) (addb (S b) d) w' k y -> Phi a (S (S b)) w k y
| Phi_E1 a e w k y : Phi (S (S a)) (S e) w k y -> Phi a 1 (blk false e w) k y
| Phi_E2 a e w w' d : LP w w' d -> Phi a 1 (blk true e w) a (p11 (addb e d) w')
| Phi_E0 a : Phi a 1 t0 (S a) t1
| Phi_Et1 a : Phi a 1 t1 a (p01 1 t1)
| Phi_Et2 a : Phi a 1 t2 a (p10 (p00 t2))
| Phi_Et3 a k y : Phi (S a) 1 (blk false 0 t0) k y -> Phi a 1 t3 k y
| Phi_eq a b w1 w2 k y : enc w1 = enc w2 -> Phi a b w2 k y -> Phi a b w1 k y.

Scheme LP_mind := Induction for LP Sort Prop
with Phi_mind := Induction for Phi Sort Prop.
Combined Scheme LP_Phi_mind from LP_mind, Phi_mind.

Definition outp (d : bool) (r : side) : side :=
  if d then [1;0;1;0;0;0] *> r else [1;0;0] *> r.

Definition LPspec (w w' : word) (d : bool) : Prop :=
  forall l, l <* <[0;1;1] {{C}}> enc w -->+ l <{{A}} outp d (enc w').

Definition Phispec (a b : nat) (w : word) (k : nat) (y : word) : Prop :=
  forall l, l <* <[1;1;0]^^a <* [0] <* <[0;1;1]^^b {{C}}> enc w -->+
            l <{{E}} [0;1] *> [0;0;1]^^k *> [0;0;0] *> enc y.

Lemma enc_a0 : enc (blk false 0 t0) = [0;0;1] *> const 0.
Proof. cbn [enc]. rewrite z3. reflexivity. Qed.

(* ===================================================================== *)
(* Section 3. Soundness: every LP / Phi derivation is a TM run.           *)
(* ===================================================================== *)

Theorem sound :
  (forall w w' d, LP w w' d -> LPspec w w' d) /\
  (forall a b w k y, Phi a b w k y -> Phispec a b w k y).
Proof.
  apply LP_Phi_mind; unfold LPspec, Phispec.
  - (* LP_a *) intros e w l. exact (LP0 l ([0;1] *> [0;0;1]^^e *> [0;0;0] *> enc w)).
  - (* LP_b *) intros e w w' d H IH l. destruct d.
    + eapply progress_trans. { exact (LPCr l e (enc w)). }
      eapply progress_trans. { exact (IH (l <* <[0;1;1;1;1;1] <* <[0;1;1]^^e)). }
      exact (LPCl1 l e (enc w')).
    + eapply progress_trans. { exact (LPCr l e (enc w)). }
      eapply progress_trans. { exact (IH (l <* <[0;1;1;1;1;1] <* <[0;1;1]^^e)). }
      exact (LPCl0 l e (enc w')).
  - (* LP_t0 *) intros l. exact (LP0z l).
  - (* LP_t1 *) intros l. exact (LPT1 l).
  - (* LP_t2 *) intros l. exact (LP0 l ([1;0;0;0;1] *> const 0)).
  - (* LP_t3 *) intros l. unfold outp. rewrite enc_a0. exact (LP11 l ([0;0;1] *> const 0)).
  - (* LP_11S *) intros x w l. exact (LP11 l ([0;1] *> [0;0;1]^^x *> [0;0;0] *> enc w)).
  - (* LP_110 *) intros w l. exact (LP11 l ([0;0] *> enc w)).
  - (* LP_01 *) intros x w l. exact (LP0 l ([1] *> [0;0;1]^^x *> [0;0;0] *> enc w)).
  - (* LP_00 *) intros w l. exact (LP0 l ([0] *> enc w)).
  - (* LP_5 *) intros e w w' d H IH l. destruct d.
    + eapply progress_trans. { exact (LP5r l e (enc w)). }
      eapply progress_trans. { exact (IH (l <* <[0;1;1;1;1] <* <[0;1;1]^^(S e))). }
      exact (LP5l1 l e (enc w')).
    + eapply progress_trans. { exact (LP5r l e (enc w)). }
      eapply progress_trans. { exact (IH (l <* <[0;1;1;1;1] <* <[0;1;1]^^(S e))). }
      exact (LP5l0 l e (enc w')).
  - (* LP_6 *) intros e w k y H IH l.
    eapply progress_trans. { exact (LP6r l e (enc w)). }
    eapply progress_trans. { exact (IH (l <* <[0;1;1;1])). }
    exact (W10 l ([0;1] *> [0;0;1]^^k *> [0;0;0] *> enc y)).
  - (* LP_T2 *) intros l. exact (LPT2 l).
  - (* LP_T3 *) intros l. exact (LPT3 l).
  - (* LP_T4 *) intros l. exact (LPT4 l).
  - (* LP_T5 *) intros l. exact (LPT5 l).
  - (* LP_T6 *) intros l. exact (LPT6 l).
  - (* LP_eq *) intros w1 w2 w' d E H IH l. rewrite E. apply IH.
  - (* Phi_B *) intros a b w w' d k y H IH H2 IH2 l. destruct d.
    + eapply progress_trans. { exact (IH (l <* <[1;1;0]^^a <* [0] <* <[0;1;1]^^(S b))). }
      eapply progress_trans. { exact (RP1 (l <* <[1;1;0]^^a) b (enc w')). }
      exact (IH2 l).
    + eapply progress_trans. { exact (IH (l <* <[1;1;0]^^a <* [0] <* <[0;1;1]^^(S b))). }
      eapply progress_trans. { exact (RP0 (l <* <[1;1;0]^^a) b (enc w')). }
      exact (IH2 l).
  - (* Phi_E1 *) intros a e w k y H IH l.
    eapply progress_trans. { exact (E1r l a e (enc w)). }
    exact (IH l).
  - (* Phi_E2 *) intros a e w w' d H IH l. destruct d.
    + eapply progress_trans. { exact (LPCr (l <* <[1;1;0]^^a <* [0]) e (enc w)). }
      eapply progress_trans. { exact (IH (l <* <[1;1;0]^^a <* [0] <* <[0;1;1;1;1;1] <* <[0;1;1]^^e)). }
      exact (E2l1 l a e (enc w')).
    + eapply progress_trans. { exact (LPCr (l <* <[1;1;0]^^a <* [0]) e (enc w)). }
      eapply progress_trans. { exact (IH (l <* <[1;1;0]^^a <* [0] <* <[0;1;1;1;1;1] <* <[0;1;1]^^e)). }
      exact (E2l0 l a e (enc w')).
  - (* Phi_E0 *) intros a l. exact (Et0 l a).
  - (* Phi_Et1 *) intros a l. exact (Et1 l a).
  - (* Phi_Et2 *) intros a l. exact (Et2 l a).
  - (* Phi_Et3 *) intros a k y H IH l.
    eapply progress_trans. { exact (Et3 l a). }
    specialize (IH l). rewrite enc_a0 in IH. exact IH.
  - (* Phi_eq *) intros a b w1 w2 k y E H IH l. rewrite E. apply IH.
Qed.

(* ===================================================================== *)
(* Section 4. Epochs and the start.                                       *)
(* ===================================================================== *)

Definition K (N : nat) (y : word) : Q * tape :=
  const 0 <* <[1;1;0] <* [0] <* <[0;1;1]^^N {{C}}> enc y.

Lemma epoch_tm N y k y' : Phi 1 N y k y' -> K N y -->+ K (S k) y'.
Proof.
  intros H. eapply progress_trans.
  - exact (proj2 sound _ _ _ _ _ H (const 0)).
  - apply Rst.
Qed.

(* The blank tape reaches L(7, 000 010001) at step 304, then the restart gives K(1,8,t2). *)
Lemma init : c0 -->* K 8 t2.
Proof. unfold K. cbn. solve_init. Qed.

(* ===================================================================== *)
(* Section 5. A computable model (fuel), sound for LP / Phi.              *)
(* ===================================================================== *)

Fixpoint lpf (n : nat) (w : word) {struct n} : option (word * bool) :=
  match n with
  | O => None
  | S n' =>
    match w with
    | t0 => Some (t1, false)
    | t1 => Some (t2, false)
    | t2 => Some (t3, false)
    | t3 => Some (blk false 0 t0, true)
    | blk false e w => Some (blk true e w, false)
    | blk true e w =>
        match lpf n' w with Some (w', d) => Some (blk false (addb e d) w', false) | None => None end
    | p11 (S x) w => Some (p01 x w, true)
    | p11 O w => Some (p00 w, true)
    | p01 x w => Some (p11 x w, false)
    | p00 w => Some (p10 w, false)
    | p10 w =>
        match w with
        | t0 => Some (t2, false)
        | t1 => Some (blk false 0 t1, false)
        | t2 => Some (p01 1 (p01 1 t1), false)
        | t3 => Some (p00 (p01 0 t2), false)
        | blk false e w =>
            match lpf n' w with Some (w', d) => Some (p01 (S (addb e d)) w', false) | None => None end
        | blk true e w =>
            match phif n' 1 (S e) w with Some (k, y) => Some (blk false k y, false) | None => None end
        | p00 t0 => Some (t2, false)
        | p00 t1 => Some (p01 1 t1, false)
        | p00 t2 => Some (p01 0 (p01 1 t1), false)
        | p01 0 t2 => Some (p01 1 (p10 (p00 t2)), false)
        | p01 1 t1 => Some (p01 2 (p10 (p00 t2)), false)
        | p10 (p00 t2) => Some (blk false 0 t3, false)
        | _ => None
        end
    end
  end
with phif (n : nat) (a b : nat) (w : word) {struct n} : option (nat * word) :=
  match n with
  | O => None
  | S n' =>
    match b with
    | O => None
    | S O =>
      match w with
      | blk false e w => phif n' (S (S a)) (S e) w
      | blk true e w =>
          match lpf n' w with Some (w', d) => Some (a, p11 (addb e d) w') | None => None end
      | t0 => Some (S a, t1)
      | t1 => Some (a, p01 1 t1)
      | t2 => Some (a, p10 (p00 t2))
      | t3 => phif n' (S a) 1 (blk false 0 t0)
      | p10 t0 => Some (a, p01 1 t1)
      | p10 t1 => Some (a, p11 0 t1)
      | p00 t0 => Some (S a, t1)
      | p00 t1 => phif n' (S (S a)) 1 t0
      | _ => None
      end
    | S (S b') =>
      match lpf n' w with
      | Some (w', d) => phif n' (S a) (addb (S b') d) w'
      | None => None
      end
    end
  end.

Lemma enc_p10t0 : enc (p10 t0) = enc t1.
Proof. cbn. rewrite <- const_unfold. reflexivity. Qed.

Lemma enc_p10t1 : enc (p10 t1) = enc (blk true 0 t0).
Proof. cbn [enc lpow dsym]. rewrite z3. reflexivity. Qed.

Lemma enc_p00t0 : enc (p00 t0) = enc t0.
Proof. cbn. rewrite <- !const_unfold. reflexivity. Qed.

Lemma enc_p00t1 : enc (p00 t1) = enc (blk false 0 t0).
Proof. cbn [enc lpow dsym]. rewrite z3. reflexivity. Qed.

Lemma enc_p10p00t0 : enc (p10 (p00 t0)) = enc t1.
Proof. cbn. rewrite <- !const_unfold. reflexivity. Qed.

Lemma enc_p10p00t1 : enc (p10 (p00 t1)) = enc (p10 (blk false 0 t0)).
Proof. cbn [enc lpow dsym]. rewrite z3. reflexivity. Qed.

Lemma model_sound n :
  (forall w w' d, lpf n w = Some (w', d) -> LP w w' d) /\
  (forall a b w k y, phif n a b w = Some (k, y) -> Phi a b w k y).
Proof.
  induction n as [|n [IHl IHp]]; [split; intros; discriminate|].
  split.
  - intros w w' d H. cbn [lpf] in H.
    destruct w as [| | | |[|] e w|[|x] w|x w|w|w]; try (inversion H; subst; constructor; fail).
    + destruct (lpf n w) as [[w1 d1]|] eqn:E; inversion H; subst. constructor. apply IHl, E.
    + destruct w as [| | | |[|] e w|[|x] w|x w|w|w]; try discriminate.
      * inversion H; subst. eapply LP_eq; [apply enc_p10t0 | constructor].
      * inversion H; subst. eapply LP_eq; [apply enc_p10t1 | ]. apply (LP_b 0 t0 t1 false). constructor.
      * inversion H; subst. constructor.
      * inversion H; subst. constructor.
      * destruct (phif n 1 (S e) w) as [[k y]|] eqn:E; inversion H; subst. constructor. apply IHp, E.
      * destruct (lpf n w) as [[w1 d1]|] eqn:E; inversion H; subst. constructor. apply IHl, E.
      * destruct x as [|[|x]]; try discriminate; destruct w; try discriminate;
          inversion H; subst; constructor.
      * destruct w; try discriminate; inversion H; subst.
        -- eapply LP_eq; [apply enc_p10p00t0 | constructor].
        -- eapply LP_eq; [apply enc_p10p00t1 | ]. apply (LP_5 0 t0 t1 false). constructor.
        -- constructor.
      * destruct w; try discriminate. destruct w; try discriminate. inversion H; subst.
        apply (LP_eq _ (blk true 0 t2)); [reflexivity | ]. apply (LP_b 0 t2 t3 false). constructor.
  - intros a b w k y H. cbn [phif] in H.
    destruct b as [|[|b]]; try discriminate.
    + destruct w as [| | | |[|] e w|[|x] w|x w|w|w]; try discriminate.
      * inversion H; subst. constructor.
      * inversion H; subst. constructor.
      * inversion H; subst. constructor.
      * constructor. apply IHp, H.
      * destruct (lpf n w) as [[w1 d1]|] eqn:E; inversion H; subst. constructor. apply IHl, E.
      * constructor. apply IHp, H.
      * destruct w; try discriminate; inversion H; subst.
        -- eapply Phi_eq; [apply enc_p00t0 | constructor].
        -- eapply Phi_eq; [apply enc_p00t1 | ]. constructor. apply IHp, H.
      * destruct w; try discriminate; inversion H; subst.
        -- eapply Phi_eq; [apply enc_p10t0 | constructor].
        -- eapply Phi_eq; [apply enc_p10t1 | ]. apply (Phi_E2 _ 0 t0 t1 false). constructor.
    + destruct (lpf n w) as [[w1 d1]|] eqn:E; try discriminate.
      eapply Phi_B; [apply IHl, E | apply IHp, H].
Qed.


(* ===================================================================== *)
(* Section 6. Counter words G, their value, and the counting phase.        *)
(* ===================================================================== *)

Open Scope nat_scope.

Definition tl_of (s : nat) : word :=
  match s with O => t0 | 1 => t1 | 2 => t2 | _ => t3 end.

Fixpoint gw (bs : list (bool * nat)) (s : nat) : word :=
  match bs with [] => tl_of s | (d, e) :: bs => blk d e (gw bs s) end.

Fixpoint ginc (bs : list (bool * nat)) (s : nat) : list (bool * nat) * nat * bool :=
  match bs with
  | [] => match s with O => ([], 1, false) | 1 => ([], 2, false) | 2 => ([], 3, false)
          | _ => ([(false, 0)], O, true) end
  | (false, e) :: bs => ((true, e) :: bs, s, false)
  | (true, e) :: bs => let '(bs', s', d) := ginc bs s in ((false, addb e d) :: bs', s', false)
  end.

Fixpoint gval (bs : list (bool * nat)) (s : nat) : nat :=
  match bs with [] => 4 + s | (d, _) :: bs => (if d then 1 else 0) + 2 * gval bs s end.

Fixpoint gsum (bs : list (bool * nat)) : nat :=
  match bs with [] => O | (_, e) :: bs => e + gsum bs end.

Lemma ginc_LP bs s : s <= 3 -> forall bs' s' d, ginc bs s = (bs', s', d) -> LP (gw bs s) (gw bs' s') d.
Proof.
  intros Hs. induction bs as [|[[|] e] bs IH]; intros bs' s' d E; cbn in E.
  - destruct s as [|[|[|[|s]]]]; inversion E; subst; cbn; try constructor; lia.
  - destruct (ginc bs s) as [[b1 s1] d1] eqn:E1. inversion E; subst. cbn. constructor. apply IH; reflexivity.
  - inversion E; subst. constructor.
Qed.

Lemma ginc_val bs s : s <= 3 -> forall bs' s' d, ginc bs s = (bs', s', d) ->
  gval bs' s' = S (gval bs s) /\ s' <= 3 /\
  gsum bs' + length bs + (if d then 1 else 0) = gsum bs + length bs' /\
  (d = true -> bs = []) /\ length bs <= length bs'.
Proof.
  intros Hs. induction bs as [|[[|] e] bs IH]; intros bs' s' d E; cbn in E.
  - destruct s as [|[|[|[|s]]]]; inversion E; subst; cbn; repeat split; try lia; auto.
  - destruct (ginc bs s) as [[b1 s1] d1] eqn:E1. inversion E; subst.
    destruct (IH _ _ _ eq_refl) as (H1 & H2 & H3 & H4 & H5). cbn.
    destruct d1; cbn [addb]; [specialize (H4 eq_refl); subst bs; cbn in *|]; repeat split; try lia; discriminate.
  - inversion E; subst. cbn. repeat split; try lia; discriminate.
Qed.

Lemma gval_ge bs s : 4 <= gval bs s.
Proof. induction bs as [|[d e] bs IH]; cbn; lia. Qed.

Lemma gval_len bs s : length bs <= gval bs s.
Proof. induction bs as [|[d e] bs IH]; cbn; [lia|]. pose proof (gval_ge bs s). lia. Qed.

(* Psi = value + budget + sum of exponents - number of blocks: no bounce raises it, every
   E1g lowers it by value - 1 >= 3. So every counting phase ends (gcount below; cf. the
   write-up's D.0). *)
Definition Psi (bs : list (bool * nat)) (s b : nat) : nat := gval bs s + b + gsum bs - length bs.

Import ListNotations.

(* ===================================================================== *)
(* Section 7. The epoch map on counter words, multi-step LP, digestion.   *)
(* ===================================================================== *)

Definition blks := list (bool * nat).
Definition b2n (d : bool) : nat := if d then 1 else 0.
Lemma addb_b2n e d : addb e d = e + b2n d.
Proof. destruct d; cbn; lia. Qed.

Inductive GRes : Type := RE2 (k x : nat) (bs : blks) (s : nat) | RSp (k : nat) (y : word).
Definition rk (r : GRes) : nat := match r with RE2 k _ _ _ => k | RSp k _ => k end.
Definition ry (r : GRes) : word := match r with RE2 _ x bs s => p11 x (gw bs s) | RSp _ y => y end.

(* GPhi a b bs s r: the epoch map Phi on a counter word, bounce by bounce (write-up 3.6, 3.8). *)
Inductive GPhi : nat -> nat -> blks -> nat -> GRes -> Prop :=
| GB a b bs s bs' s' d r : ginc bs s = (bs', s', d) -> GPhi (S a) (addb (S b) d) bs' s' r ->
    GPhi a (S (S b)) bs s r
| GE1 a e bs s r : GPhi (S (S a)) (S e) bs s r -> GPhi a 1 ((false, e) :: bs) s r
| GE2 a e bs s bs' s' d : ginc bs s = (bs', s', d) ->
    GPhi a 1 ((true, e) :: bs) s (RE2 a (addb e d) bs' s')
| GE0 a : GPhi a 1 [] 0 (RSp (S a) t1)
| GEt1 a : GPhi a 1 [] 1 (RSp a (p01 1 t1))
| GEt2 a : GPhi a 1 [] 2 (RSp a (p10 (p00 t2)))
| GEt3 a r : GPhi (S a) 1 [(false, 0)] 0 r -> GPhi a 1 [] 3 r.

Lemma ginc_s3 bs s bs' s' d : s <= 3 -> ginc bs s = (bs', s', d) -> s' <= 3.
Proof. intros Hs E. destruct (ginc_val bs s Hs _ _ _ E) as (_ & H & _). exact H. Qed.

Lemma GPhi_sound a b bs s r : GPhi a b bs s r -> s <= 3 -> Phi a b (gw bs s) (rk r) (ry r).
Proof.
  induction 1; intros Hs; cbn [gw rk ry tl_of] in *.
  - eapply Phi_B. { apply (ginc_LP bs s Hs _ _ _ H). } apply IHGPhi. eapply ginc_s3; eauto.
  - apply Phi_E1. apply IHGPhi. exact Hs.
  - apply Phi_E2. apply (ginc_LP bs s Hs _ _ _ H).
  - apply Phi_E0.
  - apply Phi_Et1.
  - apply Phi_Et2.
  - apply Phi_Et3. apply IHGPhi. lia.
Qed.

Lemma GPhi_s3 a b bs s r : GPhi a b bs s r -> s <= 3 ->
  match r with RE2 _ _ _ s2 => s2 <= 3 | RSp _ y => y = t1 \/ y = p01 1 t1 \/ y = p10 (p00 t2) end.
Proof.
  induction 1; intros Hs; auto; try (apply IHGPhi; first [lia | eapply ginc_s3; eauto]).
  eapply ginc_s3; eauto.
Qed.

Lemma GPhi_rk a b bs s r : GPhi a b bs s r -> a + b <= S (rk r).
Proof. induction 1; try destruct d; cbn [rk addb] in *; lia. Qed.

Lemma gcount : forall P bs s a b, s <= 3 -> 1 <= b -> Psi bs s b <= P -> exists r, GPhi a b bs s r.
Proof.
  induction P as [P IHP] using lt_wf_ind.
  intros bs s a b. revert bs s a. induction b as [b IHb] using lt_wf_ind. intros bs s a Hs Hb HP.
  destruct b as [|[|b]]; [lia| |].
  - destruct bs as [|[[|] e] bs].
    + destruct s as [|[|[|[|s]]]]; try lia.
      * eexists. apply GE0.
      * eexists. apply GEt1.
      * eexists. apply GEt2.
      * eexists. apply GEt3. apply (GE1 _ 0 []). apply GE0.
    + destruct (ginc bs s) as [[b1 s1] d1] eqn:E1. eexists. eapply GE2. exact E1.
    + assert (Hlt : Psi bs s (S e) < P).
      { unfold Psi in *. cbn [gval gsum length] in HP. pose proof (gval_ge bs s). pose proof (gval_len bs s). lia. }
      destruct (IHP _ Hlt bs s (S (S a)) (S e) Hs ltac:(lia) (le_n _)) as (r & H).
      exists r. apply GE1, H.
  - destruct (ginc bs s) as [[b1 s1] d1] eqn:E1.
    destruct (ginc_val bs s Hs _ _ _ E1) as (V1 & S1 & M1 & D1 & L1).
    destruct d1.
    + specialize (D1 eq_refl). subst bs. cbn in E1.
      destruct s as [|[|[|[|s]]]]; inversion E1; subst; try lia.
      assert (Hlt : S b < S (S b)) by lia.
      destruct (IHb _ Hlt [(true, 0)] 0 (S (S a)) ltac:(lia) ltac:(lia)) as (r & H).
      { unfold Psi in *. cbn in HP |- *. lia. }
      exists r. eapply GB. { exact E1. }
      cbn [addb]. eapply GB. { reflexivity. } exact H.
    + assert (Hlt : S b < S (S b)) by lia.
      destruct (IHb _ Hlt b1 s1 (S a) S1 ltac:(lia)) as (r & H).
      { unfold Psi in *. lia. }
      exists r. eapply GB. { exact E1. } exact H.
Qed.

(* Multi-step local pass: n LP steps, c absorptions. *)
Inductive LPs : word -> word -> nat -> nat -> Prop :=
| LPs_eq w w' : enc w = enc w' -> LPs w w' 0 0
| LPs_step w w1 w2 d n c : LP w w1 d -> LPs w1 w2 n c -> LPs w w2 (S n) (c + b2n d).

Lemma LPs_step' w w1 w2 d n c c' : LP w w1 d -> LPs w1 w2 n c -> c' = c + b2n d -> LPs w w2 (S n) c'.
Proof. intros H1 H2 ->. econstructor; eauto. Qed.

Lemma LPs_eql w0 w1 w2 n c : enc w0 = enc w1 -> LPs w1 w2 n c -> LPs w0 w2 n c.
Proof.
  intros E H. inversion H; subst.
  - apply LPs_eq. congruence.
  - eapply LPs_step; [apply (LP_eq _ _ _ _ E); eassumption | eassumption].
Qed.

Lemma LPs_trans w1 w2 w3 n c n' c' : LPs w1 w2 n c -> LPs w2 w3 n' c' -> LPs w1 w3 (n + n') (c + c').
Proof.
  intros H. revert n' c' w3. induction H; intros n' c' w3 H'.
  - cbn. eapply LPs_eql; eassumption.
  - eapply LPs_step'; [eassumption | apply IHLPs, H' | ]. destruct d; cbn; lia.
Qed.

Lemma LPs_cn w w' n c : LPs w w' n c -> c <= n.
Proof. induction 1; [lia | destruct d; cbn; lia]. Qed.

Lemma LPs_hub w w' n c : LPs w w' n c -> forall a B k y, n + 2 <= B + c ->
  Phi (a + n) (B + c - n) w' k y -> Phi a B w k y.
Proof.
  induction 1 as [w w' E | w w1 w2 d n c H1 H2 IH]; intros a B k y Hb HP.
  - rewrite Nat.add_0_r in HP. replace (B + 0 - 0) with B in HP by lia. eapply Phi_eq; eassumption.
  - pose proof (LPs_cn _ _ _ _ H2) as Hc.
    destruct B as [|[|B]]; [destruct d; cbn in Hb; lia | destruct d; cbn in Hb; lia |].
    eapply Phi_B; [exact H1|]. apply IH.
    + rewrite addb_b2n. destruct d; unfold b2n in *; lia.
    + rewrite addb_b2n. replace (S a + n) with (a + S n) by lia.
      replace (S B + b2n d + c - n) with (S (S B) + (c + b2n d) - S n) by (destruct d; unfold b2n; lia).
      exact HP.
Qed.

Lemma LPs_nest y y' n c : LPs y y' n c -> forall k, LPs (blk false k y) (blk false (k + c) y') (2 * n) 0.
Proof.
  induction 1 as [y y' E | y y1 y2 d n c H1 H2 IH]; intros k.
  - rewrite Nat.add_0_r. apply LPs_eq. cbn [enc]. rewrite E. reflexivity.
  - replace (2 * S n) with (S (S (2 * n))) by lia.
    replace (k + (c + b2n d)) with (addb k d + c) by (rewrite addb_b2n; lia).
    eapply LPs_step'; [apply LP_a | eapply LPs_step'; [apply (LP_b k y y1 d H1) | apply IH | reflexivity] | reflexivity].
Qed.

(* The end words of a digestion (the end words of write-up 3.4), as explicit finite chains. *)
Inductive DigE : word -> nat -> nat -> blks -> nat -> Prop :=
| DE0 : DigE (p10 t0) 0 0 [] 1
| DE1 : DigE (p10 t1) 0 0 [(true, 0)] 0
| DE2 : DigE (p10 t2) 13 5 [(false, 0)] 2
| DE3 : DigE (p10 t3) 7 2 [(false, 0)] 2
| DEs0 : DigE t1 0 0 [] 1
| DEs1 : DigE (p01 1 t1) 2 1 [] 2
| DEs2 : DigE (p10 (p00 t2)) 11 4 [(false, 0)] 2.

Ltac lps := first [ apply LPs_eq; first [reflexivity | apply enc_p10t0 | apply enc_p10t1]
                  | eapply LPs_step'; [ constructor | lps | reflexivity ] ].

Lemma DigE_sound y n c bs s : DigE y n c bs s -> LPs y (gw bs s) n c.
Proof. destruct 1; cbn [gw tl_of]; lps. Qed.

Lemma DigE_props y n c bs s : DigE y n c bs s ->
  n <= 13 /\ c <= 5 /\ length bs <= 1 /\ s <= 3 /\ Forall (fun e => e = 0) (map snd bs).
Proof. destruct 1; cbn; repeat split; auto; lia. Qed.

(* Digestion of a residue: DigP x bs s = digestion of 11 (001)^x 000 W, DigT = of 10 W, with W the
   counter word gw bs s. n LP steps (own level), c absorptions, result gw bsp sp. A b-block runs a
   sub-epoch (GPhi) and the next level is nested inside the new block (LPs_nest). *)
Inductive DigP : nat -> blks -> nat -> nat -> nat -> blks -> nat -> Prop :=
| DP x bs s n c bsp sp : DigT bs s n c bsp sp -> DigP x bs s (2 * x + 2 + n) (S x + c) bsp sp
with DigT : blks -> nat -> nat -> nat -> blks -> nat -> Prop :=
| DTa e bs s bs' s' d n c bsp sp : ginc bs s = (bs', s', d) ->
    DigP (S (addb e d)) bs' s' n c bsp sp -> DigT ((false, e) :: bs) s (S (S n)) c bsp sp
| DTb e bs s k x bs2 s2 n c bsp sp : GPhi 1 (S e) bs s (RE2 k x bs2 s2) ->
    DigP x bs2 s2 n c bsp sp -> DigT ((true, e) :: bs) s (S (2 * n)) 0 ((false, k + c) :: bsp) sp
| DTs e bs s k y n c bsp sp : GPhi 1 (S e) bs s (RSp k y) ->
    DigE y n c bsp sp -> DigT ((true, e) :: bs) s (S (2 * n)) 0 ((false, k + c) :: bsp) sp
| DTt s n c bsp sp : DigE (p10 (tl_of s)) n c bsp sp -> DigT [] s n c bsp sp.

Scheme DigP_mind := Induction for DigP Sort Prop
with DigT_mind := Induction for DigT Sort Prop.
Combined Scheme Dig_mind from DigP_mind, DigT_mind.

Lemma prefix_LPs x w : LPs (p11 x w) (p10 w) (2 * x + 2) (S x).
Proof.
  induction x as [|x IH].
  - eapply LPs_step'; [apply LP_110 | eapply LPs_step'; [apply LP_00 | apply LPs_eq; reflexivity | reflexivity] | reflexivity].
  - replace (2 * S x + 2) with (S (S (2 * x + 2))) by lia.
    eapply LPs_step'; [apply LP_11S | eapply LPs_step'; [apply LP_01 | exact IH | reflexivity] | cbn; lia].
Qed.

Lemma Dig_sound :
  (forall x bs s n c bsp sp, DigP x bs s n c bsp sp -> s <= 3 -> LPs (p11 x (gw bs s)) (gw bsp sp) n c) /\
  (forall bs s n c bsp sp, DigT bs s n c bsp sp -> s <= 3 -> LPs (p10 (gw bs s)) (gw bsp sp) n c).
Proof.
  apply Dig_mind.
  - intros x bs s n c bsp sp H IH Hs.
    exact (LPs_trans _ _ _ _ _ _ _ (prefix_LPs x (gw bs s)) (IH Hs)).
  - intros e bs s bs' s' d n c bsp sp E H IH Hs. cbn [gw].
    eapply LPs_step'; [apply LP_5, (ginc_LP bs s Hs _ _ _ E) |
      eapply LPs_step'; [apply LP_01 | apply IH; eapply ginc_s3; eauto | reflexivity] | cbn; lia].
  - intros e bs s k x bs2 s2 n c bsp sp HG H IH Hs. cbn [gw].
    pose proof (GPhi_s3 _ _ _ _ _ HG Hs) as Hs2. cbn in Hs2.
    eapply LPs_step'; [apply LP_6; exact (GPhi_sound _ _ _ _ _ HG Hs) |
      exact (LPs_nest _ _ _ _ (IH Hs2) k) | reflexivity].
  - intros e bs s k y n c bsp sp HG H Hs. cbn [gw].
    eapply LPs_step'; [apply LP_6; exact (GPhi_sound _ _ _ _ _ HG Hs) |
      exact (LPs_nest _ _ _ _ (DigE_sound _ _ _ _ _ H) k) | reflexivity].
  - intros s n c bsp sp H Hs. cbn [gw]. exact (DigE_sound _ _ _ _ _ H).
Qed.

Lemma Dig_sp :
  (forall x bs s n c bsp sp, DigP x bs s n c bsp sp -> sp <= 3) /\
  (forall bs s n c bsp sp, DigT bs s n c bsp sp -> sp <= 3).
Proof.
  apply Dig_mind; intros; auto; eapply DigE_props; eassumption.
Qed.

(* One epoch from an ordinary residue: digestion (n bounces), then counting (GPhi). *)
Lemma epoch_ord N x bs s n c bsp sp r : s <= 3 -> DigP x bs s n c bsp sp -> n + 2 <= N ->
  GPhi (1 + n) (N + c - n) bsp sp r -> Phi 1 N (p11 x (gw bs s)) (rk r) (ry r).
Proof.
  intros Hs HD Hn HG.
  apply (LPs_hub _ _ _ _ (proj1 Dig_sound _ _ _ _ _ _ _ HD Hs) 1 N); [lia|].
  apply GPhi_sound; [exact HG | exact (proj1 Dig_sp _ _ _ _ _ _ _ HD)].
Qed.

Lemma epoch_spec N y n c bsp sp r : DigE y n c bsp sp -> n + 2 <= N ->
  GPhi (1 + n) (N + c - n) bsp sp r -> Phi 1 N y (rk r) (ry r).
Proof.
  intros HD Hn HG.
  apply (LPs_hub _ _ _ _ (DigE_sound _ _ _ _ _ HD) 1 N); [lia|].
  apply GPhi_sound; [exact HG | apply (DigE_props _ _ _ _ _ HD)].
Qed.

(* ===================================================================== *)
(* Section 8. Positions and potentials (write-up D.0, Lemma C, D.7).      *)
(* ===================================================================== *)

Definition exs (bs : blks) : list nat := map snd bs.

Fixpoint bumpl (l : list nat) : list nat :=
  match l with [] => [] | e :: l' => match l' with [] => [S e] | _ => e :: bumpl l' end end.

Lemma length_bumpl l : length (bumpl l) = length l.
Proof. induction l as [|e l IH]; [reflexivity|]. destruct l; cbn in *; [reflexivity|]. rewrite IH. reflexivity. Qed.

Lemma length_exs bs : length (exs bs) = length bs.
Proof. apply length_map. Qed.

(* inc on G: the exponents stay, or (overflow) the last one gets +1 and a new 0 is appended. *)
Lemma ginc_exps bs s : s <= 3 -> forall bs' s' d, ginc bs s = (bs', s', d) ->
  (exs bs' = exs bs /\ d = false) \/
  (exs bs' = bumpl (exs bs) ++ [0] /\ d = match bs with [] => true | _ => false end).
Proof.
  intros Hs. induction bs as [|[[|] e] bs IH]; intros bs' s' d E; cbn in E.
  - destruct s as [|[|[|[|s]]]]; inversion E; subst; cbn; auto; lia.
  - destruct (ginc bs s) as [[b1 s1] d1] eqn:E1. inversion E; subst.
    destruct (IH _ _ _ eq_refl) as [[H1 H2] | [H1 H2]]; subst; unfold exs in *; cbn [map snd].
    + left. rewrite H1. auto.
    + right. rewrite H1. destruct bs as [|b bs]; cbn in *; subst; cbn; auto.
  - inversion E; subst. left. auto.
Qed.

(* ---------- the Q potential: bounds the number of positions ---------- *)

Fixpoint qsum (l : list nat) : nat := match l with [] => 0 | e :: l => S e + 2 * qsum l end.
Definition Qp (f : nat) (bs : blks) (s p : nat) : nat := 2 ^ f * (gval bs s + 2 * qsum (exs bs) + p).
Definition QI (Q0 f : nat) (bs : blks) (s p : nat) : Prop := Qp f bs s p <= Q0 + 3 * 2 ^ (f + length bs).

Lemma qsum_app0 l : qsum (l ++ [0]) = qsum l + 2 ^ length l.
Proof. induction l as [|e l IH]; cbn [qsum app length]; [reflexivity|]. rewrite IH. cbn. lia. Qed.

Lemma qsum_bumpl l : l <> [] -> 2 * qsum (bumpl l) = 2 * qsum l + 2 ^ length l.
Proof.
  induction l as [|e l IH]; intros Hne; [congruence|].
  destruct l as [|e' l]; [cbn; lia|].
  change (bumpl (e :: e' :: l)) with (e :: bumpl (e' :: l)).
  cbn [qsum length]. rewrite Nat.pow_succ_r'. specialize (IH ltac:(discriminate)). cbn [qsum length] in IH. lia.
Qed.

Lemma gval_lb bs s : 4 * 2 ^ length bs <= gval bs s.
Proof. induction bs as [|[d e] bs IH]; cbn [gval length]; [cbn; lia|]. rewrite Nat.pow_succ_r'. lia. Qed.

Lemma gval_ub bs s : s <= 3 -> gval bs s < 8 * 2 ^ length bs.
Proof. intros Hs. induction bs as [|[d e] bs IH]; cbn [gval length]; [cbn; lia|]. rewrite Nat.pow_succ_r'. destruct d; lia. Qed.

Lemma QI_low Q0 f bs s p : QI Q0 f bs s p -> 2 ^ (f + length bs) <= Q0.
Proof.
  unfold QI, Qp. intros H. pose proof (gval_lb bs s) as G. rewrite Nat.pow_add_r in *.
  assert (2 ^ f * (4 * 2 ^ length bs) <= 2 ^ f * (gval bs s + 2 * qsum (exs bs) + p)) by (apply Nat.mul_le_mono_l; lia).
  lia.
Qed.

Lemma QI_Ps Q0 Ps f bs s p : QI Q0 f bs s p -> Q0 < 2 ^ (Ps + 1) -> f + length bs <= Ps.
Proof.
  intros H HP. apply QI_low in H. destruct (Nat.le_gt_cases (f + length bs) Ps) as [|Hc]; [assumption|].
  assert (2 ^ (Ps + 1) <= 2 ^ (f + length bs)) by (apply Nat.pow_le_mono_r; lia). lia.
Qed.

Lemma QI_drop Q0 f bs s p : QI Q0 f bs s p -> QI Q0 f bs s 0.
Proof. unfold QI, Qp. intros H. assert (2 ^ f * (gval bs s + 2 * qsum (exs bs) + 0) <= 2 ^ f * (gval bs s + 2 * qsum (exs bs) + p)) by (apply Nat.mul_le_mono_l; lia). lia. Qed.

Lemma QI_cons Q0 f dd e bs s p : QI Q0 f ((dd, e) :: bs) s 0 -> p <= S e -> QI Q0 (S f) bs s p.
Proof.
  unfold QI, Qp, exs. cbn [map snd qsum gval length]. intros H Hp.
  replace (S f + length bs) with (f + S (length bs)) by lia.
  rewrite Nat.pow_succ_r'.
  set (F := 2 ^ f) in *. set (G := gval bs s) in *. set (Q := qsum (map snd bs)) in *.
  assert (F * p <= F * S e) by (apply Nat.mul_le_mono_l; lia).
  assert (E1 : 2 * F * (G + 2 * Q + p) = 2 * (F * G) + 4 * (F * Q) + 2 * (F * p)) by ring.
  assert (E2 : F * ((if dd then 1 else 0) + 2 * G + 2 * (S e + 2 * Q) + 0) =
    F * (if dd then 1 else 0) + 2 * (F * G) + 2 * (F * S e) + 4 * (F * Q)) by ring.
  rewrite E1. rewrite E2 in H. lia.
Qed.

Lemma QI_inc Q0 f bs s p bs' s' d : s <= 3 -> ginc bs s = (bs', s', d) ->
  QI Q0 f bs s (S p) -> QI Q0 f bs' s' (p + b2n d).
Proof.
  intros Hs E H. unfold QI, Qp in *.
  destruct (ginc_val bs s Hs _ _ _ E) as (V & _).
  destruct (ginc_exps bs s Hs _ _ _ E) as [[E1 E2] | [E1 E2]]; subst d.
  - assert (L : length bs' = length bs) by (rewrite <- !length_exs, E1; reflexivity).
    rewrite E1, V, L. cbn [b2n]. replace (S (gval bs s) + 2 * qsum (exs bs) + (p + 0)) with
      (gval bs s + 2 * qsum (exs bs) + S p) by lia. exact H.
  - assert (L : length bs' = S (length bs))
      by (rewrite <- !length_exs, E1, length_app, length_bumpl; cbn; lia).
    rewrite E1, V, L, qsum_app0, length_bumpl, length_exs.
    replace (f + S (length bs)) with (S (f + length bs)) by lia.
    rewrite Nat.pow_succ_r'. rewrite Nat.pow_add_r in *.
    destruct bs as [|b bs0].
    + cbn [bumpl exs map qsum length b2n] in *. rewrite Nat.pow_0_r in *.
      rewrite !Nat.mul_add_distr_l in *. lia.
    + cbn [b2n]. pose proof (qsum_bumpl (exs (b :: bs0)) ltac:(cbn; discriminate)) as QB.
      rewrite length_exs in QB.
      set (F := 2 ^ f) in *. set (X := 2 ^ length (b :: bs0)) in *.
      set (G := gval (b :: bs0) s) in *. set (Q := qsum (exs (b :: bs0))) in *.
      set (Q' := qsum (bumpl (exs (b :: bs0)))) in *.
      rewrite !Nat.mul_add_distr_l in *.
      assert (F * (2 * (Q' + X)) = 2 * (F * Q) + 3 * (F * X)) by nia.
      lia.
Qed.

Lemma QI_et3 Q0 f : QI Q0 f [] 3 0 -> QI Q0 f [(false, 0)] 0 0.
Proof. unfold QI, Qp. cbn. rewrite !Nat.add_0_r. rewrite Nat.add_1_r, Nat.pow_succ_r'. lia. Qed.

(* ---------- generic weighted potentials over positions ---------- *)

Fixpoint wpot (v : nat -> nat) (al be f : nat) (l : list nat) : nat :=
  match l with [] => 0 | e :: l => v f * (al * e + be) + wpot v al be (S f) l end.

Fixpoint vsum (v : nat -> nat) (f m : nat) : nat :=
  match m with 0 => 0 | S m => v f + vsum v (S f) m end.

Definition Pot (v : nat -> nat) (al be ga Ps f : nat) (l : list nat) : nat :=
  wpot v al be f l + ga * vsum v (f + length l) (Ps - (f + length l)).

Definition mono (v : nat -> nat) : Prop := forall i j, i <= j -> v i <= v j.

Lemma Pot_cons v al be ga Ps f e l :
  Pot v al be ga Ps f (e :: l) = v f * (al * e + be) + Pot v al be ga Ps (S f) l.
Proof. unfold Pot. cbn [wpot length]. replace (f + S (length l)) with (S f + length l) by lia. lia. Qed.

Lemma wpot_app1 v al be f l x : wpot v al be f (l ++ [x]) = wpot v al be f l + v (f + length l) * (al * x + be).
Proof.
  revert f. induction l as [|e l IH]; intros f; cbn [wpot app length].
  - rewrite !Nat.add_0_r. reflexivity.
  - rewrite IH. replace (S f + length l) with (f + S (length l)) by lia. lia.
Qed.

Lemma wpot_bumpl v al be f l : mono v -> wpot v al be f (bumpl l) <= wpot v al be f l + al * v (f + length l).
Proof.
  intros Hv. revert f. induction l as [|e l IH]; intros f; [cbn; lia|].
  destruct l as [|e' l].
  - cbn [bumpl wpot length]. pose proof (Hv f (f + 1) ltac:(lia)). nia.
  - change (bumpl (e :: e' :: l)) with (e :: bumpl (e' :: l)). cbn [wpot length].
    specialize (IH (S f)). cbn [wpot length] in IH. replace (S f + S (length l)) with (f + S (S (length l))) in IH by lia.
    lia.
Qed.

Lemma Pot_ov v al be ga Ps f l : mono v -> al + be + 1 <= ga -> f + length l + 1 <= Ps ->
  Pot v al be ga Ps f (bumpl l ++ [0]) + v (f + length l) <= Pot v al be ga Ps f l.
Proof.
  intros Hv Hg HP. unfold Pot. rewrite wpot_app1, length_app, length_bumpl. cbn [length].
  pose proof (wpot_bumpl v al be f l Hv) as B.
  replace (Ps - (f + length l)) with (S (Ps - (f + (length l + 1)))) by lia.
  cbn [vsum]. replace (S (f + length l)) with (f + (length l + 1)) by lia.
  set (V := v (f + length l)) in *. set (R := vsum v (f + (length l + 1)) (Ps - (f + (length l + 1)))).
  assert ((al + be + 1) * V <= ga * V) by (apply Nat.mul_le_mono_r; lia).
  rewrite Nat.mul_0_r, Nat.add_0_l, Nat.mul_add_distr_l. rewrite !Nat.mul_add_distr_r in *. lia.
Qed.

Lemma Pot_inc v al be ga Ps Q0 f bs s p bs' s' d : mono v -> al + be + 1 <= ga -> Q0 < 2 ^ (Ps + 1) -> s <= 3 ->
  ginc bs s = (bs', s', d) -> QI Q0 f bs s (S p) ->
  Pot v al be ga Ps f (exs bs') + b2n d * v f <= Pot v al be ga Ps f (exs bs).
Proof.
  intros Hv Hg HP Hs E HQ.
  pose proof (QI_inc _ _ _ _ _ _ _ _ Hs E HQ) as HQ'. apply (QI_Ps _ Ps) in HQ'; [|exact HP].
  destruct (ginc_exps bs s Hs _ _ _ E) as [[E1 E2] | [E1 E2]]; subst.
  - rewrite E1. cbn. lia.
  - rewrite E1. assert (length bs' = S (length bs)) as L
      by (rewrite <- !length_exs, E1, length_app, length_bumpl; cbn; lia).
    pose proof (Pot_ov v al be ga Ps f (exs bs) Hv Hg) as O. rewrite length_exs in O.
    specialize (O ltac:(lia)). destruct bs; cbn [b2n] in *; [rewrite Nat.add_0_r in O; lia | lia].
Qed.

(* The epoch map consumes positions from the front; the potential pays for each one. *)
Lemma GPhi_pot v al be ga Ps Q0 : mono v -> al + be + 1 <= ga -> 1 <= al -> 2 <= be -> Q0 < 2 ^ (Ps + 1) ->
  forall a b bs s r, GPhi a b bs s r -> s <= 3 -> forall f U, QI Q0 f bs s (b - 1) ->
  (forall q, f <= q -> U <= v q) ->
  match r with
  | RE2 k x bs2 s2 => exists h, QI Q0 (f + S h) bs2 s2 0 /\
      U * k + Pot v al be ga Ps (f + S h) (exs bs2) + v (f + h) * (al * x + be) <=
      Pot v al be ga Ps f (exs bs) + U * (a + b - 1) + al * v (f + h)
  | RSp k y => U * k <= Pot v al be ga Ps f (exs bs) + U * (a + b)
  end.
Proof.
  intros Hv Hg Ha Hb HP.
  induction 1 as [a b bs s bs' s' d r E H IH | a e bs s r H IH | a e bs s bs' s' d E | a | a | a | a r H IH];
    intros Hs f U HQ HU.
  - (* bounce *)
    replace (S (S b) - 1) with (S b) in HQ by lia.
    pose proof (Pot_inc v al be ga Ps Q0 f bs s b bs' s' d Hv Hg HP Hs E HQ) as PI.
    pose proof (QI_inc _ _ _ _ _ _ _ _ Hs E HQ) as HQ'.
    specialize (IH (ginc_s3 _ _ _ _ _ Hs E) f U).
    rewrite addb_b2n in IH. replace (S b + b2n d - 1) with (b + b2n d) in IH by lia.
    specialize (IH HQ' HU). pose proof (HU f (le_n _)) as Uf.
    destruct r as [k x bs2 s2 | k y].
    + destruct IH as (h & H1 & H2). exists h. split; [exact H1|].
      assert (U * b2n d <= b2n d * v f) by (destruct d; cbn; lia). nia.
    + assert (U * b2n d <= b2n d * v f) by (destruct d; cbn; lia). nia.
  - (* E1g *)
    pose proof (QI_cons _ _ _ _ _ _ e HQ (le_S _ _ (le_n _))) as HQ'.
    specialize (IH Hs (S f) U). replace (S e - 1) with e in IH by lia. specialize (IH HQ').
    specialize (IH (fun q Hq => HU q ltac:(lia))). pose proof (HU f (le_n _)) as Uf.
    change (exs ((false, e) :: bs)) with (e :: exs bs). rewrite Pot_cons.
    assert (U * (e + 2) <= v f * (al * e + be)).
    { apply (Nat.le_trans _ (v f * (e + 2))); [apply Nat.mul_le_mono_r; exact Uf|].
      apply Nat.mul_le_mono_l. assert (e <= al * e) by nia. lia. }
    destruct r as [k x bs2 s2 | k y].
    + destruct IH as (h & H1 & H2). exists (S h).
      replace (f + S (S h)) with (S f + S h) by lia. replace (f + S h) with (S f + h) by lia.
      split; [exact H1|].
      replace (S (S a) + S e - 1) with (a + (e + 2)) in H2 by lia. rewrite (Nat.mul_add_distr_l U a (e + 2)) in H2.
      replace (a + 1 - 1) with a by lia. lia.
    + replace (S (S a) + S e) with ((a + 1) + (e + 2)) in IH by lia. rewrite (Nat.mul_add_distr_l U (a + 1) (e + 2)) in IH. lia.
  - (* E2g *)
    exists 0. pose proof (QI_cons _ _ _ _ _ _ 1 HQ ltac:(lia)) as HQ1.
    pose proof (QI_inc _ _ _ _ _ _ _ _ Hs E HQ1) as HQ2.
    pose proof (Pot_inc v al be ga Ps Q0 (S f) bs s 0 bs' s' d Hv Hg HP Hs E HQ1) as PI.
    replace (f + 1) with (S f) by lia. rewrite Nat.add_0_r.
    split; [eapply QI_drop; exact HQ2|].
    change (exs ((true, e) :: bs)) with (e :: exs bs). rewrite Pot_cons, addb_b2n.
    assert (v f * (al * (e + b2n d) + be) <= v f * (al * e + be) + al * v f) by (destruct d; cbn; nia).
    replace (a + 1 - 1) with a by lia. lia.
  - nia.
  - nia.
  - nia.
  - (* Et3 *)
    pose proof (QI_et3 _ _ HQ) as HQ'.
    pose proof (QI_Ps _ Ps _ _ _ _ HQ' HP) as HPs. cbn [length] in HPs.
    pose proof (Pot_ov v al be ga Ps f [] Hv Hg ltac:(cbn; lia)) as O. cbn [bumpl app length] in O.
    rewrite Nat.add_0_r in O.
    specialize (IH ltac:(lia) f U HQ' HU). pose proof (HU f (le_n _)) as Uf.
    destruct r as [k x bs2 s2 | k y].
    + destruct IH as (h & H1 & H2). exists h. split; [exact H1|]. cbn [exs map snd] in *.
      replace (S a + 1 - 1) with (a + 1) in H2 by lia. rewrite (Nat.mul_add_distr_l U a 1) in H2.
      replace (a + 1 - 1) with a by lia. lia.
    + cbn [exs map snd] in *. replace (S a + 1) with (a + 1 + 1) in IH by lia.
      rewrite (Nat.mul_add_distr_l U (a + 1) 1) in IH. lia.
Qed.

(* ===================================================================== *)
(* Section 9. Digestion bounds: cost, merged exponents, length; existence. *)
(* ===================================================================== *)

Definition w (q : nat) : nat := 2 ^ ((q + 1) / 2).

Lemma w_mono : mono w.
Proof. intros i j H. unfold w. apply Nat.pow_le_mono_r; [lia|]. apply Nat.Div0.div_le_mono; lia. Qed.

Lemma w_lev l q : 2 * l <= q -> 2 ^ l <= w q.
Proof.
  intros H. unfold w. apply Nat.pow_le_mono_r; [lia|].
  replace l with ((2 * l) / 2) at 1 by (rewrite Nat.mul_comm, Nat.div_mul; lia).
  apply Nat.Div0.div_le_mono; lia.
Qed.

Lemma w_lev1 l q : 2 * l + 1 <= q -> 2 ^ S l <= w q.
Proof.
  intros H. unfold w. apply Nat.pow_le_mono_r; [lia|].
  replace (S l) with ((2 * S l) / 2) at 1 by (rewrite Nat.mul_comm, Nat.div_mul; lia).
  apply Nat.Div0.div_le_mono; lia.
Qed.

Lemma GPhi_QI Q0 Ps a b bs s k x bs2 s2 f : Q0 < 2 ^ (Ps + 1) -> GPhi a b bs s (RE2 k x bs2 s2) -> s <= 3 ->
  QI Q0 f bs s (b - 1) -> exists h, QI Q0 (f + S h) bs2 s2 0.
Proof.
  intros HP HG Hs HQ.
  pose proof (GPhi_pot (fun _ => 0) 1 2 4 Ps Q0 ltac:(intros ? ? ?; lia) ltac:(lia) ltac:(lia) ltac:(lia) HP
    _ _ _ _ _ HG Hs f 0 HQ ltac:(intros; lia)) as G.
  destruct G as (h & G & _). eauto.
Qed.

Lemma Dig_cost Q0 Ps : Q0 < 2 ^ (Ps + 1) ->
  (forall x bs s n c bsp sp, DigP x bs s n c bsp sp -> s <= 3 -> forall l f, 2 * l <= f -> QI Q0 f bs s 0 ->
    2 ^ l * n <= Pot w 2 8 11 Ps f (exs bs) + 2 ^ l * (2 * x + 2) + 13 * w Ps) /\
  (forall bs s n c bsp sp, DigT bs s n c bsp sp -> s <= 3 -> forall l f, 2 * l <= f -> QI Q0 f bs s 0 ->
    2 ^ l * n <= Pot w 2 8 11 Ps f (exs bs) + 13 * w Ps).
Proof.
  intros HP. apply Dig_mind.
  - intros x bs s n c bsp sp H IH Hs l f Hl HQ. specialize (IH Hs l f Hl HQ).
    rewrite Nat.mul_add_distr_l. lia.
  - intros e bs s bs' s' d n c bsp sp E H IH Hs l f Hl HQ.
    pose proof (QI_cons _ _ _ _ _ _ 1 HQ ltac:(lia)) as HQ1.
    pose proof (QI_inc _ _ _ _ _ _ _ _ Hs E HQ1) as HQ2. apply QI_drop in HQ2.
    specialize (IH (ginc_s3 _ _ _ _ _ Hs E) l (S f) ltac:(lia) HQ2).
    pose proof (Pot_inc w 2 8 11 Ps Q0 (S f) bs s 0 bs' s' d w_mono ltac:(lia) HP Hs E HQ1) as PI.
    change (exs ((false, e) :: bs)) with (e :: exs bs). rewrite Pot_cons.
    pose proof (w_lev l f Hl) as Wf. set (L := 2 ^ l) in *.
    assert (E1 : L * S (S n) = L * n + 2 * L) by ring.
    assert (E2 : L * (2 * S (addb e d) + 2) + 2 * L <= w f * (2 * e + 8)).
    { rewrite addb_b2n. assert (L * (2 * S (e + b2n d) + 2) + 2 * L <= L * (2 * e + 8)) by (destruct d; cbn [b2n]; nia).
      assert (L * (2 * e + 8) <= w f * (2 * e + 8)) by (apply Nat.mul_le_mono_r; exact Wf). lia. }
    lia.
  - intros e bs s k x bs2 s2 n c bsp sp HG H IH Hs l f Hl HQ.
    pose proof (QI_cons _ _ _ _ _ _ e HQ (le_S _ _ (le_n _))) as HQ1.
    pose proof (GPhi_pot w 2 8 11 Ps Q0 w_mono ltac:(lia) ltac:(lia) ltac:(lia) HP _ _ _ _ _ HG Hs (S f) 0) as G.
    replace (S e - 1) with e in G by lia. specialize (G HQ1 (fun _ _ => Nat.le_0_l _)).
    destruct G as (h & G1 & G2).
    pose proof (GPhi_s3 _ _ _ _ _ HG Hs) as Hs2. cbn in Hs2.
    specialize (IH Hs2 (S l) (S f + S h) ltac:(lia) G1).
    change (exs ((true, e) :: bs)) with (e :: exs bs). rewrite Pot_cons.
    pose proof (w_lev l f Hl) as Wf. pose proof (w_lev1 l (S f + h) ltac:(lia)) as Wh.
    rewrite Nat.pow_succ_r' in IH, Wh. set (L := 2 ^ l) in *. set (W' := w (S f + h)) in *.
    assert (E1 : L * S (2 * n) = L + 2 * L * n) by ring.
    assert (E2 : 2 * L * (2 * x + 2) <= W' * (2 * x + 2)) by (apply Nat.mul_le_mono_r; exact Wh).
    assert (E3 : W' * (2 * x + 8) = W' * (2 * x + 2) + 6 * W') by ring.
    assert (E4 : L <= w f * (2 * e + 8)) by nia.
    rewrite Nat.mul_0_l in G2. lia.
  - intros e bs s k y n c bsp sp HG H Hs l f Hl HQ.
    destruct (DigE_props _ _ _ _ _ H) as (Hn & _).
    pose proof (QI_Ps _ Ps _ _ _ _ HQ HP) as HPs. cbn [length] in HPs.
    change (exs ((true, e) :: bs)) with (e :: exs bs). rewrite Pot_cons.
    pose proof (w_lev l f Hl) as Wf. pose proof (w_lev1 l Ps ltac:(lia)) as Wh.
    rewrite Nat.pow_succ_r' in Wh. set (L := 2 ^ l) in *.
    assert (E1 : L * S (2 * n) = L + 2 * L * n) by ring.
    assert (E2 : 2 * L * n <= 13 * w Ps) by nia.
    assert (E4 : L <= w f * (2 * e + 8)) by nia.
    lia.
  - intros s n c bsp sp H Hs l f Hl HQ.
    destruct (DigE_props _ _ _ _ _ H) as (Hn & _).
    pose proof (QI_Ps _ Ps _ _ _ _ HQ HP) as HPs. cbn [length] in HPs.
    pose proof (w_lev l Ps ltac:(lia)) as Wf. nia.
Qed.

Fixpoint MO (u : nat -> nat) (l : nat) (es : list nat) : nat :=
  match es with [] => 0 | e :: es => u l * e + MO u (S l) es end.

Definition pu (u : nat -> nat) (l : nat) : nat := match l with 0 => 0 | S l' => u l' end.

Lemma pu_le u l : mono u -> pu u l <= u l.
Proof. intros Hu. destruct l; cbn; [lia | apply Hu; lia]. Qed.

Lemma MO_zero u l es : Forall (fun e => e = 0) es -> MO u l es = 0.
Proof. intros H. revert l. induction H as [|e es He H IH]; intros l; cbn; [reflexivity|]. rewrite IH, He. lia. Qed.

(* The merged blocks (write-up D.3): any level weights u that the position weights v dominate. *)
Lemma Dig_mass u v Q0 Ps : mono v -> mono u -> (forall l q, 2 * l <= q -> u l <= v q) -> Q0 < 2 ^ (Ps + 1) ->
  (forall x bs s n c bsp sp, DigP x bs s n c bsp sp -> s <= 3 -> forall l f, 2 * l <= f -> QI Q0 f bs s 0 ->
    pu u l * c + MO u l (exs bsp) <= Pot v 1 3 5 Ps f (exs bs) + pu u l * S x + 6 * v Ps) /\
  (forall bs s n c bsp sp, DigT bs s n c bsp sp -> s <= 3 -> forall l f, 2 * l <= f -> QI Q0 f bs s 0 ->
    pu u l * c + MO u l (exs bsp) <= Pot v 1 3 5 Ps f (exs bs) + 6 * v Ps).
Proof.
  intros Hv Hu Huv HP. apply Dig_mind.
  - intros x bs s n c bsp sp H IH Hs l f Hl HQ. specialize (IH Hs l f Hl HQ).
    rewrite Nat.mul_add_distr_l. lia.
  - intros e bs s bs' s' d n c bsp sp E H IH Hs l f Hl HQ.
    pose proof (QI_cons _ _ _ _ _ _ 1 HQ ltac:(lia)) as HQ1.
    pose proof (QI_inc _ _ _ _ _ _ _ _ Hs E HQ1) as HQ2. apply QI_drop in HQ2.
    specialize (IH (ginc_s3 _ _ _ _ _ Hs E) l (S f) ltac:(lia) HQ2).
    pose proof (Pot_inc v 1 3 5 Ps Q0 (S f) bs s 0 bs' s' d Hv ltac:(lia) HP Hs E HQ1) as PI.
    change (exs ((false, e) :: bs)) with (e :: exs bs). rewrite Pot_cons.
    pose proof (Nat.le_trans _ _ _ (pu_le u l Hu) (Huv l f Hl)) as Pf.
    assert (pu u l * S (S (addb e d)) <= v f * (1 * e + 3)).
    { rewrite addb_b2n. apply Nat.mul_le_mono; [exact Pf | destruct d; cbn; lia]. }
    lia.
  - intros e bs s k x bs2 s2 n c bsp sp HG H IH Hs l f Hl HQ.
    pose proof (QI_cons _ _ _ _ _ _ e HQ (le_S _ _ (le_n _))) as HQ1.
    pose proof (GPhi_pot v 1 3 5 Ps Q0 Hv ltac:(lia) ltac:(lia) ltac:(lia) HP _ _ _ _ _ HG Hs (S f) (u l)) as G.
    replace (S e - 1) with e in G by lia. specialize (G HQ1 (fun q Hq => Huv l q ltac:(lia))).
    destruct G as (h & G1 & G2).
    pose proof (GPhi_s3 _ _ _ _ _ HG Hs) as Hs2. cbn in Hs2.
    specialize (IH Hs2 (S l) (S f + S h) ltac:(lia) G1). cbn [pu] in IH.
    change (exs ((true, e) :: bs)) with (e :: exs bs). rewrite Pot_cons.
    change (exs ((false, k + c) :: bsp)) with ((k + c) :: exs bsp). cbn [MO].
    pose proof (Huv l f Hl) as Uf. pose proof (Huv l (S f + h) ltac:(lia)) as Uh.
    set (U := u l) in *. set (V' := v (S f + h)) in *.
    assert (E1 : U * S x <= V' * (x + 2)) by (apply Nat.mul_le_mono; lia).
    assert (E2 : V' * (1 * x + 3) = V' * (x + 2) + V') by ring.
    assert (E3 : U * (1 + S e - 1) <= v f * (1 * e + 3)) by (apply Nat.mul_le_mono; lia).
    assert (E4 : U * (k + c) = U * k + U * c) by ring.
    rewrite Nat.mul_0_r. lia.
  - intros e bs s k y n c bsp sp HG H Hs l f Hl HQ.
    destruct (DigE_props _ _ _ _ _ H) as (_ & Hc & _ & _ & Hz).
    pose proof (QI_cons _ _ _ _ _ _ e HQ (le_S _ _ (le_n _))) as HQ1.
    pose proof (GPhi_pot v 1 3 5 Ps Q0 Hv ltac:(lia) ltac:(lia) ltac:(lia) HP _ _ _ _ _ HG Hs (S f) (u l)) as G.
    replace (S e - 1) with e in G by lia. specialize (G HQ1 (fun q Hq => Huv l q ltac:(lia))). cbn beta iota in G.
    pose proof (QI_Ps _ Ps _ _ _ _ HQ HP) as HPs. cbn [length] in HPs.
    change (exs ((true, e) :: bs)) with (e :: exs bs). rewrite Pot_cons.
    change (exs ((false, k + c) :: bsp)) with ((k + c) :: exs bsp). cbn [MO]. rewrite (MO_zero _ _ _ Hz).
    pose proof (Huv l f Hl) as Uf. pose proof (Huv l Ps ltac:(lia)) as Up.
    set (U := u l) in *.
    assert (E3 : U * (1 + S e) <= v f * (1 * e + 3)) by (apply Nat.mul_le_mono; lia).
    assert (E4 : U * (k + c) = U * k + U * c) by ring.
    assert (E5 : U * c <= 6 * v Ps) by nia.
    rewrite Nat.mul_0_r. lia.
  - intros s n c bsp sp H Hs l f Hl HQ.
    destruct (DigE_props _ _ _ _ _ H) as (_ & Hc & _ & _ & Hz). rewrite (MO_zero _ _ _ Hz).
    pose proof (QI_Ps _ Ps _ _ _ _ HQ HP) as HPs. cbn [length] in HPs.
    pose proof (Nat.le_trans _ _ _ (pu_le u l Hu) (Huv l Ps ltac:(lia))) as Pf. nia.
Qed.

Lemma Dig_len Q0 Ps : Q0 < 2 ^ (Ps + 1) ->
  (forall x bs s n c bsp sp, DigP x bs s n c bsp sp -> s <= 3 -> forall l f, 2 * l <= f -> QI Q0 f bs s 0 ->
    2 * (l + length bsp) <= Ps + 3) /\
  (forall bs s n c bsp sp, DigT bs s n c bsp sp -> s <= 3 -> forall l f, 2 * l <= f -> QI Q0 f bs s 0 ->
    2 * (l + length bsp) <= Ps + 3).
Proof.
  intros HP. apply Dig_mind.
  - intros x bs s n c bsp sp H IH Hs l f Hl HQ. exact (IH Hs l f Hl HQ).
  - intros e bs s bs' s' d n c bsp sp E H IH Hs l f Hl HQ.
    pose proof (QI_cons _ _ _ _ _ _ 1 HQ ltac:(lia)) as HQ1.
    pose proof (QI_inc _ _ _ _ _ _ _ _ Hs E HQ1) as HQ2. apply QI_drop in HQ2.
    exact (IH (ginc_s3 _ _ _ _ _ Hs E) l (S f) ltac:(lia) HQ2).
  - intros e bs s k x bs2 s2 n c bsp sp HG H IH Hs l f Hl HQ.
    pose proof (QI_cons _ _ _ _ _ _ e HQ (le_S _ _ (le_n _))) as HQ1.
    destruct (GPhi_QI Q0 Ps _ _ _ _ _ _ _ _ (S f) HP HG Hs ltac:(replace (S e - 1) with e by lia; exact HQ1)) as (h & G1).
    pose proof (GPhi_s3 _ _ _ _ _ HG Hs) as Hs2. cbn in Hs2.
    specialize (IH Hs2 (S l) (S f + S h) ltac:(lia) G1). cbn [length]. lia.
  - intros e bs s k y n c bsp sp HG H Hs l f Hl HQ.
    destruct (DigE_props _ _ _ _ _ H) as (_ & _ & Hb & _).
    pose proof (QI_Ps _ Ps _ _ _ _ HQ HP) as HPs. cbn [length] in *. lia.
  - intros s n c bsp sp H Hs l f Hl HQ.
    destruct (DigE_props _ _ _ _ _ H) as (_ & _ & Hb & _).
    pose proof (QI_Ps _ Ps _ _ _ _ HQ HP) as HPs. cbn [length] in *. lia.
Qed.

Lemma pow_gt_self n : n < 2 ^ (n + 1).
Proof. induction n as [|n IH]; cbn; [lia|]. rewrite Nat.add_0_r. lia. Qed.

Lemma DigE_ex y : y = t1 \/ y = p01 1 t1 \/ y = p10 (p00 t2) -> exists n c bsp sp, DigE y n c bsp sp.
Proof. intros [-> | [-> | ->]]; do 4 eexists; constructor. Qed.

(* Every residue 11 (001)^x 000 W with W a counter word has a digestion. *)
Lemma DigT_exists Q0 : forall D f bs s, s <= 3 -> QI Q0 f bs s 0 -> Q0 + 1 - 2 ^ f <= D ->
  exists n c bsp sp, DigT bs s n c bsp sp.
Proof.
  induction D as [D IHD] using lt_wf_ind. intros f bs s Hs HQ HD.
  pose proof (pow_gt_self Q0) as HP.
  destruct bs as [|[[|] e] bs].
  - destruct s as [|[|[|[|s]]]]; try lia; do 4 eexists; apply DTt; constructor.
  - destruct (gcount (Psi bs s (S e)) bs s 1 (S e) Hs ltac:(lia) (le_n _)) as (r & HG).
    pose proof (QI_cons _ _ _ _ _ _ e HQ (le_S _ _ (le_n _))) as HQ1.
    pose proof (GPhi_s3 _ _ _ _ _ HG Hs) as Hr.
    destruct r as [k x bs2 s2 | k y].
    + destruct (GPhi_QI Q0 Q0 _ _ _ _ _ _ _ _ (S f) HP HG Hs ltac:(replace (S e - 1) with e by lia; exact HQ1)) as (h & G1).
      pose proof (QI_low _ _ _ _ _ G1) as L1. rewrite Nat.pow_add_r in L1.
      assert (2 ^ f < 2 ^ (S f + S h)) by (apply Nat.pow_lt_mono_r; lia).
      assert (1 <= 2 ^ length bs2) by (apply Nat.neq_0_lt_0, Nat.pow_nonzero; lia).
      assert (2 ^ (S f + S h) <= Q0) by nia.
      destruct (IHD (Q0 + 1 - 2 ^ (S f + S h)) ltac:(lia) (S f + S h) bs2 s2 Hr G1 (le_n _)) as (n & c & bsp & sp & HT).
      do 4 eexists. eapply DTb; [exact HG | apply DP; exact HT].
    + destruct (DigE_ex y Hr) as (n & c & bsp & sp & HE).
      do 4 eexists. eapply DTs; [exact HG | exact HE].
  - destruct (ginc bs s) as [[bs' s'] d] eqn:E.
    pose proof (QI_cons _ _ _ _ _ _ 1 HQ ltac:(lia)) as HQ1.
    pose proof (QI_inc _ _ _ _ _ _ _ _ Hs E HQ1) as HQ2. apply QI_drop in HQ2.
    pose proof (QI_low _ _ _ _ _ HQ2) as L1. rewrite Nat.pow_add_r in L1.
    assert (2 ^ f < 2 ^ S f) by (apply Nat.pow_lt_mono_r; lia).
    assert (1 <= 2 ^ length bs') by (apply Nat.neq_0_lt_0, Nat.pow_nonzero; lia).
    assert (2 ^ S f <= Q0) by nia.
    destruct (IHD (Q0 + 1 - 2 ^ S f) ltac:(lia) (S f) bs' s' (ginc_s3 _ _ _ _ _ Hs E) HQ2 (le_n _))
      as (n & c & bsp & sp & HT).
    do 4 eexists. eapply DTa; [exact E | apply DP; exact HT].
Qed.

(* ---------- the counting phase: exponents and value ---------- *)

Definition Rel (orig cur : list nat) : Prop :=
  (forall i, S i < length cur -> nth i cur 0 <= nth i orig 0 + 1) /\
  (forall i, length cur <= S i -> nth i cur 0 <= nth i orig 0).

Lemma nth_bumpl l i : nth i (bumpl l) 0 = nth i l 0 + (if Nat.eqb (S i) (length l) then 1 else 0).
Proof.
  revert i. induction l as [|e l IH]; intros i; [destruct i; reflexivity|].
  destruct l as [|e' l].
  - destruct i as [|[|i]]; cbn; lia.
  - change (bumpl (e :: e' :: l)) with (e :: bumpl (e' :: l)).
    destruct i as [|i]; cbn [nth length]; [cbn; lia|]. rewrite IH. reflexivity.
Qed.

Lemma nth_app0 l i : nth i (l ++ [0]) 0 = nth i l 0.
Proof. revert i. induction l as [|e l IH]; intros [|i]; cbn; auto. destruct i; reflexivity. Qed.

Lemma Rel_ov orig l : Rel orig l -> Rel orig (bumpl l ++ [0]).
Proof.
  intros [R1 R2]. unfold Rel. rewrite length_app, length_bumpl. cbn [length]. split; intros i Hi; rewrite nth_app0, nth_bumpl.
  - destruct (Nat.eqb_spec (S i) (length l)).
    + specialize (R2 i ltac:(lia)). lia.
    + destruct (Nat.lt_ge_cases (S i) (length l)) as [H|H]; [specialize (R1 i H); lia|].
      rewrite nth_overflow by lia. lia.
  - destruct (Nat.eqb_spec (S i) (length l)); [lia|]. rewrite nth_overflow by lia. lia.
Qed.

Lemma Rel_inc orig bs s bs' s' d : s <= 3 -> ginc bs s = (bs', s', d) -> Rel orig (exs bs) -> Rel orig (exs bs').
Proof.
  intros Hs E R. destruct (ginc_exps bs s Hs _ _ _ E) as [[E1 _] | [E1 _]]; rewrite E1; [exact R|].
  apply Rel_ov, R.
Qed.

Lemma Rel_tl orig cur : Rel orig cur -> Rel (tl orig) (tl cur).
Proof.
  intros [R1 R2]. split; intros i Hi.
  - destruct cur as [|c cur]; cbn in Hi; [lia|]. specialize (R1 (S i) ltac:(cbn; lia)).
    destruct orig as [|o orig]; destruct i; cbn in *; lia.
  - destruct cur as [|c cur]; [destruct i; cbn; lia|]. cbn [length tl] in Hi |- *.
    specialize (R2 (S i) ltac:(cbn; lia)).
    destruct orig as [|o orig]; destruct i; cbn in *; lia.
Qed.

Lemma Rel_refl l : Rel l l.
Proof. split; intros; lia. Qed.

Lemma GPhi_rel a b bs s r : GPhi a b bs s r -> s <= 3 -> forall orig, Rel orig (exs bs) ->
  match r with
  | RE2 k x bs2 s2 => exists h, Rel (skipn (S h) orig) (exs bs2) /\ x <= nth h orig 0 + 1
  | RSp _ _ => True
  end.
Proof.
  induction 1 as [a b bs s bs' s' d r E H IH | a e bs s r H IH | a e bs s bs' s' d E | a | a | a | a r H IH];
    intros Hs orig R; auto.
  - apply IH; [eapply ginc_s3; eauto | eapply Rel_inc; eauto].
  - specialize (IH Hs (tl orig) (Rel_tl _ _ R)). destruct r as [k x bs2 s2|]; [|exact I].
    destruct IH as (h & R1 & R2). exists (S h). split.
    + destruct orig; [destruct h|]; exact R1.
    + destruct orig; cbn in *; [destruct h|]; auto.
  - exists 0. split.
    + apply (Rel_inc _ bs s bs' s' d Hs E). exact (Rel_tl _ _ R).
    + destruct R as [R1 R2]. destruct (ginc_exps bs s Hs _ _ _ E) as [[_ ->] | [_ Ed]].
      * cbn [addb]. destruct bs as [|b bs].
        -- specialize (R2 0 ltac:(cbn; lia)). cbn in R2. lia.
        -- specialize (R1 0 ltac:(cbn; lia)). cbn in R1. lia.
      * destruct bs as [|b bs]; subst d; cbn [addb].
        -- specialize (R2 0 ltac:(cbn; lia)). cbn in R2. lia.
        -- specialize (R1 0 ltac:(cbn; lia)). cbn in R1. lia.
  - apply IH; [lia|]. destruct R as [R1 R2]. split; intros i Hi; cbn in Hi; [lia|].
    destruct i as [|[|i]]; cbn; apply Nat.le_0_l.
Qed.

Lemma GPhi_val a b bs s r : GPhi a b bs s r -> s <= 3 ->
  match r with RE2 k x bs2 s2 => 2 * gval bs2 s2 + a <= gval bs s + k + 2 | RSp _ _ => True end.
Proof.
  induction 1 as [a b bs s bs' s' d r E H IH | a e bs s r H IH | a e bs s bs' s' d E | a | a | a | a r H IH];
    intros Hs; auto.
  - destruct (ginc_val bs s Hs _ _ _ E) as (V & S1 & _). specialize (IH S1). destruct r; [rewrite V in IH; lia | exact I].
  - specialize (IH Hs). destruct r; [cbn [gval]; lia | exact I].
  - destruct (ginc_val bs s Hs _ _ _ E) as (V & _). cbn [gval]. rewrite V. lia.
  - specialize (IH ltac:(lia)). destruct r; [cbn [gval] in *; lia | exact I].
Qed.

(* ===================================================================== *)
(* Section 10. Weights, masses, the threshold, the orbit invariant.        *)
(* ===================================================================== *)

Definition v2 (q : nat) : nat := 2 ^ (q / 2).
Definition p2 (q : nat) : nat := 2 ^ S q.
Definition cst1 (q : nat) : nat := 1.
Definition u1 (l : nat) : nat := match l with 0 => 0 | S l' => 2 * w l' end.
Definition u2 (l : nat) : nat := match l with 0 => 0 | S l' => 2 ^ S l' end.

Lemma v2_mono : mono v2.
Proof. intros i j H. unfold v2. apply Nat.pow_le_mono_r; [lia|]. apply Nat.Div0.div_le_mono; lia. Qed.
Lemma p2_mono : mono p2.
Proof. intros i j H. unfold p2. apply Nat.pow_le_mono_r; lia. Qed.
Lemma cst1_mono : mono cst1.
Proof. intros i j H. unfold cst1. lia. Qed.
Lemma v2_le_w q : v2 q <= w q.
Proof. unfold v2, w. apply Nat.pow_le_mono_r; [lia|]. apply Nat.Div0.div_le_mono; lia. Qed.
Lemma cst1_le_w q : cst1 q <= w q.
Proof. unfold cst1, w. apply Nat.neq_0_lt_0, Nat.pow_nonzero. lia. Qed.

Lemma u1_mono : mono u1.
Proof. intros [|i] [|j] H; cbn [u1]; try lia. pose proof (w_mono i j ltac:(lia)). lia. Qed.
Lemma u1_w l q : 2 * l <= q -> u1 l <= w q.
Proof.
  destruct l as [|l]; intros H; cbn [u1]; [lia|].
  pose proof (w_lev1 l q ltac:(lia)) as W. unfold w at 1.
  rewrite <- Nat.pow_succ_r'.
  apply (Nat.le_trans _ (2 ^ S l)); [|exact W].
  apply Nat.pow_le_mono_r; [lia|].
  destruct l as [|l]; [cbn; lia|].
  assert ((S l + 1) / 2 <= (2 * S l) / 2) by (apply Nat.Div0.div_le_mono; lia).
  rewrite (Nat.mul_comm 2 (S l)), Nat.div_mul in H0 by lia. lia.
Qed.
Lemma u2_mono : mono u2.
Proof. intros [|i] [|j] H; cbn [u2]; try lia. apply Nat.pow_le_mono_r; lia. Qed.
Lemma u2_v2 l q : 2 * l <= q -> u2 l <= v2 q.
Proof.
  destruct l as [|l]; intros H; cbn [u2]; [lia|]. unfold v2. apply Nat.pow_le_mono_r; [lia|].
  replace (S l) with ((2 * S l) / 2) at 1 by (rewrite Nat.mul_comm, Nat.div_mul; lia).
  apply Nat.Div0.div_le_mono; lia.
Qed.

Lemma MO_u1 l es : MO u1 (S l) es = 2 * wpot w 1 0 l es.
Proof. revert l. induction es as [|e es IH]; intros l; cbn [MO wpot]; [reflexivity|]. rewrite IH. cbn [u1]. lia. Qed.
Lemma MO_u1_0 es : MO u1 0 es = 2 * wpot w 1 0 0 (tl es).
Proof. destruct es as [|e es]; cbn [MO tl]; [reflexivity|]. rewrite MO_u1. cbn [u1]. lia. Qed.
Lemma MO_u2 l es : MO u2 (S l) es = wpot p2 1 0 l es.
Proof. revert l. induction es as [|e es IH]; intros l; cbn [MO wpot]; [reflexivity|]. rewrite IH. cbn [u2]. unfold p2. lia. Qed.
Lemma MO_u2_0 es : MO u2 0 es = wpot p2 1 0 0 (tl es).
Proof. destruct es as [|e es]; cbn [MO tl]; [reflexivity|]. rewrite MO_u2. cbn [u2]. lia. Qed.
Lemma nth_le_MO h es : forall l, nth h es 0 <= MO cst1 l es.
Proof.
  revert h. induction es as [|e es IH]; intros h l; [destruct h; cbn; lia|].
  destruct h as [|h]; cbn [nth MO]; unfold cst1 at 1; [lia|]. specialize (IH h (S l)). lia.
Qed.

Lemma wpot_shift v al be f f' l : mono v -> f <= f' -> wpot v al be f l <= wpot v al be f' l.
Proof.
  intros Hv. revert f f'. induction l as [|e l IH]; intros f f' H; cbn [wpot]; [lia|].
  pose proof (Hv f f' H). specialize (IH (S f) (S f') ltac:(lia)).
  assert (v f * (al * e + be) <= v f' * (al * e + be)) by (apply Nat.mul_le_mono_r; lia). lia.
Qed.
Lemma wpot_drop v al be f h l : wpot v al be (f + h) (skipn h l) <= wpot v al be f l.
Proof.
  revert f l. induction h as [|h IH]; intros f l; [rewrite Nat.add_0_r; reflexivity|].
  destruct l as [|e l]; cbn [skipn wpot]; [lia|]. specialize (IH (S f) l).
  replace (f + S h) with (S f + h) by lia. lia.
Qed.
Lemma wpot_skipn_tl v h l : mono v -> wpot v 1 0 0 (skipn (S h) l) <= wpot v 1 0 0 (tl l).
Proof.
  intros Hv. replace (skipn (S h) l) with (skipn h (tl l)) by (destruct l; [destruct h|]; reflexivity).
  apply (Nat.le_trans _ (wpot v 1 0 (0 + h) (skipn h (tl l)))); [apply wpot_shift; [exact Hv | lia]|].
  apply wpot_drop.
Qed.
Lemma wpot_le_nth v l1 : mono v -> forall l2 f, (forall i, nth i l1 0 <= nth i l2 0 + 1) ->
  wpot v 1 0 f l1 <= wpot v 1 0 f l2 + vsum v f (length l1).
Proof.
  intros Hv. induction l1 as [|e1 l1 IH]; intros l2 f H; cbn [wpot length vsum]; [lia|].
  destruct l2 as [|e2 l2].
  - assert (H' : forall i, nth i l1 0 <= nth i [] 0 + 1) by (intros i; specialize (H (S i)); destruct i; cbn in *; lia).
    specialize (IH [] (S f) H'). cbn [wpot] in IH |- *.
    pose proof (H 0) as H0. cbn in H0. assert (v f * (1 * e1 + 0) <= v f) by nia. lia.
  - specialize (IH l2 (S f) (fun i => H (S i))). cbn [wpot].
    pose proof (H 0) as H0. cbn in H0. assert (v f * (1 * e1 + 0) <= v f * (1 * e2 + 0) + v f) by nia. lia.
Qed.
Lemma Rel_nth orig cur : Rel orig cur -> forall i, nth i cur 0 <= nth i orig 0 + 1.
Proof. intros [R1 R2] i. destruct (Nat.lt_ge_cases (S i) (length cur)); [apply R1 | specialize (R2 i)]; lia. Qed.
Lemma wpot_split v al be f l : wpot v al be f l = wpot v al 0 f l + be * vsum v f (length l).
Proof. revert f. induction l as [|e l IH]; intros f; cbn [wpot vsum length]; [lia|]. rewrite IH. ring. Qed.
Lemma wpot_scale2 v f l : wpot v 2 0 f l = 2 * wpot v 1 0 f l.
Proof. revert f. induction l as [|e l IH]; intros f; cbn [wpot]; [lia|]. rewrite IH. ring. Qed.
Lemma wpot_le_v v v' al be f l : (forall q, v q <= v' q) -> wpot v al be f l <= wpot v' al be f l.
Proof.
  intros H. revert f. induction l as [|e l IH]; intros f; cbn [wpot]; [lia|].
  specialize (IH (S f)). assert (v f * (al * e + be) <= v' f * (al * e + be)) by (apply Nat.mul_le_mono_r, H). lia.
Qed.
Lemma vsum_add v f m m' : vsum v f (m + m') = vsum v f m + vsum v (f + m) m'.
Proof. revert f. induction m as [|m IH]; intros f; cbn [vsum Nat.add]; [rewrite Nat.add_0_r; lia|]. rewrite IH. replace (S f + m) with (f + S m) by lia. lia. Qed.
Lemma vsum_mono_m v f m m' : m <= m' -> vsum v f m <= vsum v f m'.
Proof. intros H. replace m' with (m + (m' - m)) by lia. rewrite vsum_add. lia. Qed.
Lemma vsum_cst1 f m : vsum cst1 f m = m.
Proof. revert f. induction m as [|m IH]; intros f; cbn; [reflexivity|]. rewrite IH. unfold cst1. lia. Qed.
Lemma vsum_p2 f m : vsum p2 f m + 2 ^ S f = 2 ^ S (f + m).
Proof.
  revert f. induction m as [|m IH]; intros f; cbn [vsum]; [rewrite Nat.add_0_r; lia|].
  specialize (IH (S f)). replace (f + S m) with (S f + m) by lia. unfold p2 in *. rewrite (Nat.pow_succ_r' 2 (S f)) in IH. lia.
Qed.
Lemma wpot_p2_S f l : wpot p2 1 0 (S f) l = 2 * wpot p2 1 0 f l.
Proof. revert f. induction l as [|e l IH]; intros f; cbn [wpot]; [lia|]. rewrite IH. unfold p2. rewrite (Nat.pow_succ_r' 2 (S f)). ring. Qed.
Lemma qsum_p2 l : 2 * qsum l + 2 = 2 ^ S (length l) + wpot p2 1 0 0 l.
Proof.
  induction l as [|e l IH]; cbn [qsum length wpot]; [cbn; lia|]. rewrite wpot_p2_S.
  change (p2 0) with 2. rewrite (Nat.pow_succ_r' 2 (S (length l))). lia.
Qed.
Lemma wpot_zero v f l : Forall (fun e => e = 0) l -> wpot v 1 0 f l = 0.
Proof. intros H. revert f. induction H as [|e l He H IH]; intros f; cbn; [reflexivity|]. rewrite IH, He. lia. Qed.
Lemma Pot_top v al be ga Ps l : be <= ga -> length l <= Ps ->
  Pot v al be ga Ps 0 l <= wpot v al 0 0 l + ga * vsum v 0 Ps.
Proof.
  intros Hb Hl. unfold Pot. rewrite wpot_split. cbn [Nat.add].
  pose proof (vsum_add v 0 (length l) (Ps - length l)) as E. replace (length l + (Ps - length l)) with Ps in E by lia.
  cbn [Nat.add] in E. rewrite E.
  assert (be * vsum v 0 (length l) <= ga * vsum v 0 (length l)) by (apply Nat.mul_le_mono_r; lia).
  rewrite Nat.mul_add_distr_l. lia.
Qed.

(* ---------- the bound functions (all nondecreasing in kappa) ---------- *)

Definition Ws (P : nat) : nat := vsum w 0 P.
Definition V2s (P : nat) : nat := vsum v2 0 P.
Definition Pf (k : nat) : nat := Nat.max 12 (k + 3).
Definition Af (k : nat) : nat := 5 * Ws (Pf k) + 6 * w (Pf k) + 2 * Ws k.
Definition Bf (k : nat) : nat := Af k + 5 * V2s (Pf k) + 6 * v2 (Pf k) + 2 ^ (k + 1).
Definition Xf (k : nat) : nat := Af k + 5 * Pf k + 7.
Definition Costf (k : nat) : nat := 2 * Xf k + 2 + 2 * Af k + 11 * Ws (Pf k) + 13 * w (Pf k).
Definition Nlo (k : nat) : nat := 2 ^ (k + 3) - 8 * 2 ^ ((Pf k + 3) / 2).
Definition Nstar : nat := 17705.

Lemma Pf_mono k k' : k <= k' -> Pf k <= Pf k'.
Proof. unfold Pf. lia. Qed.
Lemma Ws_mono P P' : P <= P' -> Ws P <= Ws P'.
Proof. apply vsum_mono_m. Qed.
Lemma V2s_mono P P' : P <= P' -> V2s P <= V2s P'.
Proof. apply vsum_mono_m. Qed.
Lemma Af_mono k k' : k <= k' -> Af k <= Af k'.
Proof.
  intros H. unfold Af. pose proof (Pf_mono _ _ H).
  pose proof (Ws_mono _ _ H0). pose proof (w_mono _ _ H0). pose proof (Ws_mono _ _ H). lia.
Qed.

Lemma w_SS q : w (S (S q)) = 2 * w q.
Proof.
  unfold w. replace (S (S q) + 1) with ((q + 1) + 1 * 2) by lia. rewrite Nat.div_add by lia.
  rewrite Nat.pow_add_r. cbn. lia.
Qed.
Lemma v2_SS q : v2 (S (S q)) = 2 * v2 q.
Proof.
  unfold v2. replace (S (S q)) with (q + 1 * 2) by lia. rewrite Nat.div_add by lia.
  rewrite Nat.pow_add_r. cbn. lia.
Qed.
Lemma vsum_SS_w f m : vsum w (S (S f)) m = 2 * vsum w f m.
Proof. revert f. induction m as [|m IH]; intros f; cbn [vsum]; [lia|]. rewrite w_SS, IH. lia. Qed.
Lemma vsum_SS_v2 f m : vsum v2 (S (S f)) m = 2 * vsum v2 f m.
Proof. revert f. induction m as [|m IH]; intros f; cbn [vsum]; [lia|]. rewrite v2_SS, IH. lia. Qed.
Lemma Ws_SS P : Ws (S (S P)) = 2 * Ws P + 3.
Proof. unfold Ws. cbn [vsum]. rewrite vsum_SS_w. cbn. lia. Qed.
Lemma V2s_SS P : V2s (S (S P)) = 2 * V2s P + 2.
Proof. unfold V2s. cbn [vsum]. rewrite vsum_SS_v2. cbn. lia. Qed.
Lemma Pf_big k : 9 <= k -> Pf k = k + 3.
Proof. unfold Pf. lia. Qed.
Lemma Af_SS k : 9 <= k -> Af (S (S k)) = 2 * Af k + 21.
Proof.
  intros H. unfold Af. rewrite !Pf_big by lia.
  replace (S (S k) + 3) with (S (S (k + 3))) by lia. rewrite !Ws_SS, w_SS. lia.
Qed.

Definition gB (k : nat) : nat := Af k + 5 * V2s (k + 3) + 6 * v2 (k + 3).
Lemma gB_SS k : 9 <= k -> gB (S (S k)) = 2 * gB k + 31.
Proof.
  intros H. unfold gB. rewrite Af_SS by lia.
  replace (S (S k) + 3) with (S (S (k + 3))) by lia. rewrite V2s_SS, v2_SS. lia.
Qed.

Lemma gB_all m : gB (10 + 2 * m) + 31 < 7 * 2 ^ (10 + 2 * m) /\ gB (11 + 2 * m) + 31 < 7 * 2 ^ (11 + 2 * m).
Proof.
  induction m as [|m [IH1 IH2]].
  - split; apply Nat.ltb_lt; vm_compute; reflexivity.
  - replace (10 + 2 * S m) with (S (S (10 + 2 * m))) by lia.
    replace (11 + 2 * S m) with (S (S (11 + 2 * m))) by lia.
    rewrite !gB_SS by lia. rewrite !(Nat.pow_succ_r' 2 (S _)), !Nat.pow_succ_r'. lia.
Qed.

Lemma gB_ge k : 10 <= k -> gB k + 31 < 7 * 2 ^ k.
Proof.
  intros H. destruct (Nat.Even_or_Odd (k - 10)) as [[m Hm] | [m Hm]].
  - replace k with (10 + 2 * m) by lia. exact (proj1 (gB_all m)).
  - replace k with (11 + 2 * m) by lia. exact (proj2 (gB_all m)).
Qed.

(* (N1) the Q potential fits below 2^(Pf+1): created positions stay below Pf. *)
Lemma N1 k : 7 * 2 ^ k + Bf k < 2 ^ (Pf k + 1).
Proof.
  destruct (le_lt_dec k 11) as [Hk|Hk].
  - assert (H : forallb (fun k => 7 * 2 ^ k + Bf k <? 2 ^ (Pf k + 1)) (seq 0 12) = true) by (vm_compute; reflexivity).
    rewrite forallb_forall in H. specialize (H k (proj2 (in_seq 12 0 k) ltac:(lia))). apply Nat.ltb_lt, H.
  - pose proof (gB_ge k ltac:(lia)) as G. unfold Bf. fold (gB k) in *.
    unfold gB in G. rewrite Pf_big in * by lia. unfold gB in *.
    replace (k + 3 + 1) with (k + 4) by lia. rewrite (Nat.pow_add_r 2 k 4), (Nat.pow_add_r 2 k 1).
    cbn [Nat.pow]. lia.
Qed.

Lemma Costf_SS k : 9 <= k -> Costf (S (S k)) + 10 * (k + 3) = 2 * Costf k + 121.
Proof.
  intros H. unfold Costf, Xf. rewrite Af_SS by lia. rewrite !Pf_big by lia.
  replace (S (S k) + 3) with (S (S (k + 3))) by lia. rewrite Ws_SS, w_SS. generalize (Af k) (Ws (k + 3)) (w (k + 3)). intros. lia.
Qed.

Lemma Nlo_SS k : 9 <= k -> Nlo (S (S k)) = 4 * 2 ^ (k + 3) - 16 * 2 ^ ((k + 6) / 2) /\
  Nlo k = 2 ^ (k + 3) - 8 * 2 ^ ((k + 6) / 2).
Proof.
  intros H. unfold Nlo. rewrite !Pf_big by lia. split.
  - replace ((S (S k) + 3 + 3) / 2) with ((k + 6) / 2 + 1)
      by (replace (S (S k) + 3 + 3) with ((k + 6) + 1 * 2) by lia; rewrite Nat.div_add by lia; lia).
    replace (S (S k) + 3) with (k + 3 + 2) by lia.
    rewrite (Nat.pow_add_r 2 (k + 3) 2), (Nat.pow_add_r 2 ((k + 6) / 2) 1).
    generalize (2 ^ (k + 3)) (2 ^ ((k + 6) / 2)). intros. cbn. lia.
  - replace (k + 3 + 3) with (k + 6) by lia. reflexivity.
Qed.

Lemma D_all m : Costf (12 + 2 * m) + 123 <= Nlo (12 + 2 * m) /\ Costf (13 + 2 * m) + 123 <= Nlo (13 + 2 * m).
Proof.
  induction m as [|m [IH1 IH2]].
  - split; apply Nat.leb_le; vm_compute; reflexivity.
  - replace (12 + 2 * S m) with (S (S (12 + 2 * m))) by lia.
    replace (13 + 2 * S m) with (S (S (13 + 2 * m))) by lia.
    pose proof (Costf_SS (12 + 2 * m) ltac:(lia)). pose proof (Costf_SS (13 + 2 * m) ltac:(lia)).
    destruct (Nlo_SS (12 + 2 * m) ltac:(lia)) as [E1 E2]. destruct (Nlo_SS (13 + 2 * m) ltac:(lia)) as [E3 E4].
    rewrite E1, E3. rewrite E2 in IH1. rewrite E4 in IH2. lia.
Qed.

(* (N2) the digestion cost fits in the budget: below N* for kappa <= 11, below Nlo above. *)
Lemma N2 k : Costf k + 2 <= Nstar \/ Costf k + 2 <= Nlo k.
Proof.
  destruct (le_lt_dec k 11) as [Hk|Hk].
  - left. assert (H : forallb (fun k => Costf k + 2 <=? Nstar) (seq 0 12) = true) by (vm_compute; reflexivity).
    rewrite forallb_forall in H. specialize (H k (proj2 (in_seq 12 0 k) ltac:(lia))). apply Nat.leb_le, H.
  - right. destruct (Nat.Even_or_Odd (k - 12)) as [[m Hm] | [m Hm]].
    + replace k with (12 + 2 * m) by lia. pose proof (proj1 (D_all m)). lia.
    + replace k with (13 + 2 * m) by lia. pose proof (proj2 (D_all m)). lia.
Qed.

(* ===================================================================== *)
(* Section 11. The orbit invariant, one epoch, the finite part, nonhalt.  *)
(* ===================================================================== *)

Lemma Nstar_ge : 15 <= Nstar.
Proof. apply Nat.leb_le. vm_compute. reflexivity. Qed.

Ltac opq t := let x := fresh "o" in set (x := t) in *; clearbody x.

Definition Mw (bs : blks) : nat := wpot w 1 0 0 (exs bs).
Definition M2 (bs : blks) : nat := wpot p2 1 0 0 (exs bs).

(* Inv k N y: epoch K(1,N,y), k bounds the number of blocks seen so far (write-up D.6). *)
Definition Inv (k N : nat) (y : word) : Prop :=
  Nstar <= N /\ Nlo k <= N /\
  ((exists x bs s, y = p11 x (gw bs s) /\ s <= 3 /\ length bs <= k /\
      Mw bs <= Af k /\ M2 bs <= Bf k /\ x <= Xf k)
   \/ y = t1 \/ y = p01 1 t1 \/ y = p10 (p00 t2)).

Lemma next_inv k N n c bsp sp r :
  GPhi (1 + n) (N + c - n) bsp sp r -> sp <= 3 -> n + 2 <= N -> Nstar <= N -> Nlo k <= N ->
  MO u1 0 (exs bsp) <= Af k + 5 * Ws (Pf k) + 6 * w (Pf k) ->
  MO u2 0 (exs bsp) <= Af k + 5 * V2s (Pf k) + 6 * v2 (Pf k) ->
  MO cst1 0 (exs bsp) + 1 <= Xf k ->
  2 * length bsp <= Pf k + 3 ->
  exists k', Inv k' (S (rk r)) (ry r).
Proof.
  intros HG Hs Hn HN HL H1 H2 H3 H4.
  pose proof (GPhi_rk _ _ _ _ _ HG) as Hrk.
  pose proof (GPhi_s3 _ _ _ _ _ HG Hs) as Hr.
  pose proof (GPhi_rel _ _ _ _ _ HG Hs (exs bsp) (Rel_refl _)) as HR.
  pose proof (GPhi_val _ _ _ _ _ HG Hs) as HV.
  destruct r as [kk x bs2 s2 | kk y]; cbn [rk ry] in *.
  - destruct HR as (h & R1 & R2).
    exists (Nat.max k (length bs2)).
    assert (Hk : k <= Nat.max k (length bs2)) by lia.
    assert (Hk2 : length bs2 <= Nat.max k (length bs2)) by lia.
    set (k' := Nat.max k (length bs2)) in *.
    split; [lia|]. split.
    + destruct (le_lt_dec (length bs2) k) as [Hle|Hgt].
      * replace k' with k by lia. lia.
      * replace k' with (length bs2) by lia.
        pose proof (gval_lb bs2 s2). pose proof (gval_ub bsp sp Hs).
        assert (2 ^ length bsp <= 2 ^ ((Pf (length bs2) + 3) / 2)).
        { apply Nat.pow_le_mono_r; [lia|]. pose proof (Pf_mono k (length bs2) ltac:(lia)).
          apply Nat.div_le_lower_bound; lia. }
        unfold Nlo. rewrite Nat.pow_add_r.
        generalize dependent (2 ^ length bs2). generalize dependent (2 ^ length bsp).
        generalize dependent (2 ^ ((Pf (length bs2) + 3) / 2)). intros. cbn [Nat.pow] in *. lia.
    + left. exists x, bs2, s2. split; [reflexivity|]. split; [exact Hr|]. split; [lia|].
      pose proof (Pf_mono _ _ Hk) as HPf.
      split; [|split].
      * unfold Mw.
        pose proof (wpot_le_nth w (exs bs2) w_mono _ 0 (Rel_nth _ _ R1)) as A1. rewrite length_exs in A1.
        pose proof (wpot_skipn_tl w h (exs bsp) w_mono) as A2.
        rewrite MO_u1_0 in H1.
        pose proof (Ws_mono _ _ Hk2). pose proof (Ws_mono _ _ Hk). pose proof (Ws_mono _ _ HPf).
        pose proof (w_mono _ _ HPf).
        unfold Af in *. fold (Ws (length bs2)) in A1.
        generalize dependent (wpot w 1 0 0 (exs bs2)). generalize dependent (wpot w 1 0 0 (skipn (S h) (exs bsp))).
        generalize dependent (wpot w 1 0 0 (tl (exs bsp))). intros. lia.
      * unfold M2.
        pose proof (wpot_le_nth p2 (exs bs2) p2_mono _ 0 (Rel_nth _ _ R1)) as A1. rewrite length_exs in A1.
        pose proof (wpot_skipn_tl p2 h (exs bsp) p2_mono) as A2.
        rewrite MO_u2_0 in H2.
        pose proof (vsum_p2 0 (length bs2)) as A3. cbn [Nat.add] in A3.
        assert (2 ^ S (length bs2) <= 2 ^ (k' + 1)) by (apply Nat.pow_le_mono_r; lia).
        pose proof (Af_mono _ _ Hk). pose proof (V2s_mono _ _ HPf). pose proof (v2_mono _ _ HPf).
        unfold Bf.
        generalize dependent (wpot p2 1 0 0 (exs bs2)). generalize dependent (wpot p2 1 0 0 (skipn (S h) (exs bsp))).
        generalize dependent (wpot p2 1 0 0 (tl (exs bsp))). intros. lia.
      * pose proof (nth_le_MO h (exs bsp) 0).
        assert (Xf k <= Xf k') by (unfold Xf; pose proof (Af_mono _ _ Hk); lia). lia.
  - exists k. split; [lia|]. split; [lia|]. right. exact Hr.
Qed.

Lemma inv_step k N y : Inv k N y -> exists kk y', Phi 1 N y kk y' /\ exists k', Inv k' (S kk) y'.
Proof.
  intros (HN & HL & Hy).
  pose proof (N2 k) as HC.
  destruct Hy as [(x & bs & s & -> & Hs & Hk & HM & HM2 & Hx) | Hsp].
  - set (Ps := Pf k).
    set (Q0 := Qp 0 bs s 0 - 3 * 2 ^ length bs).
    assert (HQ0 : 4 * 2 ^ length bs <= Qp 0 bs s 0).
    { unfold Qp. rewrite Nat.pow_0_r. pose proof (gval_lb bs s). lia. }
    assert (HQ : QI Q0 0 bs s 0).
    { unfold QI, Q0. cbn [Nat.add]. clear - HQ0. lia. }
    assert (HP : Q0 < 2 ^ (Ps + 1)).
    { pose proof (N1 k) as N1k. unfold Q0, Qp. rewrite Nat.pow_0_r, Nat.mul_1_l.
      pose proof (qsum_p2 (exs bs)) as QP. rewrite length_exs in QP. pose proof (gval_ub bs s Hs).
      assert (2 ^ length bs <= 2 ^ k) by (apply Nat.pow_le_mono_r; lia). unfold M2 in HM2.
      rewrite Nat.pow_succ_r' in QP. fold Ps in N1k. lia. }
    destruct (DigT_exists Q0 (Q0 + 1) 0 bs s Hs HQ ltac:(lia)) as (n0 & c0 & bsp & sp & HT).
    pose proof (DP x _ _ _ _ _ _ HT) as HD.
    set (n := 2 * x + 2 + n0) in *. set (c := S x + c0) in *.
    pose proof (proj1 (Dig_cost Q0 Ps HP) _ _ _ _ _ _ _ HD Hs 0 0 (le_n _) HQ) as Hcost.
    rewrite Nat.pow_0_r, !Nat.mul_1_l in Hcost.
    pose proof (QI_Ps _ Ps _ _ _ _ HQ HP) as HPs. cbn [Nat.add] in HPs.
    assert (HPs' : length (exs bs) <= Ps) by (rewrite length_exs; exact HPs).
    pose proof (Pot_top w 2 8 11 Ps (exs bs) ltac:(lia) HPs') as PT. rewrite wpot_scale2 in PT.
    assert (Hn : n + 2 <= N).
    { unfold Costf in HC. fold Ps in HC. unfold Mw in HM. fold (Ws Ps) in PT.
      opq (w Ps). opq (Ws Ps). opq (Pot w 2 8 11 Ps 0 (exs bs)). opq (wpot w 1 0 0 (exs bs)). lia. }
    pose proof (proj1 Dig_sp _ _ _ _ _ _ _ HD) as Hsp.
    destruct (gcount (Psi bsp sp (N + c - n)) bsp sp (1 + n) (N + c - n) Hsp ltac:(lia) (le_n _)) as (r & HG).
    exists (rk r), (ry r). split; [exact (epoch_ord N x bs s n c bsp sp r Hs HD Hn HG)|].
    apply (next_inv k N n c bsp sp r HG Hsp Hn HN HL).
    + pose proof (proj1 (Dig_mass u1 w Q0 Ps w_mono u1_mono u1_w HP) _ _ _ _ _ _ _ HD Hs 0 0 (le_n _) HQ) as Hm.
      cbn [pu] in Hm. pose proof (Pot_top w 1 3 5 Ps (exs bs) ltac:(lia) HPs') as PT1.
      unfold Mw in HM. fold Ps. fold (Ws Ps) in PT1.
      opq (w Ps). opq (Ws Ps). opq (Pot w 1 3 5 Ps 0 (exs bs)). opq (wpot w 1 0 0 (exs bs)). opq (MO u1 0 (exs bsp)). lia.
    + pose proof (proj1 (Dig_mass u2 v2 Q0 Ps v2_mono u2_mono u2_v2 HP) _ _ _ _ _ _ _ HD Hs 0 0 (le_n _) HQ) as Hm.
      cbn [pu] in Hm. pose proof (Pot_top v2 1 3 5 Ps (exs bs) ltac:(lia) HPs') as PT1.
      pose proof (wpot_le_v v2 w 1 0 0 (exs bs) v2_le_w).
      unfold Mw in HM. fold Ps. fold (V2s Ps) in PT1.
      opq (v2 Ps). opq (V2s Ps). opq (Pot v2 1 3 5 Ps 0 (exs bs)). opq (wpot w 1 0 0 (exs bs)).
      opq (wpot v2 1 0 0 (exs bs)). opq (MO u2 0 (exs bsp)). lia.
    + pose proof (proj1 (Dig_mass cst1 cst1 Q0 Ps cst1_mono cst1_mono ltac:(intros; unfold cst1; lia) HP)
        _ _ _ _ _ _ _ HD Hs 0 0 (le_n _) HQ) as Hm.
      cbn [pu] in Hm. pose proof (Pot_top cst1 1 3 5 Ps (exs bs) ltac:(lia) HPs') as PT1.
      rewrite vsum_cst1 in PT1. pose proof (wpot_le_v cst1 w 1 0 0 (exs bs) cst1_le_w).
      unfold Mw in HM. unfold Xf. fold Ps. unfold cst1 at 3 in Hm.
      opq (Pot cst1 1 3 5 Ps 0 (exs bs)). opq (wpot w 1 0 0 (exs bs)). opq (wpot cst1 1 0 0 (exs bs)).
      opq (MO cst1 0 (exs bsp)). lia.
    + pose proof (proj1 (Dig_len Q0 Ps HP) _ _ _ _ _ _ _ HD Hs 0 0 (le_n _) HQ). fold Ps. lia.
  - destruct (DigE_ex y Hsp) as (n & c & bsp & sp & HE).
    destruct (DigE_props _ _ _ _ _ HE) as (Hn13 & Hc5 & Hb1 & Hs3 & Hz).
    assert (Hn : n + 2 <= N) by (pose proof Nstar_ge; lia).
    destruct (gcount (Psi bsp sp (N + c - n)) bsp sp (1 + n) (N + c - n) Hs3 ltac:(lia) (le_n _)) as (r & HG).
    exists (rk r), (ry r). split; [exact (epoch_spec N y n c bsp sp r HE Hn HG)|].
    apply (next_inv k N n c bsp sp r HG Hs3 Hn HN HL); rewrite ?(MO_zero _ _ _ Hz); unfold Xf, Pf; lia.
Qed.

(* ---------- the finite part: the computable model from K(1,8,t2) to epoch 694 ---------- *)

Fixpoint orbit (f n N : nat) (y : word) : option (nat * word) :=
  match n with
  | O => Some (N, y)
  | S n => match phif f 1 N y with Some (k, y') => orbit f n (S k) y' | None => None end
  end.

Lemma orbit_sound f n : forall N y N' y', orbit f n N y = Some (N', y') -> K N y -->* K N' y'.
Proof.
  induction n as [|n IH]; intros N y N' y' H; cbn [orbit] in H.
  - inversion H; subst. apply evstep_refl.
  - destruct (phif f 1 N y) as [[k y1]|] eqn:E; [|discriminate].
    eapply evstep_trans; [apply progress_evstep, epoch_tm, (proj2 (model_sound f) _ _ _ _ _ E) | exact (IH _ _ _ _ H)].
Qed.

Definition B694 : blks := [(false, 17); (true, 1); (true, 1); (true, 1); (true, 1);
  (false, 1); (false, 1); (false, 1); (true, 1); (false, 0)].
Definition Y694 : word := p11 7 (gw B694 0).

Lemma fin694 : orbit 100000 691 8 t2 = Some (17713, Y694).
Proof. vm_compute. reflexivity. Qed.

Lemma inv694 : Inv 10 17713 Y694.
Proof.
  unfold Inv. split; [apply Nat.leb_le; vm_compute; reflexivity|]. split; [apply Nat.leb_le; vm_compute; reflexivity|].
  left. exists 7, B694, 0. split; [reflexivity|]. split; [lia|]. split; [cbn; lia|].
  split; [|split]; [apply Nat.leb_le; vm_compute; reflexivity | apply Nat.leb_le; vm_compute; reflexivity |].
  apply Nat.leb_le; vm_compute; reflexivity.
Qed.

Lemma nonhalt_from N0 y0 (P : nat -> word -> Prop) :
  c0 -->* K N0 y0 -> P N0 y0 ->
  (forall N y, P N y -> exists k y', Phi 1 N y k y' /\ P (S k) y') ->
  ~ halts tm c0.
Proof.
  intros H0 HP0 Hstep.
  eapply multistep_nonhalt. { exact H0. }
  apply (progress_nonhalt_cond tm (nat * word) (N0, y0) (fun i => K (fst i) (snd i))
           (fun i => P (fst i) (snd i))); [| exact HP0].
  intros [N y] HP. cbn in HP.
  destruct (Hstep N y HP) as (k & y' & HPhi & HP').
  exists (S k, y'). split; [apply epoch_tm, HPhi | exact HP'].
Qed.

Lemma nonhalt: ~halts tm c0.
Proof.
  apply (nonhalt_from 17713 Y694 (fun N y => exists k, Inv k N y)).
  - eapply evstep_trans; [exact init | exact (orbit_sound _ _ _ _ _ _ fin694)].
  - exists 10. exact inv694.
  - intros N y [k Hk]. destruct (inv_step k N y Hk) as (kk & y' & H1 & H2). exists kk, y'. split; [exact H1 | exact H2].
Qed.

(*
      0     1
 A   1RB   0RF
 B   1RC   1RF
 C   1LD   0RE
 D   ---   0LE
 E   1LA   0LE
 F   0RA   0LC

 hub        K(a,b,X) = 0^inf (110)^a 0 (011)^b C> X 0^inf
 pre-record L'(k,T)  = 0^inf E> 0 01 (001)^k T 0^inf      (E0 = 1LA, then the restart)
 start      c0 -->* K(1,8,010001)
*)
