(** * The Odometer: 1RB1LC_1RC1RE_1LD1LF_---0LE_1RB0RB_0LF1LA *)

(** BB(6) holdout. Non-halt argument: notes/odometer.md in this repo.
    Proof plan (M4): startup -> structured-era sweep lemmas -> the descent
    -> crisis -> regime-3 sweep lemmas -> the melt lemma -> stationary
    meta-cycle W(n) -->+ W(n+1), closed by progress_nonhalt_simple. *)

From BusyCoq Require Import Individual62.
From Coq Require Import Lia.
Set Default Goal Selector "!".

Definition tm : TM := fun '(q, s) =>
  match q, s with
  | A, 0 => Some (1, R, B)  | A, 1 => Some (1, L, C)
  | B, 0 => Some (1, R, C)  | B, 1 => Some (1, R, E)
  | C, 0 => Some (1, L, D)  | C, 1 => Some (1, L, F)
  | D, 0 => None            | D, 1 => Some (0, L, E)
  | E, 0 => Some (1, R, B)  | E, 1 => Some (0, R, B)
  | F, 0 => Some (0, L, F)  | F, 1 => Some (1, L, A)
  end.

Notation "c --> c'" := (c -[ tm ]-> c')   (at level 40).
Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

(** The anchor: state C at the right edge of the written tape, facing the
    blank half. All macro-level bookkeeping (SPELL, the clock) is stated at
    anchors; ground truth from tools/regime3b.mjs and friends. *)

Lemma startup : c0 -->* const 0 <* <[1; 1; 0; 1; 0; 1; 1; 1] {{C}}> const 0.
Proof. execute. Qed.

(** Raw shift rules — the atoms the k=4 glyph lemmas compile down to. *)

(** B eats 11-pairs rightward, leaving 10-pairs: the O-glyph writer. *)
Lemma B_pairs : forall n l r,
  l {{B}}> [1; 1]^^n *> r -->* l <* <[1; 0]^^n {{B}}> r.
Proof.
  induction n.
  - triv.
  - execute.
    change (0 >> 1 >> ([0; 1]^^n *> l)) with ([0; 1] *> [0; 1]^^n *> l).
    rewrite <- lpow_shift'.
    follow IHn. finish.
Qed.

(** F slides leftward over zeros unchanged. *)
Lemma F_zeros : forall n l r,
  l <* <[0]^^n <{{F}} r -->* l <{{F}} [0]^^n *> r.
Proof.
  induction n.
  - triv.
  - execute.
    change (0 >> ([0]^^n *> r)) with ([0] *> [0]^^n *> r).
    rewrite <- lpow_shift'.
    follow IHn. finish.
Qed.

(** * The glyph layer.

    A k=4 block of value `1x1y` is written on tape as `y1x1` (bits
    reversed). Glyph spellings left-to-right, ground truth from
    tools/rawrules.mjs (P-2026-08-14-m):
      O = 0101   e = 0111   a = 1101   f = 1111
    A sweep crosses the tail four times, 4 raw steps per block per pass:
    F-down (e preserved), E-up (e -> a), C-down (a preserved),
    E-up (a -> e). The E-pass is the ink-neutral e/a swap primitive. *)

(** Pass 1: F walks left over e-blocks, byte-preserved. *)
Lemma F_es_left : forall n l r,
  l <* <[0; 1; 1; 1]^^n <{{F}} r -->* l <{{F}} [0; 1; 1; 1]^^n *> r.
Proof.
  induction n.
  - triv.
  - execute.
    change (0 >> 1 >> 1 >> 1 >> ([0; 1; 1; 1]^^n *> r))
      with ([0; 1; 1; 1] *> [0; 1; 1; 1]^^n *> r).
    rewrite <- lpow_shift'.
    follow IHn. finish.
Qed.

(** Pass 2: E walks right over e-blocks, converting each to a. *)
Lemma E_es_right : forall n l r,
  l {{E}}> [0; 1; 1; 1]^^n *> r -->* l <* <[1; 1; 0; 1]^^n {{E}}> r.
Proof.
  induction n.
  - triv.
  - execute.
    change (1 >> 0 >> 1 >> 1 >> ([1; 0; 1; 1]^^n *> l))
      with ([1; 0; 1; 1] *> [1; 0; 1; 1]^^n *> l).
    rewrite <- lpow_shift'.
    follow IHn. finish.
Qed.

(** Pass 3: C walks left over a-blocks, byte-preserved. *)
Lemma C_as_left : forall n l r,
  l <* <[1; 1; 0; 1]^^n <{{C}} r -->* l <{{C}} [1; 1; 0; 1]^^n *> r.
Proof.
  induction n.
  - triv.
  - execute.
    change (1 >> 1 >> 0 >> 1 >> ([1; 1; 0; 1]^^n *> r))
      with ([1; 1; 0; 1] *> [1; 1; 0; 1]^^n *> r).
    rewrite <- lpow_shift'.
    follow IHn. finish.
Qed.

(** Pass 4: E walks right over a-blocks, converting each back to e. *)
Lemma E_as_right : forall n l r,
  l {{E}}> [1; 1; 0; 1]^^n *> r -->* l <* <[0; 1; 1; 1]^^n {{E}}> r.
Proof.
  induction n.
  - triv.
  - execute.
    change (1 >> 1 >> 1 >> 0 >> ([1; 1; 1; 0]^^n *> l))
      with ([1; 1; 1; 0] *> [1; 1; 1; 0]^^n *> l).
    rewrite <- lpow_shift'.
    follow IHn. finish.
Qed.

(** * Single-block primitives.

    The E-crossing generalizes: over ANY glyph y1x1 it toggles both free
    bits (value b -> b XOR 5): e<->a and O<->f. The respell machinery,
    the tail round-trip, and the zone increment are this one rule. *)

Definition nsym (s : sym) : sym :=
  match s with S0 => S1 | S1 => S0 end.

Lemma E_glyph_right : forall (x y : sym) l r,
  l {{E}}> y >> 1 >> x >> 1 >> r -->*
  l << nsym y << 1 << nsym x << 1 {{E}}> r.
Proof. destruct x, y; execute. Qed.

(** Left-walk phase over the zone's spelled cells: the F/A/C cycle
    advances one phase per 1-cell; which state enters decides the exit. *)
Lemma C_f_left1 : forall l r,
  l <* <[1; 1; 1; 1] <{{C}} r -->* l <{{F}} [1; 1; 1; 1] *> r.
Proof. execute. Qed.

Lemma F_f_left1 : forall l r,
  l <* <[1; 1; 1; 1] <{{F}} r -->* l <{{A}} [1; 1; 1; 1] *> r.
Proof. execute. Qed.

(** Zone cell 0 on entry: A converts O to f and passes on as C. *)
Lemma A_O_left1 : forall l r,
  l <* <[0; 1; 0; 1] <{{A}} r -->* l <{{C}} [1; 1; 1; 1] *> r.
Proof. execute. Qed.

(** The deepest dipped cell reflects the head: F hits a glyph with x=0
    (an even window value), the carry lands (+1: O->e, a->f), and the
    out-walk begins in E. One rule for both, y-independent. *)
Lemma F_x0_bounce : forall (y : sym) l r,
  l <* <[y; 1; 0; 1] <{{F}} r -->* l <* <[y; 1; 1; 1] {{E}}> r.
Proof. destruct y; execute. Qed.

(** * The edge of the world (the tail's +1).

    Sweep start: the edge O becomes e (joining the tail) and the virgin
    block is stamped 1000; the down-walk begins. *)
Lemma edge_start : forall l,
  l <* <[0; 1; 0; 1] {{C}}> const 0 -->*
  l <* <[0; 1; 1; 1] {{C}}> 1 >> const 0.
Proof. execute. Qed.

(** The up-walk hits the virgin block (1000) and reflects as C, leaving
    1110 — the half-built next edge. *)
Lemma virgin_reflect : forall l r,
  l {{E}}> 1 >> 0 >> 0 >> 0 >> r -->* l <{{C}} 1 >> 1 >> 1 >> 0 >> r.
Proof. execute. Qed.

(** Same, phrased against the blank half — the form composition wants
    (unification will not unfold [const 0] to expose the three zeros). *)
Lemma virgin_reflect0 : forall l,
  l {{E}}> 1 >> const 0 -->* l <{{C}} 1 >> 1 >> 1 >> 0 >> const 0.
Proof. execute. Qed.

(** The second down-walk bounces off the separator (O-spelled since the
    first up-walk toggled it), restoring f and turning as E. *)
Lemma sep_bounce : forall l r,
  l <* <[0; 1; 0; 1] <{{C}} r -->* l <* <[1; 1; 1; 1] {{E}}> r.
Proof. execute. Qed.

(** The final up-walk finishes the virgin block into a fresh edge O and
    lands at the next anchor. *)
Lemma virgin_finish : forall l r,
  l {{E}}> 1 >> 1 >> 1 >> 0 >> r -->* l <* <[0; 1; 0; 1] {{C}}> r.
Proof. execute. Qed.

(** * The even sweep.

    At an anchor with bit0 clear (zone cells 1 and 0 both O), one sweep
    sets bit0 (cell 1 becomes f) and grows the tail by one e. Tape
    left-to-right: zc | cell1 | cell0 | separator f | tail e^n | edge O. *)
Lemma sweep_even : forall zc n,
  zc <* <[0;1;0;1] <* <[0;1;0;1] <* <[1;1;1;1] <* <[0;1;1;1]^^n <* <[0;1;0;1]
    {{C}}> const 0 -->*
  zc <* <[1;1;1;1] <* <[0;1;0;1] <* <[1;1;1;1] <* <[0;1;1;1]^^(S n) <* <[0;1;0;1]
    {{C}}> const 0.
Proof.
  introv.
  follow edge_start.
  step.
  follow (F_es_left (S n)).
  follow F_f_left1.
  follow A_O_left1.
  follow sep_bounce.
  follow (E_glyph_right 1 1).
  follow (E_glyph_right 1 1).
  follow (E_es_right (S n)).
  follow virgin_reflect0.
  follow (C_as_left (S n)).
  follow sep_bounce.
  follow (E_as_right (S n)).
  follow virgin_finish.
  finish.
Qed.

(** * The shallow odd sweep.

    At an anchor with bit0 set (cell 1 = f) and an even window at cell 2
    (x-bit clear: O or a), one sweep clears bit0 and lands the carry in
    cell 2 (window +1). Left-to-right:
    zc | cell2 = y1x1, x=0 | cell1 f | cell0 O | sep f | e^n | edge O. *)
Lemma sweep_odd_shallow : forall zc (y2 : sym) n,
  zc <* <[y2;1;0;1] <* <[1;1;1;1] <* <[0;1;0;1] <* <[1;1;1;1]
     <* <[0;1;1;1]^^n <* <[0;1;0;1] {{C}}> const 0 -->*
  zc <* <[y2;1;1;1] <* <[0;1;0;1] <* <[0;1;0;1] <* <[1;1;1;1]
     <* <[0;1;1;1]^^(S n) <* <[0;1;0;1] {{C}}> const 0.
Proof.
  introv.
  follow edge_start.
  step.
  follow (F_es_left (S n)).
  follow F_f_left1.
  follow A_O_left1.
  follow C_f_left1.
  follow (F_x0_bounce y2).
  follow (E_glyph_right 1 1).
  follow (E_glyph_right 1 1).
  follow (E_glyph_right 1 1).
  follow (E_es_right (S n)).
  follow virgin_reflect0.
  follow (C_as_left (S n)).
  follow sep_bounce.
  follow (E_as_right (S n)).
  follow virgin_finish.
  finish.
Qed.
