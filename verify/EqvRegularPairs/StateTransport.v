(** Reuse the repository's native state-renaming theorem. *)
From BusyCoq Require Import Individual62 RegularInvariant62.
Definition transport (f : state6 -> state6) (c : state6 * RI.tape) :=
  match c with (q,t) => (f q,t) end.
Definition renames (src dst : RI.TM) (f : state6 -> state6) : Prop :=
  Individual62.Enumerate.Permute.Perm src dst f.
Theorem transport_halts src dst f c : renames src dst f ->
  RI.halts src c -> RI.halts dst (transport f c).
Proof.
  destruct c as [q t]. exact (Individual62.Enumerate.Permute.perm_halts src dst f q t).
Qed.
Print Assumptions transport_halts.
