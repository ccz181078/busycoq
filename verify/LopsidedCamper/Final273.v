(** The chain of kernel jobs gives the halt of the raw machine from the blank tape. *)
From BusyCoq Require Import Individual62.
From BusyCoq.LopsidedCamper Require Import Rules273 Kernel273.

Theorem halts_of_chain: chain i0 i1 i0 -> halts tm c0.
Proof.
  intros H. destruct (chain_iter _ _ _ H) as [N HN].
  apply (halts_of_orbit N). exact HN.
Qed.
Print Assumptions halts_of_chain.
