Require Import VST.veric.SeparationLogic.
Require Import VST.concurrency.common.lksize.

Section mpred.

Context `{heapGS Σ}.

Definition exclusive_mpred R : mpred := ((R ∗ R) -∗ False)%I.

Record lock_handle := { lock_address : address; lock_index : positive }.

Definition lock_inv sh h R : mpred := LKspec LKSIZE sh (lock_address h) ∗
  ownI (lock_index h) R.

Definition rec_inv sh v (Q R: mpred): mpred := (R ∗-∗ Q ∗ ▷ lock_inv sh v R)%I.

#[global] Instance lock_inv_nonexpansive sh v : NonExpansive (lock_inv sh v).
Proof. solve_proper. Qed.

End mpred.
