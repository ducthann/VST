Require Import VST.veric.SeparationLogic.
Require Import VST.concurrency.common.lksize.
Require Import VST.concurrency.common.permissions.
(*From iris_ora.logic Require Import cancelable_invariants.*)
From iris_ora.algebra Require Import gmap_view.

(* up *)
Definition Mem_load_unchecked (chunk : memory_chunk) (m : mem) (b : Values.block) (ofs : Z) :=
    decode_val chunk (Mem.getN (size_chunk_nat chunk) ofs (PMap.get b (Mem.mem_contents m))).

    Definition Mem_store_unchecked_contents
      (chunk : memory_chunk) (m : mem) (b : Values.block) (ofs : Z) (v : val) :=
      PMap.set b
        (Mem.setN
           (encode_val chunk v)
           ofs
           (PMap.get b (Mem.mem_contents m)))
        (Mem.mem_contents m).

    Program Definition Mem_store_unchecked
      (chunk : memory_chunk) (m : mem) (b : Values.block) (ofs : Z) (v : val) :=
        Mem.mkmem
           (Mem_store_unchecked_contents chunk m b ofs v)
           (Mem.mem_access m)
           (Mem.nextblock m)
           _
           _
           _.
    Next Obligation. intros; apply Mem.access_max. Qed.
    Next Obligation. by intros; apply Mem.nextblock_noaccess. Qed.
    Next Obligation.
      intros; unfold Mem_store_unchecked_contents.
      destruct (Coqlib.peq b0 b); subst.
      - rewrite PMap.gss.
        rewrite Mem.setN_default.
        by rewrite Mem.contents_default.
      - rewrite PMap.gso; auto.
        by rewrite Mem.contents_default.
    Qed.

    Definition lock_addresses_disjoint (ls : gset address) : Prop :=
      forall l k, l ∈ ls -> k ∈ ls ->
             l <> k -> k.1 <> l.1 \/
               (k.2 + size_chunk Mptr <= l.2 \/ l.2 + size_chunk Mptr <= k.2)%Z.
    
Section mpred.

Context `{!heapGS Σ}.

Definition exclusive_mpred R : mpred := □ ((R ∗ R) -∗ False)%I.

(* Here's a version that uses global invariants.

Context {!cinvG Σ}.

Record lock_handle := { lock_address : address; lock_gname : gname }.

Definition lockN := nroot .@ "lock".

Definition lock_inv_pred l R := ∃ b : bool, address_mapsto Mptr (if b then Vptrofs (Ptrofs.one) else Vptrofs (Ptrofs.zero)) Ews l ∗
  if b then R else emp.

Definition lock_inv sh h R : mpred := (*LKspec LKSIZE sh (lock_address h) ∗
  ownI (lock_index h) R*)
  cinv lockN (lock_gname h) (lock_inv_pred (lock_address h) R) ∗
  cinv_own (lock_gname h) sh.
  (* if this works, remove LK resources from res_predicates *)
  (* This runs into the usual questions about invariants. Under a fancy update, we can
     prove that the rmap includes ownership of the lock location and (if the lock isn't held) R,
     which would imply that the thread has permission to them. If a lock protects a location
     and all threads with access to that lock have Writable permission to that location,
     then the program isn't permission-well-synchronized. But the meaning of fancy update
     is "if we're given wsat", which might be enough to avoid trouble. Certainly if we
     only access wsat during lock operations, that should be safe.
  *)

Definition rec_inv sh v (Q R: mpred): mpred := (R ∗-∗ Q ∗ ▷ lock_inv sh v R)%I.

#[global] Instance lock_inv_pred_nonexpansive l : NonExpansive (lock_inv_pred l).
Proof. solve_proper. Qed.

#[global] Instance lock_inv_nonexpansive sh v : NonExpansive (lock_inv sh v).
Proof. solve_proper. Qed.

Local Transparent Mem.load.

Lemma lock_inv_acquire m sh h R : Mem_load_unchecked Mptr m (lock_address h).1 (lock_address h).2 = Some (Vptrofs (Ptrofs.one)) →
  mem_auth m -∗ lock_inv sh h R ={↑lockN}=∗
  ∃ m', mem_auth m' ∗ lock_inv sh h R ∗ ▷ R.
Proof.
  intros Hload; iIntros "Hm (#I & Hsh)".
  iInv "I" as "((%b & >Hb & HR) & Hown)".
  iDestruct (core_load_load' with "[$Hm Hb]") as %Hload'.
  { rewrite assert_lemmas.mapsto_core_load; auto. }
  unfold Mem.load in Hload'; if_tac in Hload'; last done.
  rewrite /Mem_load_unchecked in Hload; rewrite Hload in Hload'.
  destruct b; inv Hload'.
  iDestruct (mapsto_valid_access_wr with "[$Hm $Hb]") as %?; auto.
  edestruct Mem.valid_access_store as (m' & Hstore); first done.
  iMod (juicy_mem_lemmas.mapsto_store _ _ _ (Vptrofs Ptrofs.zero) with "[$Hm $Hb]") as "(Hm & Hb)"; eauto.
  { intros _; instantiate (1 := if Archi.ptr64 then tlong else tint); done. }
  { done. }
  iFrame "#∗".
  iModIntro; iSplitL; last done.
  iExists false; by iFrame.
Qed.

Lemma lock_inv_release m sh h R : Mem_load_unchecked Mptr m (lock_address h).1 (lock_address h).2 = Some (Vptrofs (Ptrofs.zero)) →
  mem_auth m -∗ lock_inv sh h R -∗ R ={↑lockN}=∗
  ∃ m', mem_auth m' ∗ lock_inv sh h R.
Proof.
  intros Hload; iIntros "Hm (#I & Hsh) HR".
  iInv "I" as "((%b & >Hb & HR') & Hown)".
  iDestruct (core_load_load' with "[$Hm Hb]") as %Hload'.
  { rewrite assert_lemmas.mapsto_core_load; auto. }
  unfold Mem.load in Hload'; if_tac in Hload'; last done.
  rewrite /Mem_load_unchecked in Hload; rewrite Hload in Hload'.
  destruct b; inv Hload'.
  iDestruct (mapsto_valid_access_wr with "[$Hm $Hb]") as %?; auto.
  edestruct Mem.valid_access_store as (m' & Hstore); first done.
  iMod (juicy_mem_lemmas.mapsto_store _ _ _ (Vptrofs Ptrofs.one) with "[$Hm $Hb]") as "(Hm & Hb)"; eauto.
  { intros _; instantiate (1 := if Archi.ptr64 then tlong else tint); done. }
  { done. }
  iFrame "#∗".
  iModIntro; iSplitL; last done.
  iExists true; by iFrame.
Qed.

Lemma lock_inv_make m l R :
  mem_auth m -∗ (∃ v, address_mapsto Mptr v Ews l) ={↑lockN}=∗
  ∃ m', mem_auth m' ∗ ∃ h, <affine> ⌜lock_address h = l⌝ ∗ lock_inv 1 h R.
Proof.
  iIntros "Hm (% & Hl)".
  iDestruct (mapsto_valid_access_wr with "[$Hm $Hl]") as %?; auto.
  edestruct Mem.valid_access_store as (m' & Hstore); first done.
  iMod (juicy_mem_lemmas.mapsto_store _ _ _ (Vptrofs Ptrofs.zero) with "[$Hm $Hl]") as "(Hm & Hl)"; eauto.
  { intros _; instantiate (1 := if Archi.ptr64 then tlong else tint); done. }
  { done. }
  iFrame.
  rewrite /lock_inv.
  iMod (cinv_alloc _ _ (lock_inv_pred l R) with "[Hl]") as (?) "(? & ?)".
  { rewrite /lock_inv_pred.
    iExists false; by iFrame. }
  iModIntro; iExists {| lock_address := l; lock_gname := γ |}; by iFrame.
Qed.

Lemma lock_inv_free m h R : <affine> exclusive_mpred R -∗
  mem_auth m -∗ lock_inv 1 h R -∗ R ={↑lockN}=∗
  ∃ m', mem_auth m' ∗ (∃ v, address_mapsto Mptr v Ews (lock_address h)) ∗ R ∗ ▷ emp.
Proof.
  iIntros "Hexcl Hm (#I & Hsh) HR".
  iMod (cinv_cancel with "I Hsh") as "(%b & >Hb & HR')"; first done.
  destruct b.
  { iAssert (▷False)%I with "[Hexcl HR HR']" as ">[]".
    rewrite bi.affinely_elim.
    iApply "Hexcl"; by iFrame. }
  by iFrame.
Qed.
*)

(* Here's a version that uses ghost state to maintain a map of lock invariants. *)
Class lockGS Σ := LockGS
{ lockGS_inG :: inG Σ (gmap_viewR address (laterO (iPropO Σ)));
  lockGS_gname : gname }.

Context `{!lockGS Σ}.

Definition lock_inv sh v (R : mpred) : mpred := ∃ l, <affine> ⌜val2adr v l⌝ ∗
  LKspec LKSIZE sh l ∗ own lockGS_gname (gmap_view_frag l DfracDiscarded (invariant_unfold R)).

Definition rec_inv sh v (Q R: mpred) : mpred := (R ∗-∗ Q ∗ ▷ lock_inv sh v R)%I.

#[global] Instance lock_inv_nonexpansive sh v : NonExpansive (lock_inv sh v).
Proof. solve_proper. Qed.

Definition lock_state (m : mem) ls : mpred :=
  ∃ I : gmap address mpred, <affine> ⌜dom I = ls ∧ lock_addresses_disjoint ls⌝ ∗
  own lockGS_gname (gmap_view_auth (DfracOwn 1) (invariant_unfold <$> I)) ∗
  [∗ map] l ↦ R ∈ I, (<affine> ⌜Mem_load_unchecked Mptr m l.1 l.2 = Vptrofs (Ptrofs.one)⌝ ∗ ▷R) ∨
                       (<affine> ⌜Mem_load_unchecked Mptr m l.1 l.2 = Vptrofs (Ptrofs.zero)⌝).

End mpred.
