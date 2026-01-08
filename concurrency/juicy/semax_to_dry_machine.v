(* Instead of deriving a juicy-machine execution from the CSL proof, we derive a dry-machine execution
   directly, along the lines of the sequential adequacy proof (veric/SequentialClight). *)
Require Import Coq.Strings.String.

Require Import compcert.lib.Integers.
Require Import compcert.common.AST.
Require Import compcert.cfrontend.Clight.
Require Import compcert.common.Globalenvs.
Require Import compcert.common.Memory.
Require Import compcert.common.Memdata.
Require Import compcert.common.Values.

Require Import VST.msl.Coqlib2.

Require Import VST.msl.eq_dec.
Require Import VST.veric.external_state.
Require Import VST.veric.juicy_mem.
Require Import VST.veric.juicy_mem_lemmas.
Require Import VST.veric.semax_prog.
Require Import VST.veric.Clight_core.
Require Import VST.veric.Clightcore_coop.
Require Import VST.veric.semax.
Require Import VST.veric.semax_ext.
Require Import VST.veric.semax_lemmas.
Require Import VST.veric.juicy_extspec.
Require Import VST.veric.initial_world.
Require Import VST.veric.juicy_extspec.
Require Import VST.veric.tycontext.
Require Import VST.veric.res_predicates.
Require Import VST.veric.SequentialClight.
Require Import VST.floyd.coqlib3.
Require Import VST.floyd.canon.
Require Import VST.sepcomp.step_lemmas.
Require Import VST.sepcomp.event_semantics.
Require Import VST.sepcomp.extspec.
Require Import VST.concurrency.juicy.semax_conc_pred.
Require Import VST.concurrency.juicy.semax_conc.
(*Require Import VST.concurrency.juicy.juicy_machine.*)
Require Import VST.concurrency.common.threadPool.
Require Import VST.concurrency.common.HybridMachineSig.
Require Import VST.concurrency.common.HybridMachine.
Require Import VST.concurrency.common.scheduler.
Require Import VST.concurrency.common.addressFiniteMap.
Require Import VST.concurrency.common.permissions.
Require Import VST.concurrency.common.ClightSemanticsForMachines.
(*Require Import VST.concurrency.juicy.JuicyMachineModule.
Require Import VST.concurrency.juicy.sync_preds_defs.
Require Import VST.concurrency.juicy.sync_preds.
Require Import VST.concurrency.juicy.join_lemmas.
Require Import VST.concurrency.juicy.semax_invariant.
Require Import VST.concurrency.juicy.semax_initial.
Require Import VST.concurrency.juicy.semax_progress.
Require Import VST.concurrency.juicy.semax_preservation_jspec.
Require Import VST.concurrency.juicy.semax_safety_makelock.
Require Import VST.concurrency.juicy.semax_safety_spawn.
Require Import VST.concurrency.juicy.semax_safety_release.
Require Import VST.concurrency.juicy.semax_safety_freelock.
Require Import VST.concurrency.juicy.semax_preservation.
Require Import VST.concurrency.juicy.semax_simlemmas.*)
Require Import VST.concurrency.common.dry_machine_lemmas.
Require Import VST.concurrency.common.dry_machine_step_lemmas.
Require Import VST.concurrency.juicy.memLt. (* added memLt *)
Require Import iris_ora.algebra.gmap.

Import ThreadPool.

Set Bullet Behavior "Strict Subproofs".

(* concurrent state interpretation *)
Class conc_gen_heapGS Σ := ConcGenHeapGS
  { conc_gen_heap_inG :: gen_heapGpreS share address resource Σ;
    conc_gen_meta_name : gname }.

Class conc_heapGS Σ := ConcHeapGS
  { conc_heapGS_invGS :: invGS_gen HasNoLc Σ;
    conc_heapGS_gen_heapGS :: conc_gen_heapGS Σ;
    conc_heapGS_funspecGS :: funspecGS Σ }.

Class conc_VSTGS OK_ty Σ := ConcVSTGS
  { conc_VST_heapGS :: conc_heapGS Σ; conc_VST_extGS :: externalGS OK_ty Σ}.

Definition thread_gen_heapGS `{!conc_gen_heapGS Σ} g := GenHeapGS _ _ _ _ (gen_heap_inG := conc_gen_heap_inG) g conc_gen_meta_name.

Definition access_equiv (m: mem) k (r : prodO dfracO (optionO (leibnizO resource))) :=
  (access_at m k Cur) = (perm_of_res r).

Definition access_map_rmap (m: mem) σ : Prop :=
  forall loc, access_equiv m loc (σ @ loc).

About mem_auth.

(*

Definition mem_auth1 `{Σ : gFunctors}
  (gen_heapGS : gen_heapGS share address resource Σ) (m : mem) :=
  ∃ σ, ⌜juicy_mem.coherent m σ /\ access_map_rmap m σ⌝ ∧ resource_map.resource_map_auth(H1 := gen_heapGpreS_heap(gen_heapGpreS := gen_heap_inG)) (gen_heap_name _) 1 σ.

*)


Definition thread_mem_auth `{!conc_gen_heapGS Σ} g m :=
  mem_auth (gen_heapGS0 := thread_gen_heapGS g) m.


(*
Definition access_equiv (m: mem) k r := (access_at m k Cur) = (perm_of_res r).

Definition access_map_rmap m phi: forall (loc: positive * Z),
    access_equiv m loc phi.
    (access_at m loc Cur) = (perm_of_res (phi @ loc)).
*)



Definition conc_mem_auth `{!conc_gen_heapGS Σ} m (perms : gmap nat (gname * access_map)) := ∃ σs : gmap nat (resource_map.rmapUR _ _ _),
  ([∗ map] '(g,p);σ∈perms;σs,
     ⌜∃ Hp : permMapLt p (getMaxPerm m),
         coherent (restrPermMap Hp) σ (*/\ access_map_rmap (restrPermMap Hp) σ *)  ⌝ ∧
    resource_map.resource_map_auth(H1 := gen_heapGpreS_heap(gen_heapGpreS := conc_gen_heap_inG)) g 1 σ) (* ∗
  let σ := [^op map] σ∈σs, σ in <affine> ⌜✓ σ ∧ coherent m σ⌝ *).

(*
  perms : gmap nat (gname * access_map) : for each thread id

σs : gmap nat (rmapUR ...) : for each thread id, a ghost snapshot σ in heap - record the thread-local ghost view of memory that must be coherent with those perms?

([∗ map]  ... ∈ perms; σs, ...) is a zip over two maps keyed by the same domain.
perms : gmap nat (gname * access_map) - At key i: value (g,p).
σs : gmap nat (rmapUR ...) - At key i: value σ.


If σs = {0↦σ0, 1↦σ1}, then [^op map] σi ∈ σs, σi = σ0 ∙ σ1. 

If σs = ∅, then it equals ε.

\sigma_i is combination of all the point to for thread i
two different thread owns dont conflict, at most one. 
 *)

Definition thread_VSTGS `{!conc_VSTGS OK_ty Σ} g := Build_VSTGS _ _ (HeapGS _ _ (thread_gen_heapGS g) _) _.

Definition thread_state_interp `{!conc_VSTGS OK_ty Σ} g m z := thread_mem_auth g m ∗ ext_auth z.

Definition conc_state_interp `{!conc_VSTGS OK_ty Σ} m perms z := conc_mem_auth m perms ∗ ext_auth z.

(* fix in seplog *)
Definition funspec_auth `{!funspecGS Σ} m := own(inG0 := funspec_inG) funspec_name (gmap_view.gmap_view_auth (dfrac.DfracOwn 1) m).

(* up *)
Existing Instance shared.shared_equiv.
Lemma coherent_equiv m σ1 σ2 : ✓ (σ1 : resource_map.rmapUR _ _ _) → σ1 ≡ σ2 → coherent m σ1 ↔ coherent m σ2.
Proof.
  intros Hv H; rewrite /coherent.
  apply Morphisms_Prop.all_iff_morphism; intros l.
  specialize (H l).
  f_equiv.
  - split; intros Hnone H1; apply Hnone in H1; rewrite H1 in H; inv H; auto.
  - rewrite /resource_at; erewrite resR_to_resource_eq; done.
Qed.


Lemma thread_conc_mem_auth `{!conc_VSTGS OK_ty Σ} i g m :
  thread_mem_auth g m ⊢ conc_mem_auth m {[i := (g, getCurPerm m)]}.
Proof.
  intros; rewrite /thread_mem_auth /conc_mem_auth.
  iIntros "(% & % & H)".
  iDestruct (resource_map.resource_map_auth_valid with "H") as %(_ & ?).
  iExists {[i := σ]}; rewrite big_sepM2_singleton; iFrame.
  iPureIntro.
  esplit.
  exists (cur_lt_max m); rewrite restrPermMap_eq //.
  done.
  (*
  rewrite restrPermMap_eq.
  - Search permMapLt.

    split; last done; exists (cur_lt_max m); rewrite restrPermMap_eq //.
  - split; first by rewrite big_opM_singleton.
    rewrite -coherent_equiv //.
    rewrite big_opM_singleton //. *)
Qed.

Lemma thread_conc_state_interp `{!conc_VSTGS OK_ty Σ} i g m z :
  thread_state_interp g m z ⊢ conc_state_interp m {[i := (g, getCurPerm m)]} z.
Proof.
  iIntros "(? & $)".
  iApply thread_conc_mem_auth; iFrame.
Qed.


(*
Definition equal_on_perm (p : access_map) (m m' : mem) : Prop :=
  ∀ b ofs, p !! (b,ofs) = Some _ → Mem.equal m m' b ofs.
*)

Definition add_fresh_block (b : Values.block) (cur : access_map) : access_map :=
  PMap.set b (fun _ => None) cur.

(* Definition remove_region (b: Values.block) (lo hi: Z) (pm: access_map) : access_map :=
  setPermBlock None b lo pm (Z.to_nat (hi - lo)). *)

(* Half-open range [lo, hi) implemented via length = Z.to_nat (hi - lo) *)
Definition setPerm_range (p : option permission)
  (b : Values.block) (lo hi : Z) (cur : access_map)
  : access_map :=
  if Z.leb hi lo then cur
  else setPermBlock p b lo cur (Z.to_nat (hi - lo)).

Definition remove_region (b : Values.block) (lo hi : Z) (cur : access_map)
  : access_map := setPerm_range None b lo hi cur.

Definition add_region (b : Values.block) (lo hi : Z) (perm : permission) (cur : access_map)
  : access_map := setPerm_range (Some perm) b lo hi cur.

Definition can_store_at (p : access_map) (l : positive * Z) : Prop :=
  match (p # (fst l)) (snd l) with
  | Some q => perm_order q Writable   (* or just: perm_order Writable q *)
  | None   => False
  end.

Lemma writable_at_equiv (p:access_map) (l:positive*Z) :
  (match (p # (fst l)) (snd l) with
   | Some q => perm_order q Writable
   | None   => False
   end)
  <->
    Mem.perm_order'' ((p # (fst l)) (snd l)) (Some Writable).
Proof.
  unfold Mem.perm_order''.
  destruct ((p # (fst l)) (snd l)) as [q|]; cbn; split; auto.
Qed.

Definition contents_at (m : mem) (l : positive * Z) : memval :=
  ZMap.get (snd l) ((Mem.mem_contents m) # (fst l)).


Definition permMapsDisjoint_at
  (perms : gmap nat (gname * access_map))
  (i j : nat) : Prop :=
  match perms !! i, perms !! j with
  | Some pi, Some pj =>
      let mi := snd pi in
      let mj := snd pj in
      permMapsDisjoint mi mj
  | _, _ => False
  end.

Inductive SelfOp :=
| SO_id                                 (* no-op / pure store *)
| SO_alloc (b : Values.block) (lo hi : Z)                 (* malloc: fresh block b = nextblock m *)
| SO_free  (b : Values.block) (lo hi : Z).     (* free: drop [lo,hi) on block b *)

Check setPermBlock.

Print Mem.alloc.
Check PMap.set .
Check setPermBlock.
Search extensionality.
Print access_map.

(* Override one access_map on [lo,hi) in block b *)
Definition override_range
  (p : option permission) (b : Values.block) (lo hi : Z) (pmap : access_map)
  : access_map :=
  Maps.PMap.set b
    (fun ofs =>
       if zle lo ofs && zlt ofs hi then p else Maps.PMap.get b pmap ofs)
    pmap.

Print Mem.unchecked_free.

Record OpSC (i : nat) (m m' : mem)
            (p : access_map) (perms : gmap nat (gname * access_map)) : Prop := {
  sc_self : SelfOp;

  sc_self_eqs :
    match sc_self with
    | SO_id =>
        getCurPerm m' = p /\
        getMaxPerm m' = getMaxPerm m /\
        Mem.nextblock m' = Mem.nextblock m /\
          (forall loc, contents_at m loc = contents_at m' loc \/ can_store_at p loc)

    | SO_alloc b lo hi =>
        b = Mem.nextblock m /\
        (* 
        getCurPerm m' =
            setPermBlock (Some Freeable) b lo p (Z.to_nat (hi - lo)) /\
        getMaxPerm m' =
            setPermBlock (Some Freeable) b lo (getMaxPerm m) (Z.to_nat (hi - lo)) /\ *)
        Mem.mem_access m' = PMap.set (Mem.nextblock m)
           (λ (ofs : Z) (_ : perm_kind), if zle lo ofs && zlt ofs hi then Some Freeable else None)
              (Mem.mem_access m) /\
        Mem.nextblock m' = Pos.succ (Mem.nextblock m) /\
        Mem.mem_contents m' =
            PMap.set (Mem.nextblock m) (ZMap.init Undef) (Mem.mem_contents m)

    | SO_free b lo hi =>
        Mem.free m b lo hi = Some m' /\
        Mem.mem_access m' = PMap.set b (λ (ofs : Z) (k : perm_kind),
            if zle lo ofs && zlt ofs hi then None else (Mem.mem_access m) # b ofs k)
               (Mem.mem_access m) /\ 
        Mem.nextblock m' = Mem.nextblock m /\
        Mem.mem_contents m' = Mem.mem_contents m
    end;

  (* All *other* threads remain strictly below the NEW Max. *)
  sc_others_still_lt1 :
    ∀ j g' p', j ≠ i → perms !! j = Some (g', p') →
      permMapLt p' (getMaxPerm m');

  (* permMapsDisjoint in invariant *)
  sc_perm_disjoint:
    forall i j, j <> i -> permMapsDisjoint_at perms i j;

    (*
 (∃ b lo hi,                              (* lock acquire*)
              getCurPerm m' = add_region b lo hi (getCurPerm m)) ; *)

}.

Lemma writable_at_perm_order_cases
  (p : access_map) (loc : positive * Z) (x : option permission) :
  can_store_at p loc -> p # (loc.1) loc.2 = x -> x = Some Freeable \/ x = Some Writable.
Proof.
  rewrite /can_store_at.
  destruct (p # (loc.1) loc.2) as [q|] eqn: Hp; [|contradiction].
  intros; destruct x as [r|]; try tauto.
  - inv H0. inv H. by right. by left.
  - discriminate.
Qed.

Lemma access_at_restrPermMap_Cur p m loc (Hlt : permMapLt p (getMaxPerm m)):
  access_at (restrPermMap Hlt) loc Cur = p # (loc.1) loc.2 .
Proof.
  destruct loc as [b ofs].
  assert (Hacc: forall m b ofs, access_at m (b,ofs) Cur = (getCurPerm m) # b ofs).
  { rewrite /getCurPerm /access_at /=. intros; by rewrite Maps.PMap.gmap. }
  rewrite Hacc.
  pose proof (mem_equiv.getCur_restr p m Hlt) as Heq.
  specialize (Heq b).
  by rewrite Heq.
Qed.

Definition writable_dfrac (dq : dfrac) : Prop :=
  match dq with
  | DfracOwn (Share sh) => writable0_share sh
  | _ => False
  end.

(* No need at this time - maybe it's useful in the future *)
Lemma lookup_Some_VAL_from_perm_Free_Writable σ loc :
  ✓ (σ : resource_map.rmapUR _ _ _) ->
  perm_of_res (σ @ loc) = Some Freeable \/ perm_of_res (σ @ loc) = Some Writable ->
  exists (dq : dfrac) (rsh : readable_dfrac dq) (v0 : agree (leibnizO resource)),
    σ !! loc = Some (shared.YES dq rsh v0) /\ writable_dfrac dq.
Proof.
  intros Hv.
  rewrite /resource_at /resR_to_resource;
  destruct (σ !! loc) as [s|] eqn:Hlk; rewrite Hlk; simpl.
  2: {
    intros. if_tac in H; try done.
    destruct H; try done.
  }
  destruct (shared.val_of s) as [av|] eqn:Hval; simpl;
  destruct (shared.dfrac_of s) eqn: E1.
  destruct s0;
  destruct (`(resource_map.elem_of_agree av)); simpl;
    destruct x; try intros; rewrite /perm_of_sh in H; repeat if_tac in H; try congruence; try (destruct H; try done).
  - exists (shared.dfrac_of s); rewrite E1 ; destruct s; simpl in E1; subst; last first; try inv E1.
    exists rsh, v0; split; try done.
  - exists (shared.dfrac_of s); rewrite E1 ; destruct s; simpl in E1; subst; last first; try inv E1.
    exists rsh, v0; split; try done.
  - destruct (`(resource_map.elem_of_agree av)) eqn : Ha; simpl;
    destruct x; last first; intros; try done; destruct H; try done;
    assert (Hv1: ✓ (σ !! loc)); try done;
    rewrite Hlk Some_valid in Hv1;
    rewrite /shared.dfrac_of in E1;
    destruct s; last first;
    inv E1; subst; simpl in *; destruct Hv1 as ((? & ? & ?) & ?); rewrite /perm_of_sh' in H;
    destruct s0; rewrite /perm_of_sh in H; repeat if_tac in H; try done; inv H0.
    pose proof writable_top.
    by rewrite /share_top /= in H.
  - intros; destruct (shared.dfrac_of s); destruct s0; destruct H; try if_tac in H; try done.
  - intros. destruct H; try done.
Qed.

Lemma writable_readable_dfrac_excl dq1 dq :
  writable_dfrac dq1 → readable_dfrac dq → ¬ ✓ (dq1 ⋅ dq).
Proof.
  intros Hw Hr.
  assert (Hwdf: forall dq, writable_dfrac dq -> exists sh, dq = DfracOwn (Share sh) /\ writable0_share sh).
  { intros; destruct dq0; destruct s; try done; exists sh;  by split. }
  apply Hwdf in Hw.
  destruct Hw as (? & (? & ?)).
  intros Hcontra; subst.
  rewrite ora_comm in Hcontra.
  apply dfrac_valid_own_readable in Hcontra; auto.
  destruct Hcontra as (? & (Hsh & ?)).
  by inv Hsh.
Qed.

Lemma restrPermMap_Cur_eq m p (Hlt : permMapLt p (getMaxPerm m)) :
  ∀ b ofs, (Mem.mem_access (restrPermMap Hlt)) # b ofs Cur = p # b ofs.
Proof.
  intros b ofs.
  pose proof (mem_equiv.getCur_restr p m Hlt) as Heq.
  assert (Heq1: forall b ofs m, Maps.PMap.get b (getCurPerm m) ofs =
                          Maps.PMap.get b (Mem.mem_access m) ofs Cur).
  { rewrite /getCurPerm. intros. by rewrite Maps.PMap.gmap. }
  specialize (Heq1 b ofs (restrPermMap Hlt)).
  rewrite -Heq1.
  specialize (Heq b).
  by rewrite Heq.
Qed.

Lemma readable_dfrac_perm_order m p dq
  (v : memval) (v0 : agree (leibnizO resource)) loc (Hlt : permMapLt p (getMaxPerm m))
  (rsh : readable_dfrac dq):
  (option_map (λ v : agree resource,
         proj1_sig (resource_map.elem_of_agree v)) (Some v0)) = Some (VAL v) ->
  Mem.perm_order'' (access_at (restrPermMap Hlt) loc Cur)
    (perm_of_res (resR_to_resource (Some (shared.YES dq rsh v0)))) ->
  Mem.perm_order'' (p # (loc.1) loc.2) (Some Readable).
Proof.
  pose proof (access_at_restrPermMap_Cur p m loc Hlt) as Haccess.
  intros ? Horder.
  rewrite Haccess in Horder.
  set dq1 := (shared.dfrac_of (shared.YES dq rsh v0)).
  set r1 := (option_map (λ v : agree resource, proj1_sig (resource_map.elem_of_agree v))
                (shared.val_of (shared.YES dq rsh v0))).
  pose proof (perm_of_res_cases dq1 r1) as Hperm_res.
  destruct Hperm_res as [Hperm_res1 | Hperm_res2].
  - destruct Hperm_res1 as (? & ? & Hres_dfrac).
    rewrite /dq1 /r1 in Hres_dfrac.
    simpl in Horder.
    destruct dq.
    destruct s.
    simpl in *.
    destruct (`(resource_map.elem_of_agree v0)).
    simpl in *.
    destruct x0.
    subst.
    rewrite /perm_of_sh in Horder.
    repeat if_tac in Horder; subst; simpl in *; try done;
      eapply mem_lemmas.po_trans; eauto; [try apply perm_F_any | try apply perm_W_R].
    + repeat if_tac in Hres_dfrac; subst.
      * by pose proof (bot_unreadable).
      * rewrite /perm_of_sh in Hres_dfrac.
        repeat if_tac in Hres_dfrac; subst; easy.
    + rewrite /perm_of_sh in Hres_dfrac.
      repeat if_tac in Hres_dfrac; subst; easy.
    + rewrite /perm_of_sh in Hres_dfrac.
      repeat if_tac in Hres_dfrac; subst; easy.
    + simpl in *; destruct (`(resource_map.elem_of_agree v0)); destruct x0;
      repeat if_tac in Hres_dfrac; subst; auto; try easy.
      rewrite mem_lemmas.po_oo in H1.
      eapply mem_lemmas.po_trans; eauto.
  - rewrite /dq1 /r1 /= in Hperm_res2; destruct Hperm_res2 as (? & Hperm_res2);
      simpl in *;  destruct dq; destruct s; destruct (`(resource_map.elem_of_agree v0));
      specialize (H0 v); easy.
Qed.

Lemma permMapLt_trans (p q r : access_map) :
  permMapLt p q -> permMapLt q r -> permMapLt p r.
Proof.
  unfold permMapLt; intros Hpq Hqr b ofs.
  eapply mem_lemmas.po_trans; eauto.
Qed.

Lemma permMapLt_getMax_setPermBlock_Freeable
  (m : mem) (b : positive) (lo hi : Z) :
  permMapLt (getMaxPerm m)
    (setPermBlock (Some Freeable) b lo (getMaxPerm m) (Z.to_nat (hi - lo))).
Proof.
  rewrite / permMapLt.
  intros b' ofs'.
  destruct (peq b' b) as [->|Hb].
  - destruct (Z_le_dec lo ofs') as [Hlo|Hlo].
    + destruct (Z_lt_dec ofs' (lo + Z.of_nat (Z.to_nat (hi - lo)))) as [Hhi|Hhi].
      * rewrite setPermBlock_same; last first. lia.
        apply perm_order''_Freeable.
      * rewrite setPermBlock_other_1; last first. lia.
        apply po_refl.
    + rewrite setPermBlock_other_1; last first. lia.
      apply po_refl.
  - rewrite setPermBlockFunc_other_2; auto.
    apply po_refl.
Qed.

Lemma permMapLt_after_setPermBlock_Freeable
  (p : access_map) (m m' : mem) (b : positive) (lo hi : Z) :
  permMapLt p (getMaxPerm m) ->
  getMaxPerm m' = setPermBlock (Some Freeable) b lo (getMaxPerm m) (Z.to_nat (hi - lo)) ->
  permMapLt p (getMaxPerm m').
Proof.
  intros Hlt Hmax_eq.
  rewrite /permMapLt.
  eapply permMapLt_trans; [exact Hlt|].
  rewrite Hmax_eq.
  apply permMapLt_getMax_setPermBlock_Freeable.
Qed.

Lemma getCurPerm_setPermBlock_or
  (m' : mem) (b : Values.block) (lo hi : Z)
  (p : access_map)
  (Hcur : getCurPerm m' = setPermBlock (Some Writable) b lo p (Z.to_nat (hi - lo)))
  (b' : positive) (ofs' : Z) :
  (getCurPerm m') # b' ofs' = Some Writable \/
    (getCurPerm m') # b' ofs' = p # b' ofs'.
Proof.
  rewrite Hcur.
  destruct (setPermBlock_or (Some Writable) b lo (Z.to_nat (hi - lo)) p b' ofs')
    as [H|H].
  - left; exact H.
  - right; exact H.
Qed.

Lemma setPermBlock_other
  (p: option permission) (b b0: positive) (lo: Z) (pmap: access_map) (sz: nat) :
  b0 <> b ->
  (setPermBlock p b lo pmap sz) # b0 = pmap # b0.
Proof.
  revert lo pmap.
  induction sz as [|sz IH]; intros lo pmap Hb; simpl.
  - reflexivity.
  - unfold setPerm; simpl.
    rewrite PMap.gso; auto.
Qed.

Lemma getCurPerm_nextblock_none (m : mem) (ofs : Z) :
  (getCurPerm m) # (Mem.nextblock m) ofs = None.
Proof.
  destruct ((getCurPerm m) # (Mem.nextblock m) ofs) as [q|] eqn:Hq; [|reflexivity].
  exfalso.
  assert (Mem.perm m (Mem.nextblock m) ofs Cur q) as Hperm.
  { rewrite /Mem.perm.
    rewrite /getCurPerm /= in Hq.
    rewrite PMap.gmap in Hq.
    rewrite Hq.
    apply perm_refl.
  }
  pose proof (Mem.perm_valid_block _ _ _ _ _ Hperm).
  rewrite /Mem.valid_block /Plt in H.
  lia.
Qed.

Lemma getMaxPerm_nextblock_none (m : mem) (ofs : Z) :
  (getMaxPerm m) # (Mem.nextblock m) ofs = None.
Proof.
  destruct ((getMaxPerm m) # (Mem.nextblock m) ofs) as [q|] eqn:Hq; [|reflexivity].
  exfalso.
  assert (Mem.perm m (Mem.nextblock m) ofs Max q) as Hperm.
  { rewrite /getMaxPerm /= PMap.gmap in Hq.
    rewrite /Mem.perm Hq.
    apply perm_refl.
  }
  pose proof (Mem.perm_valid_block _ _ _ _ _ Hperm).
  rewrite /Mem.valid_block /Plt in H.
  lia.
Qed.

Lemma setPerm_fst
  (p : option permission) (b : positive) (ofs : Z) (pmap : access_map) :
  (setPerm p b ofs pmap).1 = pmap.1.
Proof.
  reflexivity.
Qed.

Lemma setPermBlock_fst
  (p : option permission) (b : positive) (ofs : Z) (pmap : access_map) (len : nat) :
  (setPermBlock p b ofs pmap len).1 = pmap.1.
Proof.
  induction len; simpl.
  - reflexivity.
  - exact IHlen.
Qed.

Lemma setPermBlock_tree_lookup_at_b
  (p : option permission) (b : positive) (ofs : Z)
  (pmap : access_map) (n : nat) :
  ((setPermBlock p b ofs pmap n).2 !! b)%maps =
    match n with
    | 0%nat => (pmap.2 !! b)%maps
    | S _   => Some (PMap.get b (setPermBlock p b ofs pmap n))
    end.
Proof.
  destruct n as [|n]; simpl.
  - reflexivity.
  - rewrite ! PTree.gss.
    f_equal.
    rewrite PMap.gss. auto.
Qed.

Lemma setPermBlock_tree_is_Some
  (p : option permission) (b : positive) (ofs : Z)
  (pmap : access_map) (n : nat) :
  n <> 0%nat ->
  is_Some ((setPermBlock p b ofs pmap n).2 !! b)%maps.
Proof.
  intros Hn.
  destruct n as [|n]; [contradiction|].
  rewrite setPermBlock_tree_lookup_at_b.
  eexists; reflexivity.
Qed.

Lemma setPerm_tree_gso
  (p : option permission) (b i : positive) (ofs : Z) (pmap : access_map) :
  i <> b ->
  ((setPerm p b ofs pmap).2 !! i)%maps = (pmap.2 !! i)%maps.
Proof.
  intro Hi.
  unfold setPerm.
  simpl.
  rewrite PTree.gso; auto.
Qed.

Lemma setPermBlock_tree_gso
  (p : option permission) (b : positive) (lo : Z)
  (pmap : access_map) (n : nat) (i : positive) :
  i <> b ->
  ((setPermBlock p b lo pmap n).2 !! i)%maps = (pmap.2 !! i)%maps.
Proof.
  intro Hi.
  induction n as [|n IH]; simpl; try done.
  rewrite setPerm_tree_gso; auto.
Qed.

Lemma contents_cohere_restrPermMap_iff
  (p : access_map) (m : mem) (Hlt : permMapLt p (getMaxPerm m))
  (loc : positive * Z) r :
  contents_cohere (restrPermMap Hlt) loc r <-> contents_cohere m loc r.
Proof.
  unfold contents_cohere.
  rewrite (restrPermMap_contents (p':=p) (m:=m) Hlt).
  tauto.
Qed.

Lemma getCurPerm_access_at (m : mem) (b : positive) (ofs : Z) :
  (getCurPerm m) # b ofs = (Mem.mem_access m) # b ofs Cur.
Proof. rewrite /getCurPerm /= PMap.gmap //=. Qed.

Lemma access_at_Cur_of_mem_equiv (m1 m2 : mem) (loc : address) :
  mem_equiv.mem_equiv m1 m2 ->
  access_at m1 loc Cur = access_at m2 loc Cur.
Proof.
  intros Heqv.
  destruct Heqv as [Hcur Hmax Hcnt Hnb].
  rewrite /access_at.
  rewrite <- ! getCurPerm_access_at.
  rewrite /mem_equiv.Cur_equiv /mem_equiv.access_map_equiv in Hcur.
  specialize (Hcur loc.1).
  exact ((f_equal (fun p => p loc.2) Hcur)).
Qed.

Lemma mem_coherent_equiv m1 m2 (σ : resource_map.rmapUR _ _ _):
  mem_equiv.mem_equiv m1 m2 -> coherent m1 σ -> coherent m2 σ.
Proof.
  intros Heq Hchr.
  Print mem_equiv.mem_equiv.
  rewrite /coherent in Hchr |- *.
  intros.
  specialize (Hchr loc).
  destruct Hchr as (Hloc & Hchr).
  split.
  - intros. apply Hloc.
    erewrite mem_equiv.nextblock_eqv; eauto.
  - rewrite /coherent_loc /contents_cohere /access_cohere /= in Hchr |- *.
    destruct Hchr as (Hmem & Hperm).
    split.
    + rewrite /juicy_mem.contents_at in Hmem |- *.
      destruct Heq as [Hcur Hmax Hcnt Hnb].
      rewrite /mem_equiv.content_equiv in Hcnt.
      intros.
      apply Hmem in H.
      specialize (Hcnt loc.1 loc.2).
      by rewrite Hcnt in H.
    + erewrite access_at_Cur_of_mem_equiv in Hperm; eauto.
Qed.


Lemma max_cur_equiv m m' lo hi
  (Hlt1 : permMapLt (getCurPerm m')
           (PMap.map (λ (f : Z → perm_kind → option permission) (ofs : Z), f ofs Max)
              (Mem.mem_access (Mem.alloc m lo hi).1)))
  (Heq : Mem.mem_access m' =
        PMap.set (Mem.nextblock m)
          (λ (ofs : Z) (_ : perm_kind), if zle lo ofs && zlt ofs hi then Some Freeable else None)
          (Mem.mem_access m))
  (  Hcanon : ∀ (loc : Z) (k : perm_kind), (Mem.mem_access m').1 loc k = None):
  Mem.mem_access (restrPermMap Hlt1) = Mem.mem_access m'.
Proof.
  destruct m'; simpl in *.
  destruct mem_access eqn: E; simpl.
  f_equal.
  - extensionality; extensionality k.
    destruct k; simpl.
    rewrite /getMaxPerm /= in Heq.
    pose proof (f_equal (@fst _ _) Heq) as Hfst.
    simpl in Hfst.
    by rewrite Hfst. done.
  - apply PTree.extensionality; intros.
    rewrite PTree.gmap.
    destruct (Pos.eq_dec i (Mem.nextblock m)) as [->|Hneq].
    + rewrite PTree.gss /=.
      destruct ((t0 !! Mem.nextblock m)%maps) as [f|] eqn:Ht.
      2 : { exfalso. inv Heq. rewrite PTree.gss //= in Ht. }
      f_equal.
      apply functional_extensionality; intros ofs.
      apply functional_extensionality; intros k.
      destruct k; simpl.
      * pose proof (f_equal (fun am => am # (Mem.nextblock m) ofs) Heq) as Hlook.
        rewrite /PMap.get Ht /= in Hlook.
        by rewrite Hlook PTree.gss.
      * rewrite /getCurPerm /= Heq PMap.gmap.
        pose proof (f_equal (fun am => am # (Mem.nextblock m) ofs) Heq) as Hlook.
        rewrite /PMap.get Ht /= in Hlook.
        by rewrite Hlook !PTree.gss PMap.gss.
    + rewrite PTree.gso //=.
      rewrite /option_map /=.
      destruct (((Mem.mem_access m).2 !! i)%maps) as [f1|] eqn : Ht.
      destruct (t0 !! i)%maps as [f0|] eqn : Ht1.
      * f_equal.
        apply functional_extensionality; intros ofs.
        apply functional_extensionality; intros k.
        destruct k; try done.
        destruct (Mem.mem_access m) as [o1 t1] eqn:Hacc.
        rewrite /PMap.set /= in Heq.
        inv Heq.
        simpl in Ht.
        rewrite PTree.gso //= in Ht1.
        rewrite Ht in Ht1. by inv Ht1.
        rewrite /getCurPerm /= Heq /= PMap.gmap -Heq /PMap.get /= Ht1 //=.
      * inv Heq.
        by rewrite PTree.gso //= Ht in Ht1.
      * destruct (Mem.mem_access m) as [o1 t1] eqn:Hacc.
        rewrite /PMap.set /= in Heq.
        inv Heq.
        simpl in Ht.
        rewrite PTree.gso //=.
Qed.


Definition mem_with_access
  (m: Mem.mem) (acc: PMap.t (Z -> perm_kind -> option permission))
  (Hmax : forall b ofs, Mem.perm_order'' (acc#b ofs Max) (acc#b ofs Cur))
  (Hno  : forall b ofs k, ~ Plt b (Mem.nextblock m) -> acc#b ofs k = None)
  : Mem.mem :=
  {| Mem.mem_contents := Mem.mem_contents m;
    Mem.mem_access   := acc;
    Mem.nextblock    := Mem.nextblock m;
    Mem.access_max   := Hmax;
    Mem.nextblock_noaccess := Hno;
    Mem.contents_default := Mem.contents_default m |}.

Lemma conc_mem_auth_lookup `{!conc_VSTGS OK_ty Σ} i g p m perms :
  perms !! i = Some (g, p) →
  conc_mem_auth m perms ⊢ (∃ Hp : permMapLt p (getMaxPerm m),
      thread_mem_auth g (restrPermMap Hp)) ∗
        (∀ m', ⌜OpSC i m m' p perms⌝ ∧
                 thread_mem_auth g m' -∗
              ∃ m_all, conc_mem_auth m_all (<[i:=(g, getCurPerm m')]>perms)).
Proof.
  rewrite /conc_mem_auth; intros.
  iIntros "(% & H)".
  iDestruct (big_sepM2_delete_l _ _ _ i (g, p) with "H") as "H"; auto.
  iDestruct "H" as (?) "(% & (% & H) & Hbig)".
  destruct H1 as (Hlt & H2). 
  rename x2 into σ.
  iSplitL "H".
  { iExists _. iFrame; eauto. }
  simpl.
  iIntros (m') "(%HSc & H)".
  rewrite /thread_mem_auth /mem_auth.
  iDestruct "H" as (σ') "(% & H)".
  destruct HSc.
  destruct sc_self.
  destruct sc_self_eqs as (Hcur_eq & Hmax_eq & Hnxt_eq & Hloc).
  - (* Mem.nextblock m' = Mem.nextblock m /\ getCurPerm m' = getCurPerm m *)
    unshelve
    iExists (Mem.mkmem (Mem.mem_contents m') (Mem.mem_access m) (Mem.nextblock m) _ _ _).
    apply Mem.access_max.
    apply Mem.nextblock_noaccess.
    apply Mem.contents_default.
    setoid_rewrite (big_sepM2_delete_l _ _ _ i (g, p)) at 2; auto.
    iDestruct (resource_map.resource_map_auth_valid with "H") as %(_ & Hvalid).
    iExists (<[i := σ']>σs).
    + iExists σ'.
      iSplit; first rewrite lookup_insert //.
      iSplitR "Hbig".
      iFrame. iPureIntro.
      split; auto.
      rewrite /getMaxPerm /=.
      exists Hlt.
      replace (@restrPermMap _
                             {|
                               Mem.mem_contents := Mem.mem_contents m';
                               Mem.mem_access := Mem.mem_access m;
                               Mem.nextblock := Mem.nextblock m
                             |} 
                             Hlt) with m'; auto.
      symmetry.
      {
        pose proof (Mem_canonical_useful m') as Hcanon.
        destruct m'; simpl; apply Mem.mkmem_ext; simpl in *; try done.
        destruct mem_access; simpl.
        apply f_equal_prod.
        * extensionality; extensionality k.
          destruct k; auto.
          simpl in *.
          rewrite /getMaxPerm /= in Hmax_eq.
          inv Hmax_eq.
          by specialize (f_equal (fun f => f x) H4).
        * rewrite /getMaxPerm /= in Hmax_eq.
          inv Hmax_eq.
          apply PTree.extensionality; intros.
          pose proof (f_equal (fun tr => PTree.get i0 tr) H5) as Hb.
          rewrite !PTree.gmap1 in Hb.
          rewrite PTree.gmap.
          destruct (PTree.get i0 t0) as [f1|] eqn:E1;
            destruct (PTree.get i0 (Mem.mem_access m).2) as [f2|] eqn:E2;
            simpl in *; try congruence.
          inversion Hb as [Hf]; clear Hb; subst.
          f_equal.
          clear H4.
          extensionality ofs k.
          destruct k; simpl.
          { symmetry. exact (f_equal (fun g => g ofs) Hf). }
          { rewrite getCurPerm_correct /permission_at /PMap.get /= E1; auto. }
       }
       rewrite ! delete_insert_delete /getMaxPerm /=.
       iApply (big_sepM2_mono with "Hbig"); intros.
       apply lookup_delete_Some in H4.
       destruct y1.
       do 4 f_equiv.
       rename a0 into Hlt1.
       rewrite / impl /coherent.
       intros.
       split; auto.
       * intros; apply H5; auto.         
       * destruct (Hloc loc) as [Hmem_eq | Hwrite].
         ** rewrite /contents_at in Hmem_eq.
            rewrite /coherent_loc /contents_cohere /resource_at /juicy_mem.contents_at in H5 |- *.
            split.
            intros.
            rewrite - Hmem_eq.
            apply H5; auto.
            rewrite /access_cohere in H5 |- *.
            apply H5.
         ** unfold coherent_loc in H5 |- *.
            specialize (Hvalid loc).
            split; last first; try apply H5.
            apply lookup_delete_Some in H3.
            unfold contents_cohere, contents_at in *.
            rewrite /resource_at.
            intros.
            rewrite /resR_to_resource /= in H6.
            rewrite /coherent /coherent_loc /access_cohere /contents_cohere in H2.
            specialize (H2 loc).
            destruct H2 as (? & ? & ?).
            pose proof (access_at_restrPermMap_Cur p m loc Hlt) as Haccess.
            rewrite Haccess in H8.
            rewrite /shared.val_of in H6.
            rewrite /permMapsDisjoint_at in sc_perm_disjoint0.
            specialize (sc_perm_disjoint0 k i).
            destruct H3 as (Hneq & Hperm).
            rewrite H Hperm in sc_perm_disjoint0.
            specialize (sc_perm_disjoint0 Hneq).
            simpl in sc_perm_disjoint0.
            rewrite /permMapsDisjoint /= in sc_perm_disjoint0.
            rewrite /coherent /coherent_loc /contents_cohere /access_cohere in H1.
            rewrite /access_cohere in H5.
            destruct (y2 !! loc) eqn: E; last first.
            { rewrite E in H6. inv H6. } 
            rewrite E /= in H6.
            destruct s; last first. inv H6.
            rewrite /resource_at in H5.
            specialize (H5 loc).
            destruct H5 as (_ & _ & HpermHlt1).
            rewrite E in HpermHlt1.
            apply writable_at_perm_order_cases
                  with (x := access_at (restrPermMap Hlt) loc Cur) in Hwrite; auto.
            rewrite /access_at in Hwrite.
            rewrite restrPermMap_Cur_eq in Hwrite.
            pose proof (access_at_restrPermMap_Cur a m loc Hlt1) as Haccess1.
            rewrite Haccess1 in HpermHlt1.
            assert (Hread: Mem.perm_order' (a # (loc.1) loc.2) Readable).
            { rewrite mem_lemmas.po_oo.
              eapply readable_dfrac_perm_order with (Hlt:= Hlt1) (rsh := rsh) ; try eauto.
              rewrite Haccess1; auto. }
            assert (Hwrite1: Mem.perm_order' (p # (loc.1) loc.2) Writable).
            { destruct Hwrite as [Hwrite | Hwrite];
                rewrite mem_lemmas.po_oo; rewrite Hwrite;
                [try apply perm_F_any | apply perm_refl].
            }
            assert (¬ ∃ pu : option permission,
                            perm_union (a # (loc.1) loc.2) (p # (loc.1) loc.2) = Some pu).
            { apply (perm_order_clash (a # (loc.1) loc.2) (p # (loc.1) loc.2)); done. }
            specialize (sc_perm_disjoint0 loc.1 loc.2); easy.
          + rewrite lookup_insert -Hcur_eq; auto.
  - (* getCurPerm m' = add_fresh_block b p
                  ∧ getMaxPerm m' = add_fresh_block b (getMaxPerm m)
                    ∧ Mem.nextblock m' = Pos.succ (Mem.nextblock m) *)
    unshelve iExists (fst (Mem.alloc m lo hi)).
    setoid_rewrite (big_sepM2_delete_l _ _ _ i (g, getCurPerm m')) at 2; auto.
    iDestruct (resource_map.resource_map_auth_valid with "H") as %(_ & Hvalid).
    destruct sc_self_eqs as (Hblk & Hcur_max_eq & Hnxt_eq & Hcnt_eq).
    iExists (<[i := σ']>σs).
    + iExists σ'.
      iSplit; first rewrite lookup_insert //.
      iSplitR "Hbig".
      iFrame. iPureIntro.
      split; auto.
      rewrite /getMaxPerm /=.
      assert (Hlt1: permMapLt (getCurPerm m')
                      (PMap.map (λ (f : Z → perm_kind → option permission) (ofs : Z), f ofs Max)
                         (Mem.mem_access (Mem.alloc m lo hi).1))).
      { rewrite /permMapLt.
        intros b1 ofs1.
        rewrite /getCurPerm /= Hcur_max_eq.
        destruct (Pos.eq_dec b1 (Mem.nextblock m)) as [->|Hneq].
        rewrite !PMap.gmap PMap.gss.
        destruct (zle lo ofs1 && zlt ofs1 hi) eqn:Hrange; try done.
        - apply perm_order''_Freeable.
        - rewrite !PMap.gmap PMap.gso //=.
          exact (Mem.access_max m b1 ofs1).
      }
      exists Hlt1.
      assert (mem_equiv.mem_equiv (restrPermMap Hlt1) m').
      {
        pose proof (Mem_canonical_useful m') as Hcanon.
        assert (Hacc_eq: Mem.mem_access (restrPermMap Hlt1) = Mem.mem_access m').
        { by apply max_cur_equiv. }
        econstructor; try done; last first.
        - rewrite /mem_equiv.content_equiv /Mem.mem_contents /=.
          intros. simpl.
          clear -Hcnt_eq.
          destruct m', m.
          simpl in *.
          by rewrite Hcnt_eq.
        - by apply mem_equiv.mem_access_max_equiv.
        - by apply mem_equiv.mem_access_cur_equiv.
      }
      eapply mem_coherent_equiv; eauto. done.
      rewrite ! delete_insert_delete /getMaxPerm /=.
      iApply (big_sepM2_mono with "Hbig"); intros.
      apply lookup_delete_Some in H4.
      destruct y1.
      iIntros "(%Hlt1 & H1)".
      iFrame "H1".
      iPureIntro.
      destruct Hlt1 as (Hlt1 & Hchr).
      split; auto.
      destruct H4 as [Hik Hσk].
      have Hperms_k : perms !! k = Some (g0, a).
      { rewrite lookup_delete_ne in H3; auto. }
      have Hlt' : permMapLt a (getMaxPerm (Mem.alloc m lo hi).1).
      { Transparent Mem.alloc.
        rewrite /getMaxPerm /Mem.alloc /= -Hcur_max_eq.
        eapply sc_others_still_lt2; eauto.
      }
      exists Hlt'.
      split.
      * intro Hge.
        rewrite restrPermMap_nextblock /= in Hge.
        rewrite /coherent in Hchr.
        apply Hchr.
        rewrite restrPermMap_nextblock /=. lia.
      * rewrite /coherent_loc.
        split.
        ** rewrite /contents_cohere restrPermMap_contents /juicy_mem.contents_at /=.
           intros.
           rewrite /coherent in Hchr.
           specialize (Hchr loc).
           destruct Hchr as (? & Hchr).
           rewrite /coherent_loc /contents_cohere in Hchr.
           destruct Hchr as (Hchr & ?).
           destruct (peq (loc.1) (Mem.nextblock m)) as [Heq1 | Hneq].
           { rewrite /resource_at in H4.
             destruct (y2 !! loc) eqn: E; last first.
             { rewrite E in H4. inv H4. }
             rewrite restrPermMap_nextblock in H5.
             rewrite Heq1 in H5.
             assert (Hge: (Mem.nextblock m >= Mem.nextblock m)%positive). lia.
             apply H5 in Hge. done.
           }
           apply Hchr in H4.
           rewrite /juicy_mem.contents_at in H4.
           have H4m :
             ZMap.get loc.2 (Mem.mem_contents m) # (loc.1) = v.
           { pose proof (f_equal (fun f => f loc) (restrPermMap_contents Hlt1)) as Hc.
             unfold juicy_mem.contents_at in Hc.
             rewrite Hc in H4. auto.
           }
           rewrite PMap.gso; auto. 
        ** rewrite /access_cohere.
           rewrite access_at_restrPermMap_Cur.
           Unshelve.
           rewrite /coherent in Hchr.
           specialize (Hchr loc).
           destruct Hchr as (? & ?).
           rewrite /coherent_loc in H5.
           destruct H5 as (? & ?).
           rewrite /access_cohere in H6.
           rewrite access_at_restrPermMap_Cur in H6. auto.
      + rewrite lookup_insert; auto.
    - unshelve iExists (Mem.unchecked_free m b lo hi).
      setoid_rewrite (big_sepM2_delete_l _ _ _ i (g, getCurPerm m')) at 2; auto.
      destruct sc_self_eqs as (Hblk & Hcur_max_eq & Hnxt_eq & Hcnt_eq).
      iDestruct (resource_map.resource_map_auth_valid with "H") as %(_ & Hvalid).
      iExists (<[i := σ']>σs).
      + iExists σ'.
        iSplit; first rewrite lookup_insert //.
        iSplitR "Hbig".
        iFrame. iPureIntro.
        split; auto.
        rewrite /getMaxPerm /=.
        set acc := (PMap.set b
                        (λ (ofs : Z) (k : perm_kind),
                          if zle lo ofs && zlt ofs hi then None else (Mem.mem_access m) # b ofs k)
                        (Mem.mem_access m)).
        assert (Hlt1: permMapLt (getCurPerm m')
                        (PMap.map (λ (f : Z → perm_kind → option permission) (ofs : Z), f ofs Max) acc)).
        {
          rewrite /permMapLt.
          intros b1 ofs1.
          rewrite /getCurPerm.
          rewrite Hcur_max_eq.
          destruct (peq b1 b) as [->|Hneq].
          - rewrite ! PMap.gmap PMap.gss.
            destruct (zle lo ofs1 && zlt ofs1 hi) eqn:Hrange; try done.
            exact (Mem.access_max m b ofs1).
          - rewrite ! PMap.gmap PMap.gso //=.
            exact (Mem.access_max m b1 ofs1).
        }
        set (m_acc := {|
                 Mem.mem_contents := Mem.mem_contents m;
                 Mem.mem_access := acc;
                 Mem.nextblock := Mem.nextblock m;
                 Mem.access_max := λ (b0 : positive) (ofs : Z),
                   Memory.Mem.unchecked_free_obligation_1 m b lo hi b0 ofs;
                 Mem.nextblock_noaccess :=
                   λ (b0 : positive) (ofs : Z) (k : perm_kind) (H4 : ¬ Plt b0 (Mem.nextblock m)),
                   Memory.Mem.unchecked_free_obligation_2 m b lo hi b0 ofs k H4;
                 Mem.contents_default :=
                   λ b0 : positive, Memory.Mem.unchecked_free_obligation_3 m b0
               |}).
        change (PMap.map (fun (f:Z->perm_kind->option permission) (ofs:Z) => f ofs Max) acc)
          with (getMaxPerm m_acc) in Hlt1.
        exists Hlt1.
        assert (mem_equiv.mem_equiv (restrPermMap Hlt1) m').
        {
          pose proof (Mem_canonical_useful m') as Hcanon.
          econstructor; try done; last first.
          - rewrite /mem_equiv.content_equiv.
            intros. rewrite Hcnt_eq.
            rewrite /Mem.mem_contents /=. done.
          - rewrite /mem_equiv.Max_equiv /mem_equiv.access_map_equiv /getMaxPerm.
            rewrite Hcur_max_eq.
            intros.
            simpl.
            apply functional_extensionality; intros ofs.
            destruct (Pos.eq_dec b0 b) as [->|Hb0neq].
            + by rewrite !PMap.gmap /Maps.PMap.get /= !PTree.gmap !PTree.gss /=.
            + rewrite !PMap.gmap /Maps.PMap.get !PTree.gmap PTree.gso //=.
              destruct ((Mem.mem_access m).2 !! b0)%maps; simpl. done. done.
          - rewrite /mem_equiv.Cur_equiv /mem_equiv.access_map_equiv /getCurPerm.
            intros.
            apply functional_extensionality; intro ofs.
            rewrite !PMap.gmap /restrPermMap /=.
            destruct ((Mem.mem_access m').2 !! b0)%maps as [f|] eqn:Hb0; simpl.
            + rewrite Hcur_max_eq /= /Maps.PMap.get in Hb0.
              rewrite /Maps.PMap.get /= !PTree.gmap.
              rewrite Hb0 /= PTree.gmap1 /option_map.
              destruct ((Mem.mem_access m').2 !! b0)%maps; reflexivity.
            + rewrite Hcur_max_eq /= in Hb0.
              rewrite /Maps.PMap.get /= !PTree.gmap.
              rewrite Hb0 /=.
              destruct ((Mem.mem_access m').2 !! b0)%maps as [x|] eqn:Hb; simpl.
              rewrite Hcur_max_eq in Hb.
              by rewrite Hb in Hb0.
              specialize (Hcanon ofs Cur). done. 
        }
        by eapply mem_coherent_equiv; eauto.
        rewrite ! delete_insert_delete /getMaxPerm /=.
        iApply (big_sepM2_mono with "Hbig"); intros.
        apply lookup_delete_Some in H4.
        destruct y1.
        iIntros "(%Hlt1 & H1)".
        iFrame "H1".
        iPureIntro.
        split; auto.
        destruct Hlt1 as (Hlt1 & Hchr).
        destruct H4 as [Hik Hσk].
        have Hperms_k : perms !! k = Some (g0, a).
        { rewrite lookup_delete_ne in H3; auto. }
        set acc := (PMap.set b
                      (λ (ofs : Z) (k : perm_kind),
                        if zle lo ofs && zlt ofs hi then None else (Mem.mem_access m) # b ofs k)
                      (Mem.mem_access m)).
        assert (Hlt': permMapLt a (PMap.map (λ (f : Z → perm_kind → option permission) (ofs : Z),
                                       f ofs Max) acc)).
        {
          rewrite /acc.
          rewrite /getMaxPerm in sc_others_still_lt2.
          rewrite Hcur_max_eq in sc_others_still_lt2.
          eapply sc_others_still_lt2; eauto.
        }
        exists Hlt'.
        split.
        * intro Hge.
          rewrite restrPermMap_nextblock /= in Hge.
          rewrite /coherent in Hchr.
          apply Hchr.
          rewrite restrPermMap_nextblock /=. lia.
        * rewrite /coherent_loc.
          split.
          ** rewrite /contents_cohere restrPermMap_contents /juicy_mem.contents_at /=.
             intros.
             rewrite /coherent in Hchr.
             specialize (Hchr loc).
             destruct Hchr as (? & Hchr).
             rewrite /coherent_loc /contents_cohere in Hchr.
             destruct Hchr as (Hchr & ?).
             destruct (peq (loc.1) (Mem.nextblock m)) as [Heq1 | Hneq].
             { rewrite /resource_at in H4.
               destruct (y2 !! loc) eqn: E; last first.
               { rewrite E in H4. inv H4. }
               rewrite restrPermMap_nextblock in H5.
               rewrite Heq1 in H5.
               assert (Hge: (Mem.nextblock m >= Mem.nextblock m)%positive). lia.
               apply H5 in Hge. done.
             }
             apply Hchr in H4.
             rewrite /juicy_mem.contents_at in H4.
             have H4m :
               ZMap.get loc.2 (Mem.mem_contents m) # (loc.1) = v.
             { pose proof (f_equal (fun f => f loc) (restrPermMap_contents Hlt1)) as Hc.
               unfold juicy_mem.contents_at in Hc.
               rewrite Hc in H4. auto.
             }
             done.
          ** rewrite /access_cohere.
             rewrite access_at_restrPermMap_Cur.
             Unshelve.
             rewrite /coherent in Hchr.
             specialize (Hchr loc).
             destruct Hchr as (? & ?).
             rewrite /coherent_loc in H5.
             destruct H5 as (? & ?).
             rewrite /access_cohere in H6.
             rewrite access_at_restrPermMap_Cur in H6. auto.
        + rewrite lookup_insert; auto.
        
Admitted.

Lemma conc_state_interp_lookup `{!conc_VSTGS OK_ty Σ} i g p m perms z :
  perms !! i = Some (g, p) →
  conc_state_interp m perms z ⊢ ∃ Hp : permMapLt p (getMaxPerm m), thread_state_interp g (restrPermMap Hp) z ∗ (∀ m', thread_state_interp g m' z -∗ conc_mem_auth m' (<[i:=(g, getCurPerm m')]>perms)).
Proof.
  (* iIntros (?) "(? & $)"; by iApply conc_mem_auth_lookup. *)
  Admitted.

Lemma init_conc_VST: forall Z `{!VSTGpreS Z Σ} (z : Z),
  ⊢ |==> ∀ _ : invGS_gen HasNoLc Σ, ∃ HH : conc_gen_heapGS Σ, ∃ _ : funspecGS Σ, ∃ _ : externalGS Z Σ, ∃ γ0,
    let H : conc_VSTGS Z Σ := ConcVSTGS _ _ (ConcHeapGS _ _ _ _) _ in
    (thread_state_interp γ0 Mem.empty z ∗ funspec_auth ∅ ∗ has_ext z) ∗ ghost_map.ghost_map_auth(H0 := gen_heapGpreS_meta(gen_heapGpreS := conc_gen_heap_inG)) (@conc_gen_meta_name _ HH) 1 ∅.
Proof.
  intros; iIntros.
  iMod gen_heap_init_names_empty as (??) "(? & ?)".
  iMod (own_alloc(A := gmap_view.gmap_viewR address (@funspecO' Σ)) (gmap_view.gmap_view_auth (dfrac.DfracOwn 1) ∅)) as (γf) "?".
  { apply gmap_view.gmap_view_auth_valid. }
  iMod (ext_alloc z) as (?) "(? & ?)".
  iIntros "!>" (?); iExists (ConcGenHeapGS _ _ γm), (FunspecG _ _ γf), _.
  iFrame.
  iSplit => //; iPureIntro.
  apply empty_coherent.
Qed.
(* end concurrency setup *)

Ltac absurd_ext_link_naming :=
  exfalso;
  match goal with
  | H : Some (_ _, _) = _ |- _ =>
    rewrite <- ?H in *
  end;
  unfold funsig2signature in *;
  match goal with
  | H : Some (?ext_link ?a, ?b) <> Some (?ext_link ?a, ?b') |- _ =>
    simpl in H; [contradiction || congruence]
  | H : Some (?ext_link ?a, ?c) = Some (?ext_link ?b, ?d) |- _ =>
    simpl in H;
    match goal with
    | ext_link_inj : forall s1 s2, ext_link s1 = ext_link s2 -> s1 = s2 |- _ =>
      assert (a = b) by (apply ext_link_inj; congruence); congruence
    end
  end.

Ltac funspec_destruct s :=
  simpl (extspec.ext_spec_pre _); simpl (extspec.ext_spec_type _); simpl (extspec.ext_spec_post _);
  unfold funspec2pre, funspec2post;
  let Heq_name := fresh "Heq_name" in
  destruct (oi_eq_dec (Some (_ s, _)) (ef_id_sig _ (EF_external _ _)))
    as [Heq_name | Heq_name]; try absurd_ext_link_naming.

(*+ Final instantiation *)

Record CSL_proof := {
  CSL_Σ : gFunctors;
  CSL_prog : Clight.program;
  CSL_CS: compspecs;
  CSL_V : varspecs;
  CSL_G : @funspecs CSL_Σ;
  CSL_ext_link : string -> ident;
  CSL_ext_link_inj : forall s1 s2, CSL_ext_link s1 = CSL_ext_link s2 -> s1 = s2;
  CSL_all_safe : forall (HH : VSTGS unit CSL_Σ), @semax_prog _ _ HH (concurrent_ext_spec CSL_CS CSL_ext_link)
    CSL_CS CSL_prog tt CSL_V CSL_G;
  CSL_init_mem_not_none : Genv.init_mem CSL_prog <> None;
                   }.

(*
Definition Clight_init_state (prog:Ctypes.program function) main_symb f_main init_mem :=
  State Clight_safety.main_handler
        (Scall None (Etempvar BinNums.xH (type_of_fundef f_main))
               (List.map (fun x : AST.ident * Ctypes.type => Etempvar (fst x) (snd x))
                         (Clight_new.params_of_types (BinNums.xO BinNums.xH)
                                                     (Clight_new.params_of_fundef f_main))))
        (Kseq (Sloop Sskip Sskip) Kstop) empty_env
        (temp_bindings BinNums.xH (cons main_symb nil)) init_mem.
*)

Section Safety.
  Variable CPROOF: CSL_proof.
  Definition Σ := CPROOF.(CSL_Σ).
  Definition CS :=   CPROOF.(CSL_CS).
  Definition V :=   CPROOF.(CSL_V).
  Definition G :=   CPROOF.(CSL_G).
  Definition ext_link :=   CPROOF.(CSL_ext_link).
  Definition ext_link_inj :=   CPROOF.(CSL_ext_link_inj).
  Definition prog :=   CPROOF.(CSL_prog).
  Definition all_safe :=   CPROOF.(CSL_all_safe).
  Definition init_mem_not_none :=   CPROOF.(CSL_init_mem_not_none).
  Definition ge := Clight.globalenv CPROOF.(CSL_prog).

  Definition init_mem : {m : mem | Genv.init_mem (CSL_prog CPROOF) = Some m}.
  Proof.
    pose proof init_mem_not_none.
    destruct (Genv.init_mem (CSL_prog CPROOF)); last done.
    eauto.
  Defined.

(*   Local Instance CEspec (HH : heapGS Σ) (HE : externalGS unit Σ) (HL : lockGS Σ) : OracleKind :=
    Concurrent_Espec unit CS ext_link. *)

  Lemma CEspec_cases : forall `{!VSTGS unit Σ} e
    (x : ext_spec_type (concurrent_ext_spec CS ext_link) e),
    e = LOCK \/ e = UNLOCK \/ e = MKLOCK \/ e = FREE_LOCK \/ e = CREATE.
  Proof.
    intros.
    simpl in x.
    repeat (if_tac in x; [destruct e; try done; inversion H as [H1];
                          apply ext_link_inj in H1 as <-; auto
      | clear H]); last done.
  Qed.

  (* funspecs_destruct isn't working well, so prove a spec lemma for each function *)
  Ltac next_spec := subst; let Hspecs := fresh "Hspecs" in match goal with |-context[add_funspecs_rec _ _ _ ?l] =>
    destruct l eqn: Hspecs; first done;
    injection Hspecs; clear Hspecs; intros Hspecs <-; simpl;
    unfold funspec2pre, funspec2post, ef_id_sig; simpl; if_tac end.

  Ltac solve_spec x := intros; revert x;
    unfold ext_spec_post, concurrent_ext_spec;
    pose proof ext_link_inj as Hinj; fold ext_link in Hinj;
    repeat (next_spec; first absurd_ext_link_naming); next_spec; last done;
    intros; split; [|intros (? & Heq & ?)]; eauto;
    inversion Heq as [Heq0 Heq']; apply inj_pair2 in Heq'; subst; auto.

  Lemma CEspec_acquire_pre : forall `{!VSTGS unit Σ} x args z m,
    ext_spec_pre (concurrent_ext_spec CS ext_link) LOCK x (genv_symb_injective ge) (sig_args (ef_sig LOCK)) args z m <->
    match acquire_spec with mk_funspec _ _ A _ P _ => exists x'', JMeq.JMeq x x'' /\ funspec2pre' _ A P x'' (genv_symb_injective ge) (sig_args (ef_sig LOCK)) args z m end.
  Proof.
    solve_spec x.
  Qed.

  Lemma CEspec_acquire_post : forall `{!VSTGS unit Σ} x ret z m,
    ext_spec_post (concurrent_ext_spec CS ext_link) LOCK x (genv_symb_injective ge) (sig_res (ef_sig LOCK)) ret z m <->
    match acquire_spec with mk_funspec _ _ A _ _ Q => exists x'', JMeq.JMeq x x'' /\ funspec2post' _ A Q x'' (genv_symb_injective ge) (sig_res (ef_sig LOCK)) ret z m end.
  Proof.
    solve_spec x.
  Qed.

  Lemma CEspec_release_pre : forall `{!VSTGS unit Σ} x args z m,
    ext_spec_pre (concurrent_ext_spec CS ext_link) UNLOCK x (genv_symb_injective ge) (sig_args (ef_sig UNLOCK)) args z m <->
    match release_spec with mk_funspec _ _ A _ P _ => exists x'', JMeq.JMeq x x'' /\ funspec2pre' _ A P x'' (genv_symb_injective ge) (sig_args (ef_sig UNLOCK)) args z m end.
  Proof.
    solve_spec x.
  Qed.

  Lemma CEspec_release_post : forall `{!VSTGS unit Σ} x ret z m,
    ext_spec_post (concurrent_ext_spec CS ext_link) UNLOCK x (genv_symb_injective ge) (sig_res (ef_sig UNLOCK)) ret z m <->
    match release_spec with mk_funspec _ _ A _ _ Q => exists x'', JMeq.JMeq x x'' /\ funspec2post' _ A Q x'' (genv_symb_injective ge) (sig_res (ef_sig UNLOCK)) ret z m end.
  Proof.
    solve_spec x.
  Qed.

  Lemma CEspec_makelock_pre : forall `{!VSTGS unit Σ} x args z m,
    ext_spec_pre (concurrent_ext_spec CS ext_link) MKLOCK x (genv_symb_injective ge) (sig_args (ef_sig MKLOCK)) args z m <->
    match makelock_spec CS with mk_funspec _ _ A _ P _ => exists x'', JMeq.JMeq x x'' /\ funspec2pre' _ A P x'' (genv_symb_injective ge) (sig_args (ef_sig MKLOCK)) args z m end.
  Proof.
    solve_spec x.
  Qed.

  Lemma CEspec_makelock_post : forall `{!VSTGS unit Σ} x ret z m,
    ext_spec_post (concurrent_ext_spec CS ext_link) MKLOCK x (genv_symb_injective ge) (sig_res (ef_sig MKLOCK)) ret z m <->
    match makelock_spec CS with mk_funspec _ _ A _ _ Q => exists x'', JMeq.JMeq x x'' /\ funspec2post' _ A Q x'' (genv_symb_injective ge) (sig_res (ef_sig MKLOCK)) ret z m end.
  Proof.
    solve_spec x.
  Qed.

  Lemma CEspec_freelock_pre : forall `{!VSTGS unit Σ} x args z m,
    ext_spec_pre (concurrent_ext_spec CS ext_link) FREE_LOCK x (genv_symb_injective ge) (sig_args (ef_sig FREE_LOCK)) args z m <->
    match freelock_spec CS with mk_funspec _ _ A _ P _ => exists x'', JMeq.JMeq x x'' /\ funspec2pre' _ A P x'' (genv_symb_injective ge) (sig_args (ef_sig FREE_LOCK)) args z m end.
  Proof.
    solve_spec x.
  Qed.

  Lemma CEspec_freelock_post : forall `{!VSTGS unit Σ} x ret z m,
    ext_spec_post (concurrent_ext_spec CS ext_link) FREE_LOCK x (genv_symb_injective ge) (sig_res (ef_sig FREE_LOCK)) ret z m <->
    match freelock_spec CS with mk_funspec _ _ A _ _ Q => exists x'', JMeq.JMeq x x'' /\ funspec2post' _ A Q x'' (genv_symb_injective ge) (sig_res (ef_sig FREE_LOCK)) ret z m end.
  Proof.
    solve_spec x.
  Qed.

  Lemma CEspec_spawn_pre : forall `{!VSTGS unit Σ} x args z m,
    ext_spec_pre (concurrent_ext_spec CS ext_link) CREATE x (genv_symb_injective ge) (sig_args (ef_sig CREATE)) args z m <->
    match spawn_spec with mk_funspec _ _ A _ P _ => exists x'', JMeq.JMeq x x'' /\ funspec2pre' _ A P x'' (genv_symb_injective ge) (sig_args (ef_sig CREATE)) args z m end.
  Proof.
    solve_spec x.
  Qed.

  Lemma CEspec_spawn_post : forall `{!VSTGS unit Σ} x ret z m,
    ext_spec_post (concurrent_ext_spec CS ext_link) CREATE x (genv_symb_injective ge) (sig_res (ef_sig CREATE)) ret z m <->
    match spawn_spec with mk_funspec _ _ A _ _ Q => exists x'', JMeq.JMeq x x'' /\ funspec2post' _ A Q x'' (genv_symb_injective ge) (sig_res (ef_sig CREATE)) ret z m end.
  Proof.
    solve_spec x.
  Qed.

  Program Definition spr (HH : VSTGS unit Σ) :=
    semax_prog_rule (concurrent_ext_spec CS ext_link) V G prog
      (proj1_sig init_mem) 0 tt _ (all_safe HH) (proj2_sig init_mem).
  Next Obligation.
  Proof. intros ?????; apply I. Qed.

  Check @jsafe.

  Instance Sem : Semantics := ClightSemanticsForMachines.ClightSem (Clight.globalenv CPROOF.(CSL_prog)).

  Existing Instance HybridMachineSig.HybridCoarseMachine.DilMem.
  Existing Instance HybridMachineSig.HybridCoarseMachine.scheduler.

  (* If there are enough of these conditions, re-split out into semax_invariant. *)
  Definition dtp := t(ThreadPool := @OrdinalPool.OrdinalThreadPool dryResources Sem).

(*  (* We want to enforce additional coherence properties between the rmap and the memory, accounting
     for the effects of locks (and other things?). *)
  Definition lock_coherent_loc m loc (r : dfrac * option resource) : Prop :=
    match r.2 with
    | Some (LK _ _ b) => Mem.load Mptr m loc.1 loc.2 = Some (Vptrofs (if b then Ptrofs.zero else Ptrofs.one))
    | _ => True
    end.

  Definition lock_coherent m σ := forall loc, lock_coherent_loc m loc (σ @ loc).

  Definition mem_auth' `{!heapGS Σ} m := ∃ σ, ⌜coherent m σ ∧ lock_coherent m σ⌝ ∧ resource_map.resource_map_auth(H0 := gen_heapGpreS_heap(gen_heapGpreS := gen_heap_inG)) (gen_heap_name _) 1 σ.
  Definition state_interp' {Z} `{!heapGS Σ} `{!externalGS Z Σ} m z := mem_auth' m ∗ ext_auth z.*)

  (* Each thread needs to be safe given only its fragment (access_map) of the shared memory. We use
     the current max permissions as an upper bound on the max permissions of the state_interp. *)

  Section conc_heap.

  Context `{!conc_VSTGS unit Σ}.

  Program Definition jsafe_perm_pre g
    (jsafe : coPset -d> unit -d> CC_core -d> (access_map * access_map) -d> iPropO Σ) :
    coPset -d> unit -d> CC_core -d> (access_map * access_map) -d> iPropO Σ := λ E z c '(p, max),
      |={E}=> ∀ m, ⌜mem_equiv.access_map_equiv (getCurPerm m) p ∧ getMaxPerm m = max⌝ → thread_state_interp(*'*) g m z -∗
        (∃ i, ⌜halted (cl_core_sem ge) c i ∧ ext_spec_exit (concurrent_ext_spec(VSTGS0 := thread_VSTGS g) CS ext_link) (Some (Vint i)) z m⌝) ∨
        (|={E}=> ∃ c' m', ⌜corestep (cl_core_sem ge) c m c' m'⌝ ∧ thread_state_interp(*'*) g m' z (* ?? *) ∗ ▷ jsafe E z c' (getCurPerm m', getMaxPerm m')) ∨
        (∃ e args x, ⌜at_external (cl_core_sem ge) c m = Some (e, args) ∧ ext_spec_pre (concurrent_ext_spec CS ext_link) e x (genv_symb_injective ge) (sig_args (ef_sig e)) args z m⌝ ∧
           ▷ (∀ ret m' z', ⌜Val.has_type_list args (sig_args (ef_sig e)) ∧ Builtins0.val_opt_has_rettype ret (sig_res (ef_sig e))⌝ →
            ⌜ext_spec_post (concurrent_ext_spec(VSTGS0 := thread_VSTGS g) CS ext_link) e x (genv_symb_injective ge) (sig_res (ef_sig e)) ret z' m'⌝ → |={E}=>
                ∃ c', ⌜after_external (cl_core_sem ge) ret c m' = Some c'⌝ ∧ thread_state_interp(*'*) g m' z' ∗ jsafe E z' c' (getCurPerm m', getMaxPerm m'))).

  Local Instance jsafe_perm_pre_contractive g : Contractive (jsafe_perm_pre g).
  Proof.
    rewrite /jsafe_perm_pre => n jsafe jsafe' Hsafe E z c [??].
    do 14 f_equiv.
    - try f_contractive; repeat f_equiv. apply Hsafe.
    - f_contractive; repeat f_equiv. apply Hsafe.
  Qed.


  Local Definition jsafe_perm_def g : coPset -> unit -> CC_core -> _ -> iProp Σ := fixpoint (jsafe_perm_pre g).
  Local Definition jsafe_perm_aux : seal (jsafe_perm_def). Proof. by eexists. Qed.
  Definition jsafe_perm := jsafe_perm_aux.(unseal).
  Local Lemma jsafe_perm_unseal : jsafe_perm = jsafe_perm_def.
  Proof. rewrite -jsafe_perm_aux.(seal_eq) //. Qed.


  Lemma jsafe_perm_unfold g E z c p :
    jsafe_perm g E z c p ⊣⊢ jsafe_perm_pre g (jsafe_perm g) E z c p.
  Proof.
    rewrite jsafe_perm_unseal.
    apply (fixpoint_unfold (jsafe_perm_pre g)).
  Qed.

  (*
  Lemma jsafe_perm_mono : forall `{!VSTGS unit Σ} p1 p2 E z c p, permMapLt p2 p1 ->
    jsafe_perm E z c p1 ⊢ jsafe_perm E z c p.
  Proof.
    intros.
    iLöb as "IH" forall (p H z c).
    rewrite !jsafe_perm_unfold /jsafe_perm_pre.
    iIntros ">H !>" (?? (Hmax & Hcur)) "S".
    pose proof (PreOrder_Transitive _ _ _ Hmax H).
    iDestruct ("H" with "[%] [S]")as "?"; eauto.
    Set Printing Implicit.
    try done.
    iPureIntro.
    instantiate (1 := m).
    iPureIntro.
    instantiate (1:= m). admit.
    iPureIntro.
    iDestruct ("H" with "S") as "[H | [H | H]]"; first done.
    - iLeft; done.
    - iRight; iLeft.
      iMod "H" as (???) "(? & ?)".
      iIntros "!>"; iExists _, _; iSplit; first done; iFrame.
      by iApply "IH".
    - iRight; iRight.
      iDestruct "H" as (????) "H".
      iExists _, _, _; iSplit; first done.
      iNext; iIntros (?????).
      iMod ("H" with "[%] [%]") as (??) "(? & ?)"; [done..|].
      iIntros "!>"; iExists _; iSplit; first done; iFrame.
      by iApply "IH".
  Qed.
*)
  Existing Instance mem_equiv.access_map_equiv_Equivalence.

  (*
  Lemma jsafe_perm_equiv : forall `{!VSTGS unit Σ} p E z c p1 p2, mem_equiv.access_map_equiv p1.1 p2.1 ->
     jsafe_perm p E z c p1 ⊢ jsafe_perm p E z c p2.
  Proof.
    intros.
    iLöb as "IH" forall (p z c p1 p2 H).
    rewrite !jsafe_perm_unfold /jsafe_perm_pre.
    iIntros ">H !>" (?? (Hmax & Hcur)) "S".
    assert (permMapLt p1.1 (getMaxPerm m)) as Hlt1.
    { rewrite -Hcur in Hlt.
      eapply mem_equiv.permMapLt_equiv; eauto.
      instantiate (1 := (getMaxPerm m)); try done.
      rewrite -Hcur. apply cur_lt_max.
    }
    iDestruct ("H" $! _ Hlt1 with "[%] S") as "[H | [H | H]]".
    { split; auto.
      rewrite -Hcur in H.
      rewrite /mem_equiv.access_map_equiv in H.
    - iLeft; done.
    - iRight; iLeft.
      iMod "H" as (???) "(S & Hsafe)".
      Check restrPermMap_ext.
      iIntros "!>"; iExists _, _; iSplit; first done.
      iFrame.
    - iRight; iRight.
      iDestruct "H" as (????) "H".
      iExists _, _, _; iSplit.
      + done.
      + iNext; iIntros (?????).
        iMod ("H" with "[%] [%]") as (??) "(? & ?)"; [done..|].
        iIntros "!>". iExists _. iFrame.
        iPureIntro. done.
  Qed.

*)

  (*
    Hlt : permMapLt max (getMaxPerm m)

    m1 = (getCurPerm m) 
    m2 = (getCurPerm (restrPermMap Hlt))

   *)

  (*
    b1 :
    Max : Writable
    Cur : Readable

    Cur : Writable 

   *)


(*  Axiom external_call_memLt
    : ∀ (ef : external_function) (ge : Senv.t) (vargs : list val) (m1 : mem) 
        (t : Events.trace) (vres : val) (m2 m1' : mem),
      Events.external_call ef ge vargs m1 t vres m2
      → memLt m1 m1'
      → ∃ (m2' : mem),
          (Events.external_call ef ge vargs m1' t vres m2'
           ∧ memLt m2 m2' ∧ Mem.unchanged_on (Events.loc_out_of_bounds m1) m1' m2')%type. (* for builtins only? *)

  Lemma alloc_step_step m1 m2 xs e:
    forall m1', memLt m1 m2 -> alloc_variables ge empty_env m1 xs e m1'
           -> exists m2', alloc_variables ge empty_env m2 xs e m2' /\ memLt m1' m2'.
  Proof. intros; eapply alloc_variables_memLt_gen in H0; eauto. Qed.

  Lemma cl_step_step m1 m2 (c c': CC_core):
    forall m1', memLt m1 m2 ->
           cl_step ge c m1 c' m1' -> exists m2', cl_step ge c m2 c' m2' /\ memLt m1' m2'.
  Proof.
    intros.
    inv H0.
    (* 1st case *)
    apply Clight_evsem.assign_locT_ax2 in H4.
    destruct H4 as (?& Hassign).
    eapply assign_locT_sub_memLt with (m1 := m2) in Hassign.
    destruct Hassign as (m2' & HmemLt1 & Hassign); auto.
    eexists; esplit.
    eapply step_assign; eauto.
    eapply eval_expr_eval_lvalue_memLt; eauto; econstructor; auto. auto.
    eapply eval_expr_eval_lvalue_memLt; eauto; econstructor.
    erewrite sem_cast_memLt; eauto.
    eapply Clight_evsem.assign_locT_ax1; eauto. auto. auto.
    (* 2nd case *)
    eexists; esplit.
    eapply step_set; eapply eval_expr_memLt; eauto. auto.
    (* 3rd case *)
    eexists; esplit.
    eapply step_call; eauto.
    eapply eval_expr_memLt; eauto.
    eapply eval_exprlist_memLt; eauto. auto.
    (* 4th case *)
    eexists; esplit.
    eapply step_builtin; eauto.
    eapply eval_exprlist_memLt; eauto.
    eapply external_call_memLt in H3; eauto.
    admit. admit.
    (* 5th case *)
    eexists; esplit.
    econstructor; eauto. auto.
    (* 6th case *)
    eexists; esplit. econstructor; eauto. auto.
    (* 7th case *)
    eexists; esplit. econstructor; eauto. auto.
    eexists; esplit. econstructor; eauto. auto.
    (**)
    eexists; esplit.
    eapply step_ifthenelse; eauto.
    eapply eval_expr_memLt; eauto.
    eapply bool_val_memLt; eauto. auto.
    (**)
    eexists; esplit. econstructor; eauto. auto.
    eexists; esplit. econstructor; eauto. auto.
    eexists; esplit. econstructor; eauto. auto.
    eexists; esplit. econstructor; eauto. auto.
    eexists; esplit. econstructor; eauto. auto.
    (**)
    eapply free_list_memLt with (m2 := m2) in H1.
    destruct H1 as (? & H1 & ?). try done.
    eexists; esplit.
    eapply step_return_0.
    instantiate (1 := x). apply H1. auto. auto.
    (**)
    eapply free_list_memLt with (m2 := m2) in H3.
    destruct H3 as (? & H3 & ?). try done.
    eexists; esplit.
    econstructor.
    eapply eval_expr_memLt; eauto.
    eapply sem_cast_memLt; eauto.
    instantiate (1 := x); auto. auto. auto.
    (**)
    eapply free_list_memLt with (m2 := m2) in H2.
    destruct H2 as (? & H2 & ?).
    eexists; esplit.
    eapply step_skip_call; eauto. auto. auto.
    (**)
    eexists; esplit. econstructor; eauto. auto.
    eapply eval_expr_eval_lvalue_memLt; eauto; econstructor; auto. auto.
    (**)
    eexists; esplit. econstructor; eauto. auto.
    (**)
    eexists; esplit. econstructor; eauto. auto.
    (**)
    eexists; esplit. econstructor; eauto. auto.
    (**)
    eexists; esplit. econstructor; eauto. auto.
    (**)
    inv H1.
    eapply alloc_variables_memLt_gen with (m2 := m2) in H4.
    destruct H4 as (? &? & ?).
    eexists; esplit. eapply step_internal_function.
    eapply function_entry2_intro; eauto. auto. auto.
    (**)
    eexists; esplit. econstructor; eauto. auto.
    admit. admit.
    eexists; esplit. econstructor; eauto. auto.
  Admitted. *)

  Lemma permMapLt_cur: forall p m (Hlt : permMapLt (getCurPerm p) (getCurPerm m)),
      permMapLt (getCurPerm p) (getMaxPerm m).
  Proof.
    intros.
    etrans; first apply Hlt.
    apply cur_lt_max.
  Qed.

  Lemma restr_permMapLt: forall (m1 m2 : mem) (M: memLt m1 m2)
      (M1: getMaxPerm m2 = getMaxPerm m1) (Hlt : permMapLt (getCurPerm m1) (getMaxPerm m2)),
      restrPermMap Hlt = m1.
  Proof.
    intros.
    destruct M as (? & ? & ? & ?).
    pose proof (Mem_canonical_useful m1) as Hcanon.
    destruct m1, m2.
    apply Mem.mkmem_ext.
    simpl in * ; auto.
    destruct mem_access, mem_access0; simpl.
    apply f_equal_prod; auto.
    - extensionality; extensionality k.
      destruct k; auto.
      simpl in *.
      rewrite /getMaxPerm /= in M1.
      inv M1.
      by specialize (f_equal (fun f => f x) H4).
    - rewrite /getMaxPerm /= in M1.
      inv M1.
      apply PTree.extensionality; intros.
      pose proof (f_equal (fun tr => PTree.get i tr) H5) as Hb.
      rewrite !PTree.gmap1 in Hb.
      rewrite PTree.gmap.
      destruct (PTree.get i t1) as [f1|] eqn:E1;
        destruct (PTree.get i t0) as [f2|] eqn:E2; simpl in *; try congruence.
      inversion Hb as [Hf]; clear Hb; subst.
      f_equal.
      clear H4.
      extensionality ofs k.
      destruct k; simpl.
      + exact (f_equal (fun g => g ofs) Hf).
      + rewrite getCurPerm_correct /permission_at /PMap.get /=.
        rewrite E2; auto.
    - auto.
   Qed.

  Lemma permMapLt_cur_restr: forall (m : mem) (max : access_map) (Hlt : permMapLt max (getMaxPerm m))
                               (Hmax : permMapLt (getMaxPerm m) max),
      permMapLt (getCurPerm m) (getCurPerm (restrPermMap Hlt)).
  Proof.
    intros ???? b ofs.
    pose proof (@mem_equiv.getCur_restr max m Hlt) as Heq.
    eapply (perm_order''_trans _ ((getMaxPerm m) # b ofs)); last first; try apply getCur_Max.
    rewrite /mem_equiv.access_map_equiv in Heq.
    rewrite /permMapLt /Mem.perm_order'' in Hmax.
    specialize (Heq b).
    specialize (Hmax b ofs).
    by rewrite -Heq in Hmax.
  Qed.

  Lemma jsafe_jsafe_perm : forall g E z c p1 p2,
    jsafe(genv_symb := genv_symb_injective)(gen_heapGS0 := thread_gen_heapGS g) (cl_core_sem ge) (concurrent_ext_spec(VSTGS0 := thread_VSTGS g) CS ext_link) ge E z c ⊢
    jsafe_perm g E z c (p1, p2).
  Proof.
    intros.
    iLöb as "IH" forall (p1 p2 z c).
    rewrite jsafe_unfold jsafe_perm_unfold /jsafe_pre /jsafe_perm_pre.
    iIntros ">H !>" (? (? & <-)) "S".
    iDestruct ("H" with "S") as "[H | [H | H]]".
    - by iLeft.
    - iRight; iLeft.
      iMod "H" as (??) "($ & $ & Hsafe)".
      iIntros "!> !>"; by iApply "IH".
    - iRight; iRight.
      iDestruct "H" as (??? (? & ?)) "H".
      iExists _, _, _; iSplit; first done.
      iIntros "!>" (?????).
      iMod ("H" with "[%] [%]") as (?) "($ & $ & Hsafe)"; [done..|].
      by iApply "IH".
  Qed.

  (*
  Lemma jsafe_jsafe_perm1 : forall `{!VSTGS unit Σ} max E z c p, p = max ->
   jsafe(genv_symb := genv_symb_injective) (cl_core_sem ge) (concurrent_ext_spec CS ext_link) ge E z c ⊢ jsafe_perm max E z c p.
  Proof.
    intros.
    iLöb as "IH" forall (p H z c).
    rewrite jsafe_unfold jsafe_perm_unfold /jsafe_pre /jsafe_perm_pre.
    iIntros ">H !>" (?? Hmax) "S".
    subst; pose proof (partial_order_antisym mem_equiv.permMapLt_order _ _ Hlt) as Heq.
    clear Heq.
(*    iDestruct "S" as "((% & (% & %Hlock) & Hm) & Hz)". *)
    iDestruct ("H" with "S") as "[H | [H | H]]".
    - by iLeft.
    - iRight; iLeft.
      iMod "H" as (???) "(S & Hsafe)".
      iIntros "!>".
      eapply (cl_step_step m (restrPermMap Hlt)) in H.
      destruct H as (? & ?).
      iExists c', x.
      iSplit.
      { destruct H; try done. }
      destruct H as (Hcl & HmemLt).
      rewrite /memLt in HmemLt.
      destruct HmemLt as (Hperm & Hcontent & Hnext & HgetMax).
      2 :
        { repeat split; auto.
          apply permMapLt_cur_restr; auto.
          rewrite restr_Max_eq; auto.
      }
      iSplitL "S".
      { iExists (getCurPerm m').
        assert (permMapLt (getCurPerm m') (getMaxPerm x)) as Hltm'.
        { apply permMapLt_cur; auto. }
        iExists Hltm'.
        rewrite restr_permMapLt; auto.
        split; auto.
      }
      iNext.
      iApply ("IH" with "[%] Hsafe"). admit.
    - iRight. iRight. admit.
   Admitted.

  (* remove p = max, then change jsafe_perm max E z c p into jsafe_perm p E z c p *)
  Lemma jsafe_jsafe_perm : forall `{!VSTGS unit Σ} E z c p,
    jsafe(genv_symb := genv_symb_injective) (cl_core_sem ge) (concurrent_ext_spec CS ext_link) ge E z c ⊢ jsafe_perm p E z c p.
  Proof.
    intros.
    iLöb as "IH" forall (p z c).
    rewrite jsafe_unfold jsafe_perm_unfold /jsafe_pre /jsafe_perm_pre.
    iIntros ">H !>" (?? Hmax) "S".
    subst; pose proof (partial_order_antisym mem_equiv.permMapLt_order _ _ Hlt Hmax) as Heq.
    iDestruct ("H" with "S") as "[H | [H | H]]".
    - by iLeft.
    - iRight; iLeft.
      iMod "H" as (???) "(S & Hsafe)".
      iIntros "!>".
      eapply (cl_step_step _ (restrPermMap Hlt)) in H.
      destruct H as (? & ?).
      rewrite /cl_step in H.
      iExists c', x.
      iSplit.
      { destruct H; try done. }
      destruct H as (Hcl & HmemLt).
      destruct HmemLt as (Hperm & Hcontent & Hnext & HgetMax).
      2 :
      { repeat split; auto.
        apply permMapLt_cur_restr; auto.
        rewrite restr_Max_eq; auto.
      }
      iSplitL "S".
      { iExists (getCurPerm m').
        assert (permMapLt (getCurPerm m') (getMaxPerm x)) as Hltm'.
        { apply permMapLt_cur; auto. }
        iExists Hltm'.
        rewrite restr_permMapLt; auto.
        split; auto.
      }
      iNext.
      (* iApply ("IH" with "Hsafe"). *)
      admit.
    - iRight; iRight.
      iDestruct "H" as (??? (? & ?)) "H".
      assert (ext_spec_pre (concurrent_ext_spec CS ext_link) e x (genv_symb_injective ge)
       (sig_args (ef_sig e)) args z (restrPermMap Hlt)) by admit.
      iExists _, _, _; iSplit; first done.
      iIntros "!>" (?????).
      iMod ("H" with "[%] [%]") as (??) "(S & Hsafe)"; [done..|].
      iIntros "!>"; iExists _; iSplit; first done.
  (*  iFrame; iApply ("IH" with "[%] Hsafe").
      simpl in H, H4. *)
  Admitted.
*)

  Section Scratch.
    Variable tp : dtp.
    Variable i  : nat.
    Variable cnt : containsThread tp i.


    Check (getThreadR cnt).
    (* Coq usually simplifies this: *)
    Print res.  (* confirms it's Resources -> Type *)
    Check Resources.

    (* Check the projection form *)
    Check ((getThreadR cnt).1).
  End Scratch.

  Definition thread_safe max (tp : dtp) i g :=
    ∃ cnti : containsThread tp i,
    match getThreadC cnti with
    | Krun c | Kblocked c => jsafe_perm g ⊤ tt c ((getThreadR cnti).1, max)
    | Kresume c v =>
      ∀ c',
        (* [v] is not used here. The problem is probably coming from
           the definition of JuicyMachine.resume_thread'. *)
        ⌜cl_after_external None c = Some c'⌝ →
        jsafe_perm g ⊤ tt c' ((getThreadR cnti).1, max)
    | Kinit v1 v2 =>
      ∃ q_new,
      ⌜cl_initial_core ge v1 (v2 :: nil) = Some q_new⌝ ∧
      jsafe_perm g ⊤ tt q_new ((getThreadR cnti).1, max)
    end%I.

  Definition threads_safe max (tp : dtp) (gs : gmap nat gname) :=
    [∗ list] i ∈ seq 0 (pos.n (OrdinalPool.num_threads tp)), ∃ g, ⌜gs !! i = Some g⌝ ∧ thread_safe max tp i g.

  Definition threads_wellformed (tp : dtp) :=
    forall i (cnti : containsThread(ThreadPool := OrdinalPool.OrdinalThreadPool) tp i),
    match getThreadC cnti with
    | Krun q => Logic.True
    | Kblocked q => cl_at_external q <> None
    | Kresume q v => cl_at_external q <> None /\ v = Vundef
    | Kinit _ _ => Logic.True
    end.

  Definition locks_coherent (tp : dtp) (m : mem) (ls : gmap address unit) :=
    forall l, (l ∈ dom ls -> lockRes tp l <> None /\ (Mem.load Mptr m l.1 l.2 = Some (Vptrofs Ptrofs.zero) <-> lockRes tp l = Some (empty_map, empty_map))).

(*  Definition other_threads_safe max tp (gs : gmap nat gname) i :=
    ∀ Ψ, □ (∀ k j g, ⌜seq 0 (pos.n (OrdinalPool.num_threads tp)) !! k = Some j⌝ → ⌜k ≠ i⌝ →
        thread_safe max tp j g -∗ Ψ k j) -∗
      Ψ i i -∗ [∗ list] k↦y ∈ seq 0 (pos.n (OrdinalPool.num_threads tp)), Ψ k y. *)

  (*
  Definition post_safe `{!VSTGS unit Σ} max sig x c args k : mpred :=
    ∀ (ret : option val) (m' : mem) z',
      ⌜Val.has_type_list args (sig_args sig) ∧ Builtins0.val_opt_has_rettype ret (sig_res sig)⌝ →
      ⌜ext_spec_post (concurrent_ext_spec CS ext_link) LOCK x (genv_symb_injective ge) (sig_res sig) ret z' m'⌝ →
      |={⊤}=> ∃ c' : CC_core, ⌜after_external (cl_core_sem ge) ret (Callstate c args k) m' = Some c'⌝ ∧
        state_interp m' z' ∗ jsafe_perm max ⊤ z' c' (getCurPerm m').
*)

  
(*
 (* these lemmas could be split off again into semax_acquire_safety, etc. *)
  Lemma acquire_safe `{!VSTGS unit Σ} tp m ls i
    (Htp_wf : threads_wellformed tp) (Hinvariant : invariant tp) (Hcompat : HybridMachineSig.mem_compatible tp m)
    (cnti : containsThread tp i) argsty retty cc k args
    (Hi : getThreadC cnti = Kblocked (Callstate (Ctypes.External LOCK argsty retty cc) args k))
    p (Hmax : permMapLt p (getMaxPerm m)) (Hlt0 : permMapLt (getThreadR cnti).1 (getMaxPerm (restrPermMap Hmax)))
    x (Hpre : ext_spec_pre (concurrent_ext_spec CS ext_link) LOCK x (genv_symb_injective ge) (sig_args (ef_sig LOCK)) args () (restrPermMap Hlt0)) :
    ⊢ other_threads_safe (getMaxPerm m) tp i -∗
      ▷ post_safe (getMaxPerm m) (ef_sig LOCK) x (Ctypes.External LOCK argsty retty cc) args k -∗
      (* lock_set ls -∗ *)
      |={⊤}[∅]▷=> ∃ (tp' : t) (m' : mem) (ev : Events.sync_event),
        ⌜threads_wellformed tp' ∧ invariant tp' ∧ mem_compatible tp' m' ∧ locks_coherent tp' m' ls ∧ syncStep true cnti Hcompat tp' m' ev⌝ ∧
        threads_safe (getMaxPerm m') tp' ∗ (∃ (p0 : access_map) (Hlt : permMapLt p0 (getMaxPerm m')), state_interp (restrPermMap Hlt) ()) (* ∗ lock_set ls *).
  Proof.
    iIntros "Hsafe Hpost".
    apply CEspec_acquire_pre in Hpre as (x' & Heqx & Hpre).
    destruct x' as ((n, phi), ((l, sh), R)); simpl in Hpre.
    destruct Hpre as (Hvphi & Hty & Hpre).
    set (c := Callstate (Ctypes.External LOCK argsty retty cc) args k).
    destruct args as [|arg args]; simpl in Hty; first done.
    destruct Hty as (Hty & Htys); destruct args; last done.
    clear Htys.
    assert (readable_share sh /\ val_lemmas.isptr arg) as (Hsh & Hisptr).
    { revert Hpre; rewrite /PROPx /PARAMSx /GLOBALSx /LOCALx /SEPx; monPred.unseal; ouPred.unseal.
      intros (? & ? & ? & _ & (? & _) & [=] & _ & ? & ? & ? & Hlock & _).
      pose proof (lockinv_isptr sh l R) as [Heq].
      apply Heq in Hlock.
      revert Hlock; ouPred.unseal; intros (? & _); subst; done.
      { eapply cmra_validN_op_l, ora_validN_orderN; last done.
        eapply cmra_validN_op_r, ora_validN_orderN; done. } }
    destruct arg as [| | | | | b ofs]; try done.
    clear Hty Hisptr.
    (* Does the ls ghost state actually work? We don't have that phi is true in the current state. *)
    assert (ext_step cnti Hcompat (updLockSet (updThread cnti (Kresume c Vundef) newThreadPerm) (b, Ptrofs.intval ofs) (empty_map, empty_map)) m' (Events.acquire (b, Ptrofs.intval ofs) (Some (build_delta_content virtueThread.1 m')))) as Hstep.

    iMod ("Hpost" with "[%] [%]").
  Admitted. *)

  End conc_heap.

  Existing Instance HybridMachine.DryHybridMachine.DryHybridMachineSig.

  Theorem dry_safety `{!VSTGpreS unit Σ} `{!inG Σ (gmap_view.gmap_viewR address unitR)} sch n : exists b c_init,
    Genv.find_symbol (globalenv prog) (Ctypes.prog_main prog) = Some b /\
    cl_initial_core (globalenv prog) (Vptr b Ptrofs.zero) [] = Some c_init /\
    HybridMachineSig.HybridCoarseMachine.csafe
       (ThreadPool:= threadPool.OrdinalPool.OrdinalThreadPool(Sem:=ClightSem ge))
     (sch, [],
      DryHybridMachine.initial_machine(Sem := Sem) (getCurPerm (proj1_sig init_mem))
        c_init) (proj1_sig init_mem) n.
  Proof.
    eapply ouPred.pure_soundness, (step_fupdN_soundness_no_lc' _ (S n) O); [apply _..|].
    simpl; intros; iIntros "_".
    iMod (@init_conc_VST _ _ VSTGpreS0 tt) as "H".
    iDestruct ("H" $! Hinv) as (?? HE γ0) "(H & ?)".
    iMod (own_alloc(A := gmap_view.gmap_viewR address unit) (gmap_view.gmap_view_auth (dfrac.DfracOwn 1) ∅)) as (γl) "locks".
    { apply gmap_view.gmap_view_auth_valid. }
    set (HC := ConcVSTGS _ _ (ConcHeapGS _ _ _ _) HE).
    destruct (spr (thread_VSTGS γ0)) as (b & q & (? & ? & Hinit) & Hsafe); [| done..].
    iMod (Hsafe with "H") as "(S & Hsafe)".
    iAssert (|={⊤}[∅]▷=>^n ⌜HybridMachineSig.HybridCoarseMachine.csafe
         (ThreadPool:= threadPool.OrdinalPool.OrdinalThreadPool(Sem:=ClightSem ge))
       (sch, [],
        DryHybridMachine.initial_machine(Sem := Sem) (getCurPerm (proj1_sig init_mem))
          q) (proj1_sig init_mem) n⌝) with "[S Hsafe locks]" as "Hdry".
    2: { iApply step_fupd_intro; first done.
         iNext; iApply (step_fupdN_mono with "Hdry").
         iPureIntro. intros.
         eexists. eexists. split; first done; split; first apply Hinit; done.
    }
    clear Hinit Hsafe.
    rewrite bi.and_elim_l.
    set (tp := initial_machine _ _).
    assert (invariant tp) as Hinvariant by apply ThreadPoolWF.initial_invariant0.
    assert (HybridMachineSig.mem_compatible tp (`init_mem)) as Hcompat
        by apply ThreadPoolWF.initial_mem_compatible.
    assert (threads_wellformed tp) as Htp_wf by done.
    iPoseProof (thread_conc_state_interp O with "S") as "S".
    set (perms := {[0 := (γ0, getCurPerm (`init_mem))]}).
    iAssert (threads_safe (getMaxPerm (`init_mem)) tp (fst <$> perms)) with "[Hsafe]" as "Hsafe".
    { rewrite /threads_safe /=.
      iSplit; last done.
      iExists γ0; iSplit; first done.
      unshelve iExists _; first done; simpl.
      iApply (jsafe_jsafe_perm with "Hsafe").
    }
    assert (locks_coherent tp (`init_mem) ∅) as Hlocks by done.
    forget (proj1_sig init_mem) as m.
    forget (@nil Events.machine_event) as tr.
    assert (forall i (cnti : containsThread tp i), (snd <$> perms) !! i = Some (getThreadR cnti).1)
      as Hperms.
    { intros [|]; done. }
    clearbody perms tp.
    set (ls := ∅) in Hlocks |- *.
(*     iAssert (lock_set ls) with "locks" as "locks". *)
    clearbody ls.
    clear dependent b x q.
    iLöb as "IH" forall (sch tr tp m perms n ls Htp_wf Hinvariant Hcompat Hlocks Hperms).
    destruct n as [|n].
    { iPureIntro. constructor. }
    destruct sch as [|i sch].
    { iApply step_fupdN_intro; first done; iPureIntro. constructor; done. }
    simpl; destruct (lt_dec i (pos.n (OrdinalPool.num_threads tp))).
    2: {
      iApply step_fupd_intro; first done; iNext.
      iAssert (|={⊤}[∅]▷=>^n ∀ U'', ⌜HybridMachineSig.HybridCoarseMachine.csafe (U'', tr, tp) m n⌝) with "[-]" as "H".
      { rewrite step_fupdN_plain_forall //.
        iIntros.
        iApply ("IH" with "[%] [%] [%] [%] [%] locks S Hsafe"); done.
      }
      iApply (step_fupdN_mono with "H"); iPureIntro.
      intros Hsafe.
      eapply HybridMachineSig.HybridCoarseMachine.AngelSafe
           with (tr := []); simpl; rewrite seq.cats0; last apply Hsafe.
      eapply HybridMachineSig.schedfail; eauto.
      rewrite /containsThread /= /OrdinalPool.containsThread.
      intros ?.
      pose proof (@ssrnat.leP (S i) (pos.n (OrdinalPool.num_threads tp))) as Hle; inv Hle;
           [lia | congruence].
    }
    rewrite {2}/threads_safe.
    iPoseProof (big_sepL_lookup_acc_impl with "[$Hsafe]") as "Hsafe".
    apply lookup_seq; eauto.
    iDestruct "Hsafe" as "((% & %Hgi & % & Hsafei) & Hsafe)".
    destruct (getThreadC cnti) eqn: Hi.
    - (* Krun *)
      destruct (cl_halted s) eqn: Hhalt; [|destruct (cl_at_external s) eqn: Hat_ext].
      + (* halted *)
        assert (HybridMachineSig.halted_thread cnti Int.zero) as Hhalt'.
        { econstructor; eauto. hnf; rewrite Hhalt //. }
        iApply step_fupd_intro; first done; iNext.
        iAssert (threads_safe (getMaxPerm m) tp (fst <$> perms))
          with "[Hsafei Hsafe]" as "Hsafe".
        { iApply "Hsafe".
          * iIntros "!>" (????) "H"; iApply "H".
          * iFrame "%"; iExists cnti; rewrite Hi //. }
        iAssert (|={⊤}[∅]▷=>^n ∀ U'', ⌜HybridMachineSig.HybridCoarseMachine.csafe (U'', tr, tp) m n⌝) with "[-]" as "H".
        { rewrite step_fupdN_plain_forall //.
          iIntros; iApply ("IH" with "[%] [%] [%] [%] [%] locks S Hsafe"); done.
        }
        iApply (step_fupdN_mono with "H"); iPureIntro.
        intros Hsafe.
        eapply HybridMachineSig.HybridCoarseMachine.AngelSafe with (tr := []); simpl; rewrite seq.cats0; last apply Hsafe.
        eapply HybridMachineSig.halted_step; eauto.
      + (* HybridMachineSig.suspend_step *)
        assert (HybridMachineSig.suspend_thread m cnti (updThreadC cnti (Kblocked s))) as Hsuspend.
        { eapply (HybridMachineSig.SuspendThread _ _ _ _ _ _ _ _ Hcompat); done. }
        iApply step_fupd_intro; first done; iNext.
        iAssert (|={⊤}[∅]▷=>^n ∀ U'', ⌜HybridMachineSig.HybridCoarseMachine.csafe (U'', tr, (updThreadC cnti (Kblocked s))) m n⌝) with "[-]" as "H".
        { rewrite step_fupdN_plain_forall //.
          iIntros.
          iApply ("IH" with "[%] [%] [%] [%] [%] locks S [Hsafe Hsafei]"); try done.
          + intros j cntj.
            destruct (eq_dec j i).
            * subst; rewrite gssThreadCC Hat_ext //.
            * pose proof (cntUpdateC' _ cnti cntj) as cntj0.
              rewrite -gsoThreadCC //; apply Htp_wf.
          + by apply ThreadPoolWF.updThreadC_invariant.
          + by apply StepLemmas.updThreadC_compatible.
          + (* intros ?; rewrite gsoThreadCLPool; apply Hlocks.
          + *)
            iApply "Hsafe".
            * iIntros "!>" (?? (-> & ?)%lookup_seq ?) "(% & $ & % & Hsafe)".
              iExists (cntUpdateC _ _ _); rewrite -gsoThreadCC // gThreadCR //.
            * iFrame "%"; iExists (cntUpdateC _ _ _); rewrite gssThreadCC gThreadCR.
              by iApply "Hsafei".
        }
        iApply (step_fupdN_mono with "H"); iPureIntro; intros Hsafe.
        eapply HybridMachineSig.HybridCoarseMachine.AngelSafe with (tr := []); simpl; rewrite seq.cats0; last apply Hsafe.
        eapply HybridMachineSig.suspend_step; eauto.
      + (* corestep: HybridMachineSig.thread_step *)
        pose proof (Hperms _ cnti) as Hpermi.
        rewrite !lookup_fmap in Hgi Hpermi.
        destruct (perms !! (0 + i)) as [(?, p)|] eqn: Hpi; inv Hgi; inv Hpermi.
        iDestruct (conc_state_interp_lookup with "S") as "(% & S & H)"; first done.
        rewrite jsafe_perm_unfold /jsafe_perm_pre.
        iMod ("Hsafei" with "[%] S") as "[Hhalt | [Hstep | Hext]]".
        { split; [apply mem_equiv.getCur_restr | apply restr_Max_eq]. }
        { iDestruct "Hhalt" as %(? & Hhalt' & ?); done. }
        2: { iDestruct "Hext" as (??? (Hext & ?)) "?". simpl in Hext; congruence. }
        (* HStep *)
        iMod "Hstep" as (?? Hstep) "(S & Hsafei)".
        assert (corestep (cl_core_sem ge) s (restrPermMap (ssrfun.pair_of_and (Hcompat i cnti)).1) c' m') as Hstep'.
        { by erewrite restrPermMap_irr. }
        iApply step_fupd_intro; first done; iNext.
        apply (ev_step_ax2 (Clight_evsem.CLC_evsem ge)) in Hstep' as (? & Hstep').
        iSpecialize ("IH" $! _ _ (updThread cnti (Krun c') (getCurPerm m', (getThreadR cnti).2)) _ (<[i := (g, getCurPerm m')]> perms) with "[%] [%] [%] [%] [%] locks [S H] [Hsafe Hsafei]").
        * intros j cntj.
          destruct (eq_dec j i); first by subst; rewrite gssThreadCode.
          pose proof (cntUpdate' _ _ cnti cntj).
          rewrite gsoThreadCode //; apply Htp_wf.
        * eapply (CoreLanguageDry.corestep_invariant(Sem := Sem)); try done.
          by eapply ev_step_ax1.
        * by eapply (CoreLanguageDry.corestep_compatible(Sem := Sem)).
        * intros ?; rewrite gsoThreadLPool. (*eapply Hlocks. need to know that coresteps don't mess with locks *) admit.
        * intros j cntj. setoid_rewrite fmap_insert.
          pose proof (OrdinalPool.cntUpdate' cntj) as cntj'.
          destruct (decide (i = j)).
          { subst; rewrite lookup_insert OrdinalPool.gssThreadRes //. }
          { rewrite lookup_insert_ne // OrdinalPool.gsoThreadRes //; apply Hperms. }
        * rewrite /conc_state_interp /thread_state_interp.
          simpl in *.
          iDestruct "S" as "(? & ?)".
          iFrame.
          rewrite /conc_mem_auth.
          iApply "H"; auto.
          
          admit. (* need to build an updated conc_state_interp *)
        * iApply "Hsafe".
          -- iIntros "!>" (?? (-> & ?)%lookup_seq ?) "(% & % & % & Hsafe)".
             iExists (cntUpdate _ _ cnti cnti0).
             rewrite gsoThreadCode // gsoThreadRes //.
             admit. (* need to know that any changes to getMaxPerm don't invalidate other threads! *)
          -- iExists (cntUpdate _ _ cnti cnti).
             rewrite gssThreadCode gssThreadRes.
             simpl in *.
             iApply jsafe_perm_mono; eauto.
             (* Need to know permMapLt (getMaxPerm m') (getMaxPerm m) *)
             simpl in Hlt0.
             apply Clight_evsem.CLC_evstep_ax1 in Hstep'.
             rewrite /= in Hstep'.
             Search decay.
             admit.
        * (* Work from here *)
          iApply (step_fupdN_mono with "[IH]").
          iIntros "_".
          iPureIntro;
          eapply HybridMachineSig.HybridCoarseMachine.CoreSafe.
          rewrite /HybridMachineSig.MachStep /=.
          change (i :: sch) with (HybridMachineSig.yield (i :: sch)) at 2.
          change m' with (HybridMachineSig.diluteMem m') at 3.
          eapply HybridMachineSig.thread_step; first done.
          eapply step_dry.
          simpl. repeat try done. done. done.
          simpl in *. eauto. done. simpl in *.

          (*
          
          iPureIntro; intros Hsafe.
          eapply HybridMachineSig.HybridCoarseMachine.CoreSafe, Hsafe.
          rewrite /HybridMachineSig.MachStep /=.
          change (i :: sch) with (HybridMachineSig.yield (i :: sch)) at 2.
          change m' with (HybridMachineSig.diluteMem m') at 3.
          eapply HybridMachineSig.thread_step; first done.
          by eapply step_dry. *) admit. admit. *)
    - admit. (* Kblocked: HybridMachineSig.sync_step *)
     (* pose proof (Htp_wf _ cnti) as Hwfi; rewrite Hi in Hwfi.
      rewrite jsafe_perm_unfold /jsafe_perm_pre.
      iDestruct "S" as (? Hmax) "S".
      assert (permMapLt (getThreadR cnti).1 (getMaxPerm (restrPermMap Hmax))) as Hlt0.
      { rewrite restr_Max_eq. by apply compat_th. }
      iMod ("Hsafei" $! _ Hlt0 with "[%] S") as "[Hhalt | [Hstep | Hext]]".
      { rewrite restr_Max_eq //. }
      { iDestruct "Hhalt" as %(? & Hhalt' & ?).
        destruct s; done. }
      { iMod "Hstep" as (?? Hstep) "?".
        apply cl_corestep_not_at_external in Hstep; done. }
      iDestruct "Hext" as (??? (Hat_ext & Hpre)) "Hpost".
      iAssert (|={⊤}[∅]▷=> ∃ (tp' : t(ThreadPool := OrdinalPool.OrdinalThreadPool)) m' ev, ⌜threads_wellformed tp' ∧ invariant tp' ∧ mem_compatible tp' m' ∧
        locks_coherent tp' m' ls ∧ syncStep true cnti Hcompat tp' m' ev⌝ ∧
        threads_safe (getMaxPerm m') tp' ∗ (∃ p (Hlt : permMapLt p (getMaxPerm m')), state_interp (restrPermMap Hlt) tt) ∗ lock_set ls) with "[-]" as "Hsafe".
      2: { iMod "Hsafe"; iIntros "!> !>"; iMod "Hsafe" as (??? (? & ? & ? & ? & ?)) "(Hsafe & S & locks)".
           iAssert (|={⊤}[∅]▷=>^n ∀ U'', ⌜HybridMachineSig.HybridCoarseMachine.csafe (U'', tr ++ [Events.external i ev], tp') m' n⌝) with "[-]" as "H".
           { rewrite step_fupdN_plain_forall //.
             iIntros; iApply ("IH" with "[%] [%] [%] [%] Hsafe locks S"); done. }
           iApply (step_fupdN_mono with "H"); iPureIntro.
           intros Hsafe.
           eapply HybridMachineSig.HybridCoarseMachine.AngelSafe; simpl; last apply Hsafe.
           eapply HybridMachineSig.sync_step; eauto. }
      (* consider each of the concurrency functions *)
      clear Hwfi.
      destruct s as [|f ? k|]; try done; simpl in Hat_ext.
      destruct f as [|ext argsty retty cc]; try done.
      destruct (ef_inline ext); inv Hat_ext.
      destruct (CEspec_cases _ x) as [-> | [-> | [-> | [-> | ->]]]].
      + (* acquire *)
        iApply (acquire_safe with "Hsafe Hpost locks").
      + (* release *)
      + (* makelock *)
      + (* freelock *)
      + (* spawn *) *)
    - (* Kresume: HybridMachineSig.resume_step *)
      (* pose proof (Htp_wf _ cnti) as Hwfi; rewrite Hi in Hwfi; destruct Hwfi as (? & ->).
      destruct s; try done.
      destruct f; try done.
      assert (HybridMachineSig.resume_thread m cnti (updThreadC cnti (Krun (Returnstate Vundef c)))) as Hresume.
      { unfold cl_at_external in *; destruct (ef_inline e) eqn: Hinline; try done.
        eapply (HybridMachineSig.ResumeThread _ _ _ _ _ _ _ _ _ Hcompat); try done; simpl; by rewrite ?Hinline. }
      iApply step_fupd_intro; first done; iNext.
      iSpecialize ("IH" $! _ _ (updThreadC cnti (Krun (Returnstate Vundef c))) with "[%] [%] [%] [Hsafei Hsafe] S").
      + intros j cntj.
        destruct (eq_dec j i).
        * subst; rewrite gssThreadCC //.
        * pose proof (cntUpdateC' _ cnti cntj) as cntj0.
          rewrite -gsoThreadCC //; apply Htp_wf.
      + by apply ThreadPoolWF.updThreadC_invariant.
      + by apply StepLemmas.updThreadC_compatible.
      + iApply "Hsafe".
        * iIntros "!>" (?? (-> & ?)%lookup_seq ?) "(% & Hsafe)".
          iExists (cntUpdateC _ _ _); rewrite -gsoThreadCC // gThreadCR //.
        * iExists (cntUpdateC _ _ _); rewrite gssThreadCC gThreadCR.
          by iApply "Hsafei".
      + iApply (step_fupdN_mono with "IH"); iPureIntro; intros Hsafe.
        eapply HybridMachineSig.HybridCoarseMachine.CoreSafe with (tr := []); simpl; rewrite seq.cats0; last apply Hsafe.
        change (i :: sch) with (HybridMachineSig.yield (i :: sch)) at 2.
        eapply HybridMachineSig.resume_step; eauto. *) admit.
    - (* Kinit: HybridMachineSig.start_step *)
      iDestruct "Hsafei" as (? Hinit) "Hsafei".
      set (m' := restrPermMap (ssrfun.pair_of_and (Hcompat i cnti)).1).
      set (tp' := updThread cnti (Krun q_new) (HybridMachineSig.add_block Hcompat cnti m')).
      assert (HybridMachineSig.start_thread m cnti tp' m').
      { econstructor; done. }
      iApply step_fupd_intro; first done; iNext.
      iSpecialize ("IH" $! _ _ tp' m' with "[%] [%] [%] [Hsafei Hsafe] [S]").
      + intros j cntj.
        destruct (eq_dec j i).
        * subst; rewrite gssThreadCode //.
        * pose proof (cntUpdate' _ _ cnti cntj).
          rewrite gsoThreadCode //; apply Htp_wf.
      + by eapply (CoreLanguageDry.initial_core_invariant(Sem := Sem)).
      + eapply InternalSteps.start_compatible; try done.
      + iApply "Hsafe".
        * iIntros "!>" (?? (-> & ?)%lookup_seq ?) "(% & Hsafe)".
          iExists (cntUpdate _ _ cnti cnti0); rewrite gsoThreadCode // gsoThreadRes //.
          subst m'; rewrite restr_Max_eq //.
        * iExists (cntUpdate _ _ cnti cnti); rewrite gssThreadCode gssThreadRes.
          rewrite restr_Max_eq /=.
          iApply (jsafe_perm_equiv with "Hsafei").
          symmetry; apply mem_equiv.getCur_restr.
      + iDestruct "S" as (??) "S".
        iExists _, (mem_equiv.useful_permMapLt_trans _ Hlt).
        rewrite restrPermMap_idem. erewrite restrPermMap_irr; done.
      + iApply (step_fupdN_mono with "IH"); iPureIntro; intros Hsafe.
        eapply HybridMachineSig.HybridCoarseMachine.CoreSafe with (tr := []); simpl; rewrite seq.cats0; last apply Hsafe.
        change (i :: sch) with (HybridMachineSig.yield (i :: sch)) at 2.
        change m' with (HybridMachineSig.diluteMem m').
        eapply HybridMachineSig.start_step; eauto.
  Admitted.

End Safety.
