(* Instead of deriving a juicy-machine execution from the CSL proof, we derive a dry-machine execution
   directly, along the lines of the sequential adequacy proof (veric/SequentialClight). *)
Require Import Coq.Strings.String.

From Coq Require Import FunctionalExtensionality.

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
(* Require Import VST.concurrency.juicy.memLt. (* added memLt *) *)
Require Import iris_ora.algebra.gmap.


Import ThreadPool.

Set Bullet Behavior "Strict Subproofs".

Definition access_equiv (m: mem) k (r : prodO dfracO (optionO (leibnizO resource))) :=
  (access_at m k Cur) = (perm_of_res r).

Definition access_map_rmap (m: mem) σ : Prop :=
  forall loc, access_equiv m loc (σ @ loc).

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

(*Definition add_fresh_block (b : Values.block) (cur : access_map) : access_map :=
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
  | _, _ => True
  end.

Inductive SelfOp :=
| SO_id                                 (* no-op / pure store *)
| SO_alloc (b : Values.block) (lo hi : Z)   (* malloc: fresh block b = nextblock m *)
| SO_free  (b : Values.block) (lo hi : Z).  (* free: drop [lo,hi) on block b *)


(* Override one access_map on [lo,hi) in block b *)
Definition override_range
  (p : option permission) (b : Values.block) (lo hi : Z) (pmap : access_map)
  : access_map :=
  Maps.PMap.set b
    (fun ofs =>
       if zle lo ofs && zlt ofs hi then p else Maps.PMap.get b pmap ofs)
    pmap.

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

Lemma contents_eq_or_max_writable p m
  (Hlt : permMapLt p (getMaxPerm m))
  (m' : Mem.mem)
  (unchanged_on_contents :
    forall b ofs,
      ~ Mem.perm (restrPermMap Hlt) b ofs Max Writable ->
      Mem.perm (restrPermMap Hlt) b ofs Cur Readable ->
      contents_at m' (b,ofs) = contents_at (restrPermMap Hlt) (b,ofs))
  :
  forall b ofs,
    contents_at m' (b,ofs) = contents_at (restrPermMap Hlt) (b,ofs)
    \/ Mem.perm (restrPermMap Hlt) b ofs Max Writable \/
    ~ Mem.perm (restrPermMap Hlt) b ofs Cur Readable.
Proof.
  intros b ofs.
  Require Import Classical_Prop.
  destruct (classic (Mem.perm (restrPermMap Hlt) b ofs Max Writable)) as [Hw|Hnw].
  - right. left. done.
  - destruct (classic (Mem.perm (restrPermMap Hlt) b ofs Cur Readable)) as [HcurR | HncurR].
    + left; eapply unchanged_on_contents; eauto.
    + right. right. done.
Qed.

Lemma max_writable_implies_can_store_at
  (m: Mem.mem) (b: Values.block) (ofs: Z) :
  Mem.perm m b ofs Max Writable ->
  can_store_at (getMaxPerm m) (b,ofs).
Proof.
  rewrite /can_store_at /Mem.perm /Mem.perm_order' /getMaxPerm/=.
  intros.
  rewrite PMap.gmap. done.
Qed.

Lemma contents_eq_or_can_store_at p m
  (Hlt : permMapLt p (getMaxPerm m))
  (m' : Mem.mem)
  (unchanged_on_contents :
    forall b ofs,
      ~ Mem.perm (restrPermMap Hlt) b ofs Max Writable ->
      Mem.perm (restrPermMap Hlt) b ofs Cur Readable ->
      contents_at m' (b,ofs) = contents_at (restrPermMap Hlt) (b,ofs))
  :
  forall loc,
    contents_at m' loc = contents_at (restrPermMap Hlt) loc
    \/ can_store_at (getMaxPerm (restrPermMap Hlt)) loc \/
     ~Mem.perm (restrPermMap Hlt) (fst loc) (snd loc) Cur Readable.
Proof.
  intros [b ofs].
  destruct (contents_eq_or_max_writable p m Hlt m' unchanged_on_contents b ofs) as [Heq|Hw].
  - left; exact Heq.
  - destruct Hw.
    + right. left.
      eapply max_writable_implies_can_store_at; auto.
    + right. right. done.
Qed.

Lemma storebytes_nil_contents
  (m m' : Mem.mem) b ofs
  (Hsb : Mem.storebytes m b ofs [] = Some m') :
  mem_equiv.content_equiv m' m.
Proof.
  Transparent Mem.storebytes.
  rewrite /Mem.storebytes /= in Hsb.
  destruct (Mem.range_perm_dec m b ofs (ofs + 0%nat) Cur Writable); last first; try done.
  inv Hsb.
  rewrite /mem_equiv.content_equiv.
  intros.
  simpl.
  destruct (peq b0 b) as [->|Hneq].
  - by rewrite PMap.gss.
  - rewrite PMap.gso //=.
Qed.

Lemma content_equiv_contents_at (m1 m2 : mem) (H : mem_equiv.content_equiv m1 m2) :
  forall loc, contents_at m1 loc = contents_at m2 loc.
Proof.
  intros [b ofs].
  by unfold contents_at.
Qed.

Lemma conc_mem_auth_lookup `{!conc_VSTGS OK_ty Σ} i g p m perms :
  perms !! i = Some (g, p) →
  conc_mem_auth m perms ⊢ (∃ Hp : permMapLt p (getMaxPerm m),
      thread_mem_auth g (restrPermMap Hp)) ∗
        (∀ m', ⌜OpSC i m m' p perms⌝ ∧
                 thread_mem_auth g m' -∗
              conc_mem_auth m' (<[i:=(g, getCurPerm m')]>perms)).
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
    setoid_rewrite (big_sepM2_delete_l _ _ _ i (g, p)) at 2; auto.
    iDestruct (resource_map.resource_map_auth_valid with "H") as %(_ & Hvalid).
    iExists (<[i := σ']>σs).
    + iExists σ'.
      iSplit; first rewrite lookup_insert //.
      iSplitR "Hbig".
      iFrame. iPureIntro.
      split; auto.
      unshelve eexists; first by rewrite Hmax_eq.
      subst; rewrite restrPermMap_eq //.
       rewrite ! delete_insert_delete.
       iApply (big_sepM2_mono with "Hbig"); intros.
       apply lookup_delete_Some in H4.
       destruct y1.
       do 2 f_equiv.
       rewrite /impl /coherent.
       intros (Hlt1 & ?).
       unshelve eexists; first by rewrite Hmax_eq.
       simpl; split; auto.
       * intros; apply H5; auto.
         rewrite -Hnxt_eq //.
       * destruct (H5 loc) as (_ & Hcoh).
         destruct (Hloc loc) as [Hmem_eq | Hwrite].
         ** rewrite /contents_at in Hmem_eq.
            rewrite /coherent_loc /contents_cohere /resource_at /juicy_mem.contents_at in Hcoh |- *.
            split.
            intros.
            rewrite - Hmem_eq.
            apply H5; auto.
            rewrite /access_cohere !access_at_restrPermMap_Cur in Hcoh |- *.
            apply Hcoh.
         ** unfold coherent_loc in Hcoh |- *.
            specialize (Hvalid loc).
            unfold contents_cohere, access_cohere in *; simpl in *.
            rewrite !access_at_restrPermMap_Cur in Hcoh |- *.
            split; try apply Hcoh.
            apply lookup_delete_Some in H3.
            intros ? Hres.
            destruct Hcoh as (Hv & _); specialize (Hv _ Hres).
            rewrite !restrPermMap_contents in Hv |- *.
            rewrite /resource_at /resR_to_resource in Hres.
            rewrite /permMapsDisjoint_at in sc_perm_disjoint0.
            specialize (sc_perm_disjoint0 k i).
            destruct H3 as (Hneq & Hperm).
            rewrite H Hperm in sc_perm_disjoint0.
            specialize (sc_perm_disjoint0 Hneq).
            simpl in sc_perm_disjoint0.
            rewrite /permMapsDisjoint /= in sc_perm_disjoint0.
            destruct (y2 !! loc) eqn: E; rewrite E // in Hres.
            destruct s; inv Hres.
            rewrite /resource_at in H5.
            specialize (H5 loc).
            destruct H5 as (_ & _ & HpermHlt1).
            rewrite E in HpermHlt1.
            apply writable_at_perm_order_cases
                  with (x := access_at (restrPermMap Hlt) loc Cur) in Hwrite; last by rewrite access_at_restrPermMap_Cur.
            rewrite /access_at in Hwrite.
            rewrite restrPermMap_Cur_eq in Hwrite.
            assert (Hread: Mem.perm_order' (a # (loc.1) loc.2) Readable).
            { rewrite mem_lemmas.po_oo.
              eapply readable_dfrac_perm_order with (Hlt:= Hlt1) (rsh := rsh) ; try eauto.
              setoid_rewrite <- H6; auto. }
            assert (Hwrite1: Mem.perm_order' ((getCurPerm m') # (loc.1) loc.2) Writable).
            { destruct Hwrite as [Hwrite | Hwrite];
                rewrite mem_lemmas.po_oo; rewrite Hwrite;
                [try apply perm_F_any | apply perm_refl].
            }
            assert (¬ ∃ pu : option permission,
                            perm_union (a # (loc.1) loc.2) ((getCurPerm m') # (loc.1) loc.2) = Some pu).
            { apply (perm_order_clash (a # (loc.1) loc.2) ((getCurPerm m') # (loc.1) loc.2)); done. }
            specialize (sc_perm_disjoint0 loc.1 loc.2); easy.
          + rewrite lookup_insert -Hcur_eq; auto.
  - (* getCurPerm m' = add_fresh_block b p
                  ∧ getMaxPerm m' = add_fresh_block b (getMaxPerm m)
                    ∧ Mem.nextblock m' = Pos.succ (Mem.nextblock m) *)
    setoid_rewrite (big_sepM2_delete_l _ _ _ i (g, getCurPerm m')) at 2; auto.
    iDestruct (resource_map.resource_map_auth_valid with "H") as %(_ & Hvalid).
    destruct sc_self_eqs as (Hblk & Hcur_max_eq & Hnxt_eq & Hcnt_eq).
    iExists (<[i := σ']>σs).
    + iExists σ'.
      iSplit; first rewrite lookup_insert //.
      iSplitR "Hbig".
      iFrame. iPureIntro.
      split; auto.
      exists (cur_lt_max _).
      rewrite restrPermMap_eq //.
      rewrite ! delete_insert_delete.
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
      have Hlt' : permMapLt a (getMaxPerm m').
      { eapply sc_others_still_lt2; eauto. }
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
           rewrite Hcnt_eq PMap.gso; auto.
        ** rewrite /access_cohere.
           rewrite access_at_restrPermMap_Cur.
           rewrite /coherent in Hchr.
           specialize (Hchr loc).
           destruct Hchr as (? & ?).
           rewrite /coherent_loc in H5.
           destruct H5 as (? & ?).
           rewrite /access_cohere in H6.
           rewrite access_at_restrPermMap_Cur in H6. auto.
      + rewrite lookup_insert; auto.
    - setoid_rewrite (big_sepM2_delete_l _ _ _ i (g, getCurPerm m')) at 2; auto.
      destruct sc_self_eqs as (Hblk & Hcur_max_eq & Hnxt_eq & Hcnt_eq).
      iDestruct (resource_map.resource_map_auth_valid with "H") as %(_ & Hvalid).
      iExists (<[i := σ']>σs).
      + iExists σ'.
        iSplit; first rewrite lookup_insert //.
        iSplitR "Hbig".
        iFrame. iPureIntro.
        split; auto.
        exists (cur_lt_max _).
        rewrite restrPermMap_eq //.
        rewrite ! delete_insert_delete.
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
        assert (Hlt': permMapLt a (getMaxPerm m')).
        {
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
             rewrite Hcnt_eq //.
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
Qed.

Lemma can_store_at_getCurPerm_of_perm_order'
  (m : Mem.mem) (b : Values.block) (ofs : Z) :
  Mem.perm_order' ((Mem.mem_access m) # b ofs Cur) Writable ->
  can_store_at (getCurPerm m) (b,ofs).
Proof.
  rewrite /Mem.perm_order' /can_store_at /getCurPerm /=.
  intros H.
  rewrite PMap.gmap.
  destruct ((Mem.mem_access m) # b ofs Cur); try done.
Qed.
  
Lemma storebytes_contents_or_canstore_cur
  p m (Hlt : permMapLt p (getMaxPerm m))
  (m' : Mem.mem) b ofs bytes
  (Hst1 : Mem.storebytes (restrPermMap Hlt) b ofs bytes = Some m')
  (Hf : forall ofs0 : Z, (ofs <= ofs0 < ofs + Z.of_nat (length bytes))%Z ->
      Mem.perm_order' ((Mem.mem_access (restrPermMap Hlt)) # b ofs0 Cur) Writable):
  forall loc, contents_at m' loc = contents_at (restrPermMap Hlt) loc
         \/ can_store_at (getCurPerm (restrPermMap Hlt)) loc.
Proof.
  intros [b0 ofs0].
  Transparent Mem.storebytes.
  rewrite /Mem.storebytes in Hst1.
  destruct (Mem.range_perm_dec (restrPermMap Hlt) b ofs
              (ofs + Z.of_nat (length bytes)) Cur Writable) as [Hrp | Hnrp]; try discriminate.
  inversion Hst1; subst m'; clear Hst1.
  destruct (peq b0 b) as [-> | Hbneq].
  - destruct (classic (ofs <= ofs0 < ofs + Z.of_nat (length bytes))%Z) as [Hin | Hout].
    + right; apply can_store_at_getCurPerm_of_perm_order'; by apply Hf.
    + left; rewrite /contents_at /= PMap.gss Mem.setN_outside; auto. lia.
   - left; rewrite /contents_at PMap.gso //=.
Qed.

(*
Lemma storebytes_contents_or_canstore_cur1 m (m' : Mem.mem) b ofs bytes
  (Hst1 : Mem.storebytes m b ofs bytes = Some m')
  (Hf : forall ofs0 : Z, (ofs <= ofs0 < ofs + Z.of_nat (length bytes))%Z ->
      Mem.perm_order' ((Mem.mem_access m) # b ofs0 Cur) Writable):
  forall loc, contents_at m' loc = contents_at m loc \/ can_store_at (getCurPerm m) loc.
Proof.
  intros [b0 ofs0].
  Transparent Mem.storebytes.
  unfold Mem.storebytes in Hst1.
  destruct (Mem.range_perm_dec m b ofs (ofs + length bytes) Cur Writable)
    as [Hrp | Hnrp].
  2: discriminate.
  inversion Hst1; subst m'; clear Hst1.
  destruct (peq b0 b) as [-> | Hbneq].
  - destruct (classic (ofs <= ofs0 < ofs + Z.of_nat (length bytes))%Z) as [Hin | Hout].
    + right.
      apply can_store_at_getCurPerm_of_perm_order'.
      by apply Hf.
    + left.
      rewrite /contents_at /=.
      rewrite PMap.gss.
      rewrite Mem.setN_outside; auto.
      lia.
   - left.
     rewrite /contents_at /=.
     rewrite PMap.gso //=.
Qed.
*)

Lemma permMapLt_respects_left
  (a1 a2 amax : access_map) (Heq : mem_equiv.access_map_equiv a1 a2):
  permMapLt a1 amax -> permMapLt a2 amax.
Proof.
  rewrite /permMapLt.
  intros Hlt b ofs.
  rewrite /mem_equiv.access_map_equiv in Heq.
  specialize (Heq b).
  rewrite <- Heq. done.
Qed.

Lemma nextblock_free_list
  (m m' : mem) (l : list (Values.block * Z * Z)) :
  Mem.free_list m l = Some m' -> Mem.nextblock m' = Mem.nextblock m.
Proof.
  revert m m'.
  induction l as [| [(b & lo) hi] l IH]; intros m m' Hfl.
  - simpl in Hfl. inversion Hfl. done.
  - simpl in Hfl.
    destruct (Mem.free m b lo hi) as [m1|] eqn:Hfree; try discriminate.
    specialize (IH _ _ Hfl).
    apply Mem.nextblock_free in Hfree.
    rewrite IH. done.
Qed.

Lemma memPerm_order_permMapLt m1 m2:
  permMapLt (getCurPerm m1) (getCurPerm m2) ->
  ∀ (b : Values.block) (ofs : Z) (p : permission),
    Mem.perm_order' ((Mem.mem_access m1) # b ofs Cur) p →
    Mem.perm_order' ((Mem.mem_access m2) # b ofs Cur) p.
Proof.
  rewrite /Mem.perm_order' /getCurPerm.
  intros HpermLt b???.
  specialize (HpermLt b ofs).
  rewrite ! Maps.PMap.gmap in HpermLt.
  destruct ((Mem.mem_access m2) # b ofs Cur);
    destruct ((Mem.mem_access m1) # b ofs Cur); try contradiction.
  eapply perm_order_trans; eauto.
Qed.

Lemma memPerm_permMapLt m1 m2:
  permMapLt (getCurPerm m1) (getCurPerm m2) ->
  ∀ (b : Values.block) (ofs : Z) (p : permission),
    Mem.perm m1 b ofs Cur p → Mem.perm m2 b ofs Cur p.
Proof. eapply memPerm_order_permMapLt. Qed.

Lemma perm_order_cur m1 m2 b ofs (H : permMapLt (getCurPerm m1) (getCurPerm m2)):
  Mem.perm_order'' ((Mem.mem_access m2) # b ofs Cur) ((Mem.mem_access m1) # b ofs Cur).
Proof.
  rewrite /permMapLt /Mem.perm_order'' /getCurPerm in H |- *.
  specialize (H b ofs).
  by rewrite ! Maps.PMap.gmap in H.
Qed.

Lemma free_list_mono :
  forall l ms mb m',
    permMapLt (getCurPerm ms) (getCurPerm mb) ->
    Mem.free_list ms l = Some m' ->
    exists mb', Mem.free_list mb l = Some mb'.
Proof.
  induction l as [|[[b lo] hi] tl IH]; intros ms mb m' Hle Hfl.
  - simpl in Hfl. inversion Hfl; subst; by exists mb.
  - simpl in Hfl.
    destruct (Mem.free ms b lo hi) as [ms1|] eqn:HfreeS; try discriminate.
    assert (HexB : exists mb1, Mem.free mb b lo hi = Some mb1).
    { Transparent Mem.free.
      unfold Mem.free in *.
      destruct (Mem.range_perm_dec ms b lo hi Cur Freeable) as [Hrp|Hrp]; try discriminate.
      inv HfreeS.
      rewrite /Mem.range_perm in Hrp.
      eexists (Mem.unchecked_free mb b lo hi).
      destruct (Mem.range_perm_dec mb b lo hi Cur Freeable) as [Hrng|Hnot]; try done.
      exfalso.
      apply Hnot.
      unfold Mem.range_perm.
      intros.
      eapply memPerm_permMapLt; eauto.
    }
    destruct HexB as [mb1 HfreeB].
    assert (Hle1 : permMapLt (getCurPerm ms1) (getCurPerm mb1)).
    { rewrite /permMapLt.
      intros.
      apply Mem.free_result in HfreeS, HfreeB.
      rewrite /Mem.unchecked_free /= in HfreeB.
      pose proof (f_equal Mem.mem_access HfreeS) as HfreeS'.
      simpl in HfreeS'.
      pose proof (f_equal Mem.mem_access HfreeB) as HfreeB'.
      simpl in HfreeB'.
      rewrite /getCurPerm.
      rewrite HfreeB' HfreeS'.
      destruct (eq_block b0 b) as [->|Hneqb]; rewrite !PMap.gmap;
        [ rewrite !PMap.gss | rewrite !PMap.gso //=].
      - destruct (zle lo ofs && zlt ofs hi) eqn:Hin.
        + apply po_refl.
        + by apply perm_order_cur.
      - by apply perm_order_cur.
    }
    destruct (IH ms1 mb1 m' Hle1 Hfl) as [mb_all Htail].
    exists mb_all.
    by rewrite /= HfreeB.
Qed.

Lemma free_permMapLt_cur_max :
  forall ms mb b lo hi ms1 mb1,
    permMapLt (getCurPerm ms) (getMaxPerm mb) ->
    Mem.free ms b lo hi = Some ms1 ->
    Mem.free mb b lo hi = Some mb1 ->
    permMapLt (getCurPerm ms1) (getMaxPerm mb1).
Proof.
  rewrite /permMapLt.
  intros.
  apply Mem.free_result in H0, H1.
  pose proof (f_equal Mem.mem_access H0) as Hfr1.
  pose proof (f_equal Mem.mem_access H1) as Hfr2.
  simpl in Hfr1, Hfr2.
  rewrite /getCurPerm /getMaxPerm.
  rewrite Hfr1 Hfr2.
  destruct (eq_block b0 b) as [->|Hneqb]; rewrite !PMap.gmap;
    [ rewrite !PMap.gss | rewrite !PMap.gso //=].
  - destruct (zle lo ofs && zlt ofs hi) eqn:Hin.
    + apply po_refl.
    + rewrite /permMapLt in H.
      specialize (H b ofs).
      by rewrite /getMaxPerm /getCurPerm /= !PMap.gmap in H.
  - rewrite /permMapLt in H.
    specialize (H b0 ofs).
    by rewrite /getMaxPerm /getCurPerm /= !PMap.gmap in H.
Qed.

Lemma free_list_permMapLt_cur_max :
  forall l ms mb ms' mb',
    permMapLt (getCurPerm ms) (getMaxPerm mb) ->
    Mem.free_list ms l = Some ms' ->
    Mem.free_list mb l = Some mb' ->
    permMapLt (getCurPerm ms') (getMaxPerm mb').
Proof.
  induction l as [|[[b lo] hi] tl IH]; intros ms mb ms' mb' Hle Hs Hb.
  - simpl in Hs, Hb. inversion Hs; by inv Hb.
  - simpl in Hs, Hb.
    destruct (Mem.free ms b lo hi) as [ms1|] eqn:HfreeS; try discriminate.
    destruct (Mem.free mb b lo hi) as [mb1|] eqn:HfreeB; try discriminate.
    have Hle1: permMapLt (getCurPerm ms1) (getMaxPerm mb1) by eapply free_permMapLt_cur_max.
    by eapply IH.
Qed.

Lemma free_contents : forall m b lo hi m', Mem.free m b lo hi = Some m' ->
    Mem.mem_contents m' = Mem.mem_contents m.
Proof.
  intros m b lo hi m' H.
  unfold Mem.free in H.
  destruct (Mem.range_perm_dec m b lo hi Cur Freeable);
    inversion H; subst; simpl; reflexivity.
Qed.

Lemma free_list_contents :
  forall m l m',
    Mem.free_list m l = Some m' ->
    Mem.mem_contents m' = Mem.mem_contents m.
Proof.
  intros m l.
  revert m.
  induction l as [| [[b lo] hi] tl IH]; intros.
  - simpl in H. inversion H; subst. reflexivity.
  - simpl in H.
    destruct (Mem.free m b lo hi) as [m1|] eqn:Hfree; try discriminate.
    specialize (IH m1 m').
    apply IH in H.
    apply free_contents in Hfree.
    by rewrite <- Hfree.
Qed.

Lemma mem_contents_restrPermMap {p m}
  (Hlt : permMapLt p (getMaxPerm m)) :
  Mem.mem_contents (restrPermMap Hlt) = Mem.mem_contents m.
Proof. reflexivity. Qed.

Lemma restrPermMap_Max : forall (p' : access_map) (m : mem)
         (Hlt : permMapLt p' (getMaxPerm m)) (b : positive) (ofs : Z),
    (Mem.mem_access (restrPermMap Hlt)) # b ofs Max = (Mem.mem_access m) # b ofs Max.
Proof.
  intros p' m Hlt b ofs.
  unfold restrPermMap; simpl.
  unfold Maps.PMap.get; simpl.
  rewrite PTree.gmap.
  rewrite /option_map.
  destruct ((Mem.mem_access m).2 !! b)%maps; simpl; try done.
Qed.

Lemma alloc_mem_contents_pointwise:
  forall m m' b lo hi,
    Mem.alloc m lo hi = (m', b) ->
    forall b' ofs,
      ZMap.get ofs (Mem.mem_contents m') # b' =
        (if peq b' b
         then ZMap.get ofs (ZMap.init Undef)
         else ZMap.get ofs (Mem.mem_contents m) # b').
Proof.
  intros m m' b lo hi Halloc b' ofs.
  Transparent Mem.alloc.
  unfold Mem.alloc in Halloc.
  (* destruct the pair returned by alloc *)
  destruct (Mem.alloc m lo hi) as [m'' b''] eqn:Hall; inv Halloc.
  simpl.
  destruct (peq b' (Mem.nextblock m)); subst.
  - by rewrite PMap.gss.
  - by rewrite PMap.gso.
Qed.


Lemma free_list_contents_mem_equiv :
  forall m l m',
    Mem.free_list m l = Some m' ->
    mem_equiv.content_equiv m' m.
Proof.
  intros m l.
  revert m.
  induction l as [| [[b lo] hi] tl IH]; intros.
  - simpl in H. inversion H; subst. reflexivity.
  - simpl in H.
    destruct (Mem.free m b lo hi) as [m1|] eqn:Hfree; try discriminate.
    specialize (IH m1 m').
    apply IH in H.
    apply free_contents in Hfree.
    rewrite /mem_equiv.content_equiv in H |- *.
    rewrite <- Hfree.
    intros.
    by specialize (H b0 ofs).
Qed.

Lemma valid_block_free_list_1 :
  forall m l m' b,
    Mem.free_list m l = Some m' ->
    Mem.valid_block m b ->
    Mem.valid_block m' b.
Proof.
  intros m l.
  revert m.
  induction l as [| [(b0 & lo) hi] tl IH]; simpl; intros m m' b Hfree Hvb.
  - inversion Hfree; subst; assumption.
  - destruct (Mem.free m b0 lo hi) eqn:Hfree1; try discriminate.
    eapply IH; eauto.
    eapply Mem.valid_block_free_1; eauto.
Qed.

Definition sc_others_lt_and_disjoint
  (perms : gmap nat (gname * access_map))
  (i : nat) (m m' : mem) : Prop :=
  (* All other threads remain strictly below the NEW Max. *)
  (∀ j g' p', j ≠ i → perms !! j = Some (g', p') → permMapLt p' (getMaxPerm m')) ∧
  (* each thread's permissions are less than max *)
  (∀ j g p, i <> j -> perms !! j = Some (g,p) → permMapLt p (getMaxPerm m)) /\
  (* permMapsDisjoint in invariant *)
  (∀ j, j ≠ i → permMapsDisjoint_at perms i j).

Lemma free_preserve_disjoint_and_lt :
  forall (m m1 : mem) (b : positive) (lo hi : Z) (a : access_map),
    permMapLt a (getMaxPerm m) ->
    permMapsDisjoint (getCurPerm m) a ->
    Mem.free m b lo hi = Some m1 ->
    permMapsDisjoint (getCurPerm m1) a /\ permMapLt a (getMaxPerm m1).
Proof.
  intros m m1 b lo hi a Hlt Hdis Hfree.
  Transparent Mem.free.
  unfold Mem.free in Hfree.
  destruct (Mem.range_perm_dec m b lo hi Cur Freeable); try discriminate.
  inv Hfree.
  split.
  - unfold permMapsDisjoint in *.
    intros.
    destruct (Pos.eq_dec b0 b) as [->|Hbneq].
    + rewrite /getCurPerm PMap.gmap PMap.gss /=.
      destruct (zle lo ofs) as [Hle|Hnle];
        destruct (zlt ofs hi) as [Hltz|Hnlt]; simpl.
      * by eexists.
      * specialize (Hdis b ofs) as [pu Hpu].
        rewrite /getCurPerm PMap.gmap in Hpu.
        by eexists.
      * specialize (Hdis b ofs) as [pu Hpu].
        rewrite /getCurPerm PMap.gmap in Hpu.
        by eexists.
      * specialize (Hdis b ofs) as [pu Hpu].
        rewrite /getCurPerm PMap.gmap in Hpu.
        by eexists.
    + specialize (Hdis b0 ofs) as [pu Hpu].
      rewrite /getCurPerm PMap.gmap in Hpu.
      exists pu.
      rewrite /getCurPerm !PMap.gmap PMap.gso //.
  - unfold permMapLt in *.
    intros.
    destruct (Pos.eq_dec b0 b) as [->|Hbneq].
    + specialize (Hlt b ofs).
      rewrite /getMaxPerm PMap.gmap PMap.gss.
      destruct (zle lo ofs) as [Hle|Hnle];
        destruct (zlt ofs hi) as [Hltz|Hnlt]; simpl.
      * destruct (a # b ofs) eqn:Ha; try done.
        rewrite /permMapsDisjoint in Hdis.
        destruct (Hdis b ofs) as [pu Hpu].
        have Hperm : Mem.perm m b ofs Cur Freeable.
        { apply r. lia. }
        rewrite /Mem.perm in Hperm.
        rewrite /getCurPerm PMap.gmap in Hpu.
        destruct ((Mem.mem_access m) # b ofs Cur) as [p1|] eqn:Hacc; try done.
        rewrite Ha in Hpu.
        rewrite /perm_union /= in Hpu;
          destruct p1; try discriminate; inv Hperm.
      * by rewrite /getCurPerm PMap.gmap in Hlt.
      * by rewrite /getCurPerm PMap.gmap in Hlt.
      * by rewrite /getCurPerm PMap.gmap in Hlt.
   + rewrite /getMaxPerm !PMap.gmap PMap.gso //.
     specialize (Hlt b0 ofs).
     by rewrite /getCurPerm PMap.gmap in Hlt.
Qed.

Lemma free_list_preserve_disjoint_and_lt :
  forall m l m' a,
    permMapLt a (getMaxPerm m) ->
    permMapsDisjoint (getCurPerm m) a ->
    Mem.free_list m l = Some m' ->
    permMapsDisjoint (getCurPerm m') a /\
      permMapLt a (getMaxPerm m').
Proof.
  intros m l m' a Hlt Hdis Hfl.
  generalize dependent m'.
  generalize dependent m.
  induction l as [| x tl IH]; intros m Hlt Hdis m' Hfl.
  - by inv Hfl.
  - destruct x as [[b lo] hi].
    simpl in Hfl.
    destruct (Mem.free m b lo hi) eqn: Hfree; try discriminate.
    destruct (free_preserve_disjoint_and_lt m m0 b lo hi a Hlt Hdis Hfree)
      as [Hdis1 Hlt1].
    eapply IH; eauto.
Qed.

Lemma mem_step_preserve_disjoint_and_lt :
  forall (mi mi' : mem) (a : access_map),
    permMapLt a (getMaxPerm mi) ->
    permMapsDisjoint (getCurPerm mi) a ->
    mem_step mi mi' ->
    permMapsDisjoint (getCurPerm mi') a /\
      permMapLt a (getMaxPerm mi').
Proof.
  intros mi mi' a Hlt Hdis Hs.
  revert a Hlt Hdis.
  induction Hs; intros a Hlt Hdis.
  4 : {
    destruct (IHHs1 _ Hlt Hdis) as [Hdis1 Hlt1].
    destruct (IHHs2 _ Hlt1 Hdis1) as [Hdis2 Hlt2].
    split; auto.
  }
  - apply Mem.storebytes_access in H.
    split.
    + assert (Hcur: getCurPerm m' = getCurPerm m).
      { by rewrite /getCurPerm H. }
      by rewrite Hcur.
    + assert (Hmax: getMaxPerm m' = getMaxPerm m).
      { by rewrite /getMaxPerm H. }
      by rewrite Hmax.
  - unfold permMapsDisjoint in *.
    have Hfresh : ~ Mem.valid_block m b'.
    { eapply Mem.fresh_block_alloc; eauto. }
    split.
    + intros.
      destruct (Pos.eq_dec b b') as [->|Hneq].
      * have HaNone : a # b' ofs = None.
        { eapply invalid_block_empty; eauto. }
        exists ((getCurPerm m') # b' ofs).
        rewrite HaNone.
        rewrite /perm_union /=.
        destruct ((getCurPerm m') # b' ofs) as [p|] eqn:Hc; simpl; reflexivity.
      * specialize (Hdis b ofs) as [pu Hpu].
        exists pu.
        simpl.
        assert (Hcur: (getCurPerm m') # b ofs = (getCurPerm m) # b ofs).
        {
          rewrite /getCurPerm !PMap.gmap.
          inv H; simpl.
          rewrite PMap.gso //.
        }
        by rewrite Hcur.
    + unfold permMapLt in *.
      intros.
      destruct (Pos.eq_dec b b') as [->|Hneq].
      * have HaNone : a # b' ofs = None.
        { eapply invalid_block_empty; eauto. }
        rewrite HaNone.
        apply perm_order''_None.
      * specialize (Hlt b ofs).
        inv H; simpl.
        unfold getMaxPerm in *.
        rewrite !PMap.gmap //= in Hlt |- *.
        rewrite PMap.gso //.
  - eapply free_list_preserve_disjoint_and_lt; eauto.
Qed.

Lemma free_list_unchanged_on :
  forall m l m' P,
    Mem.free_list m l = Some m' ->
    (forall b lo hi, In (b,lo,hi) l ->
                     forall i, (lo <= i < hi)%Z -> ~ P b i) ->
    Mem.unchanged_on P m m'.
Proof.
  intros m l.
  generalize dependent m.
  induction l as [| [[b lo] hi] tl IH]; intros ??? Hfree Hout.
  - simpl in Hfree. inv Hfree. apply Mem.unchanged_on_refl.
  - simpl in Hfree.
    destruct (Mem.free m b lo hi) as [m1|] eqn:Hf; try discriminate.
    eapply Mem.unchanged_on_trans.
    + eapply Mem.free_unchanged_on; eauto.
      intros i Hi. eapply (Hout b lo hi).
      * left; reflexivity.
      * exact Hi.
    + eapply IH; eauto.
      intros b' lo' hi' Hin i Hi.
      eapply (Hout b' lo' hi'); [right; exact Hin | exact Hi].
Qed.

Lemma free_list_perm_at :
  forall m l m' b lo hi i,
    Mem.free_list m l = Some m' ->
    In (b,lo,hi) l ->
    (lo <= i < hi)%Z ->
    Mem.perm m b i Cur Freeable.
Proof.
  intros m l; revert m.
  induction l as [| [[b0 lo0] hi0] tl IH]; intros m m' b lo hi i Hfl Hin Hi.
  - inversion Hin.
  - simpl in Hfl.
    destruct (Mem.free m b0 lo0 hi0) as [m1|] eqn:Hf; try discriminate.
    simpl in Hin; destruct Hin as [Hin | Hin].
    + inversion Hin; subst b0 lo0 hi0.
      pose proof (Mem.free_range_perm _ _ _ _ _ Hf) as Hrng.
      exact (Hrng i Hi).
    + have Hperm1 : Mem.perm m1 b i Cur Freeable :=
        IH m1 m' b lo hi i Hfl Hin Hi.
      assert (Houtside : (b <> b0)%Z \/ (i < lo0)%Z \/ (hi0 <= i)%Z).
      { destruct (peq b b0) as [->|Hneq]; [|left; exact Hneq].
        right.
        assert (~ (lo0 <= i < hi0)%Z).
        { intro HinRange.
          by eapply (Mem.perm_free_2 _ _ _ _ _ Hf _ _ _ HinRange) in Hperm1.
        }
        lia.
      }
      eapply Mem.perm_free_3; eauto.
Qed.

(*

Lemma mem_step_unchanged_on_disjoint_gen
  (m m' : mem) (a : access_map) :
  permMapsDisjoint (getCurPerm m) a ->
  permMapLt a (getMaxPerm m) ->          (* for alloc/new blocks, if needed *)
  mem_step m m' ->
  Mem.unchanged_on (fun b ofs => a # b ofs <> None) m m'.
Proof.
  intros Hdis HltA Hstep.
  induction Hstep.
  4 : { eapply Mem.unchanged_on_trans; eauto.
        assert (permMapsDisjoint (getCurPerm m'') a /\
                  permMapLt a (getMaxPerm m'')).
        {
          eapply mem_step_preserve_disjoint_and_lt; eauto. }
        destruct H.
        by eapply IHHstep2.
      }
  - eapply Mem.storebytes_unchanged_on; eauto.
    intros.
    intro Ha.
    pose proof (Mem.storebytes_range_perm _ _ _ _ _ H) as Hrng.
    have Hperm : Mem.perm m b i Cur Writable.
    { eapply (Hrng i); eauto. }
    pose proof (disjoint_implies_cur_none m a Hdis b i Ha) as HcurNone.
    rewrite /Mem.perm in Hperm.
    rewrite /getCurPerm PMap.gmap /= in HcurNone.
    rewrite HcurNone in Hperm.
    inv Hperm.
  - eapply Mem.alloc_unchanged_on; eauto.
  - eapply free_list_unchanged_on; eauto.
    intros.
    have Hperm : Mem.perm m b i Cur Freeable.
    { eapply free_list_perm_at; eauto. }
    intros Ha.
    pose proof (disjoint_implies_cur_none m a Hdis b i Ha) as HcurNone.
    rewrite /Mem.perm in Hperm.
    rewrite /getCurPerm PMap.gmap /= in HcurNone.
    rewrite HcurNone in Hperm.
    inv Hperm.
Qed.

Lemma mem_step_unchanged_on_disjoint
  (m0 m'' : mem) (p a: access_map)
  (Hlt : permMapLt p (getMaxPerm m0)) :
  permMapsDisjoint p a ->
  permMapLt a (getMaxPerm m0) ->
  mem_step (restrPermMap Hlt) m'' ->
  Mem.unchanged_on (fun b ofs => a # b ofs <> None) (restrPermMap Hlt) m''.
Proof.
  intros Hdis Hperm Hstep.
  eapply mem_step_unchanged_on_disjoint_gen with (m := restrPermMap Hlt) (m' := m'') (a := a); eauto; eauto.
  - assert (Hp: mem_equiv.access_map_equiv (getCurPerm (restrPermMap Hlt)) p).
    { apply mem_equiv.getCur_restr. }
    rewrite /mem_equiv.access_map_equiv in Hp.
    rewrite /permMapsDisjoint.
    intros.
    specialize (Hp b).
    by rewrite Hp.
  - by rewrite restr_Max_eq.
Qed.
*)

Lemma load_restr_inv
  (chunk: memory_chunk) (m: Mem.mem) (p: access_map) (Hlt : permMapLt p (getMaxPerm m)) (b: Values.block) (ofs: Z) (v: val) :
  (forall b ofs k p,
      Mem.perm (restrPermMap Hlt) b ofs k p ->
      Mem.perm m b ofs k p) ->
  Mem.mem_contents (restrPermMap Hlt) = Mem.mem_contents m ->
  Mem.load chunk (restrPermMap Hlt) b ofs = Some v ->
  Mem.load chunk m b ofs = Some v.
Proof.
  intros.
  unfold Mem.perm in *.
  Transparent Mem.load.
  unfold Mem.load in *.
  destruct (Mem.valid_access_dec (restrPermMap Hlt) chunk b ofs Readable) as [Hva|Hno].
  2 : { discriminate. }
  assert (Mem.valid_access m chunk b ofs Readable) as Hva_m.
  { unfold Mem.valid_access in *.
    destruct Hva as [Hrange Halign].
    unfold Mem.range_perm in *.
    split; try done.
    intros.
    apply H. apply Hrange; done.
  }
  destruct (Mem.valid_access_dec m chunk b ofs Readable) as [Hva'|Hno'].
  2 : { done. }
  by rewrite <- H0.
Qed.

(*
Lemma mem_access_restr_le
  p (m: Mem.mem) perm (Hlt : permMapLt p (getMaxPerm m)) :
  forall b ofs k,
    Mem.perm (restrPermMap Hlt) b ofs k perm ->
    Mem.perm m b ofs k perm.
Proof.
  intros b ofs k Hperm.
  Search Mem.perm.
  unfold Mem.perm in *.
  Search Mem.perm_order'.
  eapply perm_order_trans211; eauto.
  Search Mem.perm_order''.
  destruct ((Mem.mem_access m) # b ofs k) as [p1|] eqn:Ha;
    destruct ((Mem.mem_access (restrPermMap Hlt)) # b ofs k) as [p2|] eqn:Hb;
    simpl; try done.
  2 : { admit. }
  
    unfold restrPermMap in Hb; simpl in Hb.
        rewrite Ha in Hb.
  unfold Mem.perm_order''.
  
  eapply Mem.perm_order'_trans; [exact Hperm |].
  unfold restrPermMap in Hperm; simpl.
  unfold restrPermMap; simpl.
*)


Lemma conc_mem_auth_lookup2 `{!conc_VSTGS OK_ty Σ} i g p m perms :
  perms !! i = Some (g, p) →
  conc_mem_auth m perms ⊢ ∃ Hp : permMapLt p (getMaxPerm m),
      thread_mem_auth g (restrPermMap Hp) ∗
        conc_mem_auth m (delete i perms).
Proof.
  rewrite /conc_mem_auth; intros.
  iIntros "(% & H)".
  iDestruct (big_sepM2_delete_l _ _ _ i (g, p) with "H") as "(% & % & (%Hlt & H2) & H3)"; auto.
  destruct Hlt as (Hlt & Hchr).
  iExists Hlt.
  by iFrame.
Qed.

Lemma conc_mem_auth_lookup2_rev `{!conc_VSTGS OK_ty Σ} i g p m perms
  (Hp : permMapLt p (getMaxPerm m)) :
  perms !! i = Some (g, p) →
  thread_mem_auth g (restrPermMap Hp) ∗
    conc_mem_auth m (delete i perms) ⊢
    conc_mem_auth m perms.
Proof.
  iIntros (Hlookup) "[Hthread (% & Hrest)]".
  rewrite <- (insert_delete perms i _ Hlookup).
  rewrite /conc_mem_auth.
  iDestruct "Hthread" as (σ) "[%Hcoh Hauth]".
  iDestruct (big_sepM2_dom with "Hrest") as %Hdom.
  rewrite delete_insert_delete delete_idemp in Hdom.
  assert (Hσs_none : σs !! i = None).
  {
    apply not_elem_of_dom.
    rewrite <- Hdom.
    apply not_elem_of_dom.
    by rewrite lookup_delete.
  }
  iExists (<[i := σ]> σs).
  rewrite big_sepM2_insert; auto.
  2 : { by rewrite lookup_delete. }
  rewrite delete_insert_delete delete_idemp.
  iSplitR "Hrest".
  - iFrame.
    iPureIntro.
    split; auto.
    eexists; eauto.
  - iFrame.
Qed.

Lemma conc_state_interp_lookup2_rev `{!conc_VSTGS OK_ty Σ} i g p m perms z
  (Hp : permMapLt p (getMaxPerm m)):
  perms !! i = Some (g, p) →
  thread_state_interp g (restrPermMap Hp) z ∗
    conc_mem_auth m (delete i perms) ⊢
    conc_state_interp m perms z.
Proof.
  iIntros (Hlookup) "((H & Hext) & Hconc)".
  iDestruct (conc_mem_auth_lookup2_rev i g p m perms Hp with "[$H $Hconc]") as "?"; auto.
  iFrame.
Qed.

Lemma conc_state_interp_lookup2 `{!conc_VSTGS OK_ty Σ} i g p m perms z :
  perms !! i = Some (g, p) →
  conc_state_interp m perms z ⊢ ∃ Hp : permMapLt p (getMaxPerm m),
      thread_state_interp g (restrPermMap Hp) z ∗ conc_mem_auth m (delete i perms).
Proof.
  iIntros (?) "(H & $)".
  iDestruct (conc_mem_auth_lookup2 with "[$H]") as (?) "($ & H)"; eauto.
Qed.

Lemma thread_state_interp_conc_state_interp_delete_insert_restr
  `{!conc_VSTGS OK_ty Σ} i g m perms z p
  (Hlt : permMapLt p (getMaxPerm m)) :
  thread_state_interp g (restrPermMap Hlt) z ∗
    conc_mem_auth m (delete i perms) ⊢
    conc_state_interp m (<[i := (g, p)]> perms) z.
Proof.
  rewrite <- insert_delete_insert.
  iIntros "(S & SC)".
  iDestruct (thread_conc_state_interp i with "[$S]") as "Si".
  rewrite /conc_state_interp.
  iDestruct "Si" as "[Hz Hi]".
  iFrame.
  iDestruct "SC" as (σs) "HSC".
  iDestruct "Hz" as (σi) "Hz".
  iDestruct (big_sepM2_dom with "HSC") as %Hdom.
  assert (Hσs_none : σs !! i = None).
  {
    apply not_elem_of_dom.
    rewrite <- Hdom.
    apply not_elem_of_dom.
    by rewrite lookup_delete.
  }
  rewrite /conc_mem_auth.
  iDestruct (big_sepM2_dom with "Hz") as %Hdomi.
  assert (Hi_in_dom : i ∈ dom σi).
  {
    rewrite <- Hdomi.
    apply elem_of_dom.
    eexists.
    rewrite lookup_singleton.
    done.
  }
  pose proof Hi_in_dom as Hi.
  apply elem_of_dom in Hi_in_dom.
  destruct Hi_in_dom as [σ Hlookupσ].

  assert (σi = {[ i := σ]}).
  {
    apply elem_of_dom in Hi as [ri Hri].
    apply map_eq => j.
    destruct (decide (j = i)) as [->|Hj].
    - rewrite lookup_insert; auto.
    - rewrite Hlookupσ in Hri.
      injection Hri as <-.
      rewrite lookup_insert_ne; auto.
      apply not_elem_of_dom.
      intro Hjdom.
      rewrite <- Hdomi in Hjdom.
      apply elem_of_dom in Hjdom as [x Hx].
      rewrite lookup_insert_ne in Hx; auto.
      rewrite lookup_empty in Hx.
      discriminate.
  }
  iExists (<[ i := σ ]> σs).
  rewrite big_sepM2_insert; auto; last first.
  by rewrite lookup_delete.
  iFrame.
  subst σi.
  rewrite big_sepM2_singleton.
  iDestruct "Hz" as "[%Hcoh Hg]".
  iSplit.
  - iPureIntro.
    destruct Hcoh as [Hp Hcoh].
    exists Hlt.
    eapply mem_coherent_equiv; eauto.
    eapply mem_equiv.cur_equiv_restr_mem_equiv. done.
  - iFrame.
Qed.

Lemma thread_state_interp_conc_state_interp_delete_insert
  `{!conc_VSTGS OK_ty Σ} i g m perms z :
  thread_state_interp g m z ∗
    conc_mem_auth m (delete i perms) ⊢
    conc_state_interp m (<[i := (g, getCurPerm m)]> perms) z.
Proof.
  rewrite <- insert_delete_insert.
  iIntros "(S & SC)".
  iDestruct (thread_conc_state_interp i with "[$S]") as "Si".
  rewrite /conc_state_interp.
  iDestruct "Si" as "[Hz Hi]".
  iFrame.
  iDestruct "SC" as (σs) "HSC".
  iDestruct "Hz" as (σi) "Hz".
  iDestruct (big_sepM2_dom with "HSC") as %Hdom.
  assert (Hσs_none : σs !! i = None).
  {
    apply not_elem_of_dom.
    rewrite <- Hdom.
    apply not_elem_of_dom.
    by rewrite lookup_delete.
  }
  rewrite /conc_mem_auth.
  iDestruct (big_sepM2_dom with "Hz") as %Hdomi.
  assert (Hi_in_dom : i ∈ dom σi).
  { rewrite <- Hdomi.
    rewrite elem_of_dom; eexists.
    by rewrite lookup_singleton.
  }
  pose proof Hi_in_dom as Hi.
  apply elem_of_dom in Hi_in_dom.
  destruct Hi_in_dom as [σ Hlookupσ].
  assert (σi = {[ i := σ]}).
  { apply elem_of_dom in Hi as [ri Hri].
    apply map_eq => j.
    destruct (decide (j = i)) as [->|Hj].
    - rewrite lookup_insert; auto.
    - rewrite Hlookupσ in Hri.
      injection Hri as <-.
      rewrite lookup_insert_ne; auto.
      apply not_elem_of_dom.
      intro Hjdom.
      rewrite <- Hdomi in Hjdom.
      apply elem_of_dom in Hjdom as [x Hx].
      rewrite lookup_insert_ne in Hx; auto.
      rewrite lookup_empty in Hx.
      discriminate.
  }
  iExists (<[ i := σ ]> σs).
  rewrite big_sepM2_insert; auto; last first.
  by rewrite lookup_delete.
  iFrame.
  iDestruct (big_sepM2_delete _ _  _ i (g, getCurPerm m) σ with "Hz") as "[Hzi H]"; auto.
  by rewrite lookup_insert.
  iFrame.
  rewrite H.
  by rewrite !delete_singleton big_sepM2_empty.
Qed.
    
Lemma conc_mem_auth_lookup1 `{!conc_VSTGS OK_ty Σ} i g p m perms :
  perms !! i = Some (g, p) →
  conc_mem_auth m perms ⊢ ∃ Hp : permMapLt p (getMaxPerm m),
        thread_mem_auth g (restrPermMap Hp) ∗
          (∀ m', ⌜mem_step (restrPermMap Hp) m' /\ sc_others_lt_and_disjoint perms i m m'⌝ ∧
             thread_mem_auth g m' -∗
        conc_mem_auth m' (<[i:=(g, getCurPerm m')]>perms)).
Proof.
  rewrite /conc_mem_auth; intros.
  iIntros "(% & H)".
  iDestruct (big_sepM2_delete_l _ _ _ i (g, p) with "H") as "H"; auto.
  iDestruct "H" as (?) "(% & (% & H) & Hbig)".
  destruct H1 as (Hlt & H2). 
  rename x2 into σ.
  iExists Hlt. iFrame.
  iSplit.
  iPureIntro.
  { split; auto. }
  iIntros (m') "(%HSc & H)".
  destruct HSc as (HSc & (sc_others_still_lt & sc_others_still_lt1 & sc_perm_disjoint)).
  rewrite /thread_mem_auth /mem_auth.
  remember (restrPermMap Hlt).
  clear H2.
  iStopProof.
  generalize dependent m; generalize dependent p; generalize dependent perms.
  induction HSc; intros; subst; iIntros "(Hbig & H)".
  4 : {
    assert (Hcur: mem_equiv.access_map_equiv (getCurPerm (restrPermMap Hlt)) p).
    { apply mem_equiv.getCur_restr. }
    assert (Hdisj: ∀ (j : nat) (g : gname) (a : access_map),
               j <> i → perms !! j = Some (g, a) -> permMapsDisjoint (getCurPerm m'') a /\
                 permMapLt a (getMaxPerm m'')).
    {
      intros.
      eapply (mem_step_preserve_disjoint_and_lt (restrPermMap Hlt) m'' a); eauto.
      rewrite restr_Max_eq.
      eapply (sc_others_still_lt2 j g0 a); auto.
      rewrite /mem_equiv.access_map_equiv in Hcur.
      rewrite /permMapsDisjoint.
      intros.
      specialize (Hcur b).
      rewrite Hcur.
      rewrite /permMapsDisjoint_at in sc_perm_disjoint0.
      specialize ((sc_perm_disjoint0 j) H1).
      by rewrite H H2 /= /permMapsDisjoint in sc_perm_disjoint0.
    }
    iDestruct (IHHSc2 (<[i:=(g, getCurPerm m'')]>perms) with "[-]") as (?) "Hbig".
    - intros ????; rewrite lookup_insert_ne //; by apply sc_others_still_lt.
    - intros.
      rewrite /permMapsDisjoint_at.
      rewrite lookup_insert.
      rewrite lookup_insert_ne //.
      destruct (perms !! j) eqn: E; last first; try done.
      destruct p0.
      eapply Hdisj; eauto.
    - apply lookup_insert.
    - symmetry; apply restrPermMap_eq.
    - intros.
      rewrite lookup_insert_ne // in H2.
      eapply Hdisj; eauto.
    - rewrite delete_insert_delete; iFrame.
      iApply (big_sepM2_mono with "Hbig"); intros.
      destruct y1.
      do 2 f_equiv.
      rewrite /impl /coherent.
      intros (Hlt1 & ?).
      apply lookup_delete_Some in H1, H2.
      destruct H1 as (Hneq & Hperm).
      destruct H2 as (_ & Hσ).
      assert (Hc: permMapsDisjoint (getCurPerm m'') a /\ permMapLt a (getMaxPerm m'')).
      { eapply Hdisj; eauto. }
      destruct Hc as (Hp & Hlta).
      exists Hlta.
      intros.
      split.
      + intros.
        apply H3.
        apply semantics_lemmas.mem_step_nextblock' in HSc1.
        rewrite restrPermMap_nextblock in H1.
        rewrite restrPermMap_nextblock in HSc1.
        rewrite restrPermMap_nextblock. lia.
      + rewrite /coherent_loc /contents_cohere.
        rewrite / coherent_loc in H3 |- *.
        rewrite /contents_cohere /access_cohere /= in H3 |- *.
        rewrite ! access_at_restrPermMap_Cur in H3 |- *.
        split; last first.
        * specialize (H3 loc).
          destruct H3 as (_ & _ & Hperm_order).
          by rewrite access_at_restrPermMap_Cur in Hperm_order.
        * rewrite /contents_cohere restrPermMap_contents /juicy_mem.contents_at /=.
          intros.
          pose proof H1 as Hy.
          rewrite /resource_at /resR_to_resource /= in H1.
          rewrite /coherent_loc /contents_cohere in H3.
          pose proof H3 as Hx.
          rewrite /shared.val_of /resource_at in H3.
          specialize (Hx loc).
          destruct Hx as (Hx & Hx1).
          apply Hx1 in Hy.
          destruct (y2 !! loc) eqn: E; last first.
          { rewrite /resource_at in H1.
            rewrite E in H1; inv H1.
          }
          rewrite E /= in H1.
          destruct s; last first. inv H1.
          specialize (H3 loc).
          destruct H3 as (_ & _ & HpermHlt1).
          rewrite E in HpermHlt1.
          pose proof (access_at_restrPermMap_Cur a m0 loc Hlt1) as Haccess1.
          rewrite Haccess1 in HpermHlt1.
          assert (Hread: Mem.perm_order' (a # (loc.1) loc.2) Readable).
          { rewrite mem_lemmas.po_oo.
            eapply readable_dfrac_perm_order with (Hlt:= Hlt1) (rsh := rsh); try eauto.
            rewrite Haccess1; auto.
          }
          have Hvb : Mem.valid_block (restrPermMap Hlt) loc.1.
          { unfold Mem.valid_block.
            rewrite restrPermMap_nextblock /Plt.
            destruct (Pos.lt_total loc.1 (Mem.nextblock m0)) as [Hl | [Heq | Hl]]; auto; exfalso.
            - rewrite Heq in Hx.
              assert ((Mem.nextblock m0 >= Mem.nextblock m0)%positive) by lia.
              by apply Hx in H2.
            - have Hge : (loc.1 >= Mem.nextblock m0)%positive.
              { assert ((Mem.nextblock m0 ≤ loc.1)%positive)
                  by apply (Pos.lt_le_incl _ _ Hl); lia.
              }
              by apply Hx in Hge.
          }
          assert (¬ Mem.perm (restrPermMap Hlt) loc.1 loc.2 Cur Writable).
          { rewrite /Mem.perm.
            intros Hcontra.
            rewrite restrPermMap_Cur_eq in Hcontra.
            assert (permMapsDisjoint p a).
            { rewrite /permMapsDisjoint_at in sc_perm_disjoint0.
              have Hki : k <> i := fun Hki_eq => Hneq (eq_sym Hki_eq).
              specialize ((sc_perm_disjoint0 k) Hki).
              by rewrite H Hperm in sc_perm_disjoint0.
            }
            rewrite /permMapsDisjoint in H2.
            assert (¬ ∃ pu : option permission,
                        perm_union (a # (loc.1) loc.2) (p # (loc.1) loc.2) = Some pu).
            { apply (perm_order_clash (a # (loc.1) loc.2) (p # (loc.1) loc.2) Hread Hcontra). }
            specialize (H2 (loc.1) (loc.2)).
            by rewrite perm_union_comm in H2. 
          }
          assert (ZMap.get loc.2 (Mem.mem_contents (restrPermMap Hlt)) # (loc.1) =
                     ZMap.get loc.2 (Mem.mem_contents m'') # (loc.1)).
          { by apply (semantics_lemmas.mem_step_obeys_cur_write
                     (restrPermMap Hlt) (loc.1) (loc.2) m'' Hvb H2).
          }
          rewrite /juicy_mem.contents_at mem_contents_restrPermMap in Hy.
          rewrite mem_contents_restrPermMap in H3.
          by rewrite Hy in H3.
     - rewrite insert_insert; iFrame.
  }
  - pose proof H as Hst.
    pose proof H as Hst1.
    Transparent Mem.storebytes.
    rewrite /Mem.storebytes in H.
    destruct (Mem.range_perm_dec _ _ _ _ Cur Writable) as [Hf | Hf]; last first; try done.  
    injection H as Hxy.
    pose proof (f_equal Mem.mem_access (eq_sym Hxy)) as Hacc.
    simpl in Hacc.
    assert (Hcur : getCurPerm m' = getCurPerm (restrPermMap Hlt)).
    { rewrite /getCurPerm.
      rewrite Hacc. done. }
    assert (Hmax : getMaxPerm m' = getMaxPerm (restrPermMap Hlt)).
    { by rewrite /getMaxPerm Hacc. }
    pose proof (f_equal Mem.mem_contents (eq_sym Hxy)) as Hcnt.
    simpl in Hcnt.
    pose proof (f_equal Mem.nextblock (eq_sym Hxy)) as Hnxt.
    simpl in Hnxt.
    clear Hxy.
    setoid_rewrite (big_sepM2_delete_l _ _ _ i (g, getCurPerm m')) at 2; auto.
    2 : { rewrite lookup_insert //=. }
    iDestruct "H" as (σ') "(% & H)".
    iDestruct (resource_map.resource_map_auth_valid with "H") as %(_ & Hvalid).
    iExists (<[i := σ']>σs).
    iExists σ'.
    iSplit; first rewrite lookup_insert //.
    iSplitR "Hbig".
    iFrame. iPureIntro.
    split; auto.
    exists (cur_lt_max _); rewrite restrPermMap_eq //.
    rewrite ! delete_insert_delete.
    iApply (big_sepM2_mono with "Hbig"); intros.
    destruct y1.
    do 2 f_equiv.
    rewrite /impl /coherent.
    intros (Hlt1 & ?).
    apply lookup_delete_Some in H2, H3.
    destruct H2.
    destruct H3.
    unshelve eexists.
    {
      have Hperms_k : perms !! k = Some (g0, a) by done.
      eapply (sc_others_still_lt _ _ a); eauto.
    }
    simpl; split; auto.
    * intros; apply H4; auto; simpl in *. rewrite Hnxt // in H7.
    * unfold Mem.range_perm, Mem.perm in Hf.
      assert (Hloc: forall loc, contents_at m' loc = contents_at (restrPermMap Hlt) loc
                           \/ can_store_at (getCurPerm (restrPermMap Hlt)) loc).
      { eapply storebytes_contents_or_canstore_cur; eauto. }
      destruct (H4 loc) as (_ & Hcoh).
      destruct (Hloc loc) as [Hmem_eq | Hwrite].
      + rewrite /contents_at in Hmem_eq.
        rewrite /coherent_loc /contents_cohere /resource_at /juicy_mem.contents_at in Hcoh |- *.
        split; simpl.
        intros.
        rewrite Hmem_eq mem_contents_restrPermMap.
        rewrite mem_contents_restrPermMap in Hcoh.
        apply Hcoh; auto.
        rewrite /access_cohere !access_at_restrPermMap_Cur in Hcoh |- *.
        apply Hcoh.
      + rewrite / coherent_loc in Hcoh |- *.
        rewrite /contents_cohere /access_cohere /= in Hcoh |- *.
        rewrite ! access_at_restrPermMap_Cur in Hcoh |- *.
        split; try apply Hcoh.
        intros ? Hres.
        destruct Hcoh as (Hv & _); specialize (Hv _ Hres).
        rewrite !restrPermMap_contents in Hv |- *.
        rewrite /resource_at /resR_to_resource in Hres.
        rewrite /permMapsDisjoint_at in sc_perm_disjoint0.
        specialize (sc_perm_disjoint0 k).
        rename H2 into Hneq.
        rename H5 into Hperm.
        rewrite Hperm in sc_perm_disjoint0.
        specialize (sc_perm_disjoint0 (not_eq_sym Hneq)).
        rewrite /permMapsDisjoint /= in sc_perm_disjoint0.
        destruct (y2 !! loc) eqn: E; last first.
        { rewrite E in Hres. inv Hres. } 
        rewrite E /= in Hres.
        destruct s; last first. inv Hres.
        rewrite /resource_at in H4.
        specialize (H4 loc).
        destruct H4 as (_ & _ & HpermHlt1).
        rewrite E in HpermHlt1.
        apply writable_at_perm_order_cases
          with (x := access_at (restrPermMap Hlt) loc Cur) in Hwrite; auto.
        2 : { by rewrite /getCurPerm /access_at PMap.gmap. }
        rewrite /access_at in Hwrite.
        rewrite restrPermMap_Cur_eq in Hwrite.        
        pose proof (access_at_restrPermMap_Cur a m0 loc Hlt1) as Haccess1.
        rewrite /access_cohere Haccess1 in HpermHlt1.
        assert (Hread: Mem.perm_order' (a # (loc.1) loc.2) Readable).
        { rewrite mem_lemmas.po_oo.
          eapply readable_dfrac_perm_order with (Hlt:= Hlt1) (rsh := rsh) ; try eauto.
          by rewrite Haccess1.
        }
        assert (Hwrite1: Mem.perm_order' (p # (loc.1) loc.2) Writable).
        { destruct Hwrite as [Hwrite | Hwrite];
            rewrite mem_lemmas.po_oo; rewrite Hwrite;
            [try apply perm_F_any | apply perm_refl].
        }
        assert (¬ ∃ pu : option permission,
                    perm_union (a # (loc.1) loc.2) (p # (loc.1) loc.2) = Some pu).
        { apply (perm_order_clash (a # (loc.1) loc.2) (p # (loc.1) loc.2)); done. }
        rewrite H1 in sc_perm_disjoint0.
        specialize (sc_perm_disjoint0 loc.1 loc.2).
        simpl in sc_perm_disjoint0.
        by rewrite perm_union_comm in H2.
  - Transparent Mem.alloc.
    rewrite /Mem.alloc /= in H.
    injection H as Hxy.
    pose proof (f_equal Mem.mem_access (eq_sym Hxy)) as Hacc.
    simpl in Hacc.
    assert (mem_equiv.access_map_equiv (getCurPerm (restrPermMap Hlt)) p).
    { apply mem_equiv.getCur_restr. }
    pose proof (f_equal Mem.mem_contents (eq_sym Hxy)) as Hcnt.
    simpl in Hcnt.
    pose proof (f_equal Mem.nextblock (eq_sym Hxy)) as Hnxt.
    simpl in Hnxt.
    clear Hxy.
    setoid_rewrite (big_sepM2_delete_l _ _ _ i (g, getCurPerm m')) at 2; auto.
    2 : { rewrite lookup_insert //=. }
    iDestruct "H" as (σ') "(% & H)".
    iDestruct (resource_map.resource_map_auth_valid with "H") as %(_ & Hvalid).
    iExists (<[i := σ']>σs).
    iExists σ'.
    iSplit; first rewrite lookup_insert //.
    iSplitR "Hbig".
    iFrame. iPureIntro.
    split; auto.
    exists (cur_lt_max _); rewrite restrPermMap_eq //.
    rewrite ! delete_insert_delete.
    iApply (big_sepM2_mono with "Hbig"); intros.
    apply lookup_delete_Some in H5.
    destruct y1.
    iIntros "(%Hlt1 & H1)".
    iFrame "H1".
    iPureIntro.
    split; auto.
    destruct Hlt1 as (Hlt1 & Hchr).
    destruct H5 as [Hik Hσk].
    have Hperms_k : perms !! k = Some (g0, a).
    { rewrite lookup_delete_ne in H4; auto. }
    assert (Hlt': permMapLt a (getMaxPerm m')).
    { eapply sc_others_still_lt; eauto. }
    exists Hlt'.
    split.
    * intro Hge.
      rewrite restrPermMap_nextblock /= in Hge.
      rewrite /coherent in Hchr.
      apply Hchr.
      rewrite restrPermMap_nextblock. lia.
    * rewrite /coherent_loc.
      split.
      ** rewrite /contents_cohere restrPermMap_contents /juicy_mem.contents_at /=.
         intros.
         rewrite /coherent in Hchr.
         specialize (Hchr loc).
         destruct Hchr as (? & Hchr).
         rewrite /coherent_loc /contents_cohere in Hchr.
         destruct Hchr as (Hchr & ?).
         destruct (peq (loc.1) (Mem.nextblock m0)) as [Heq1 | Hneq].
         { rewrite /resource_at in H4.
           destruct (y2 !! loc) eqn: E; last first.
           { rewrite /resource_at in H5.
             rewrite E in H5. inv H5.
           }
           rewrite restrPermMap_nextblock in H6.
           rewrite Heq1 in H6.
           assert (Hge: (Mem.nextblock m0 >= Mem.nextblock m0)%positive) by lia.
           by apply H6 in Hge.
         }
         apply Hchr in H5.
         rewrite /juicy_mem.contents_at mem_contents_restrPermMap in H5.
         rewrite Hcnt.
         rewrite PMap.gso //.
      ** rewrite /access_cohere.
         rewrite access_at_restrPermMap_Cur.
         Unshelve.
         2 : { apply cur_lt_max. }
         rewrite /coherent in Hchr.
         specialize (Hchr loc).
         destruct Hchr as (? & ?).
         rewrite /coherent_loc in H6.
         destruct H6 as (? & ?).
         rewrite /access_cohere in H7.
         by rewrite access_at_restrPermMap_Cur in H7.
  - setoid_rewrite (big_sepM2_delete_l _ _ _ i (g, getCurPerm m')) at 2; auto.
    iDestruct "H" as (σ') "(% & H)".
    iDestruct (resource_map.resource_map_auth_valid with "H") as %(_ & Hvalid).
    2 : { rewrite lookup_insert; auto. }
    iExists (<[i := σ']>σs).
    iExists σ'.
    iSplit; first rewrite lookup_insert //.
    iSplitR "Hbig".
    iFrame. iPureIntro.
    split; auto.
    exists (cur_lt_max _); rewrite restrPermMap_eq //.
    rewrite ! delete_insert_delete.
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
    assert (Hlt': permMapLt a (getMaxPerm m')).
    { eapply sc_others_still_lt; eauto. }
    exists Hlt'.
    split.
    * intro Hge.
      rewrite restrPermMap_nextblock /= in Hge.
      rewrite /coherent restrPermMap_nextblock in Hchr.
      apply Hchr.
      apply nextblock_free_list in H.
      rewrite restrPermMap_nextblock in H.
      by rewrite H in Hge.
    * rewrite /coherent_loc.
      split.
      ** rewrite /contents_cohere restrPermMap_contents /juicy_mem.contents_at /=.
         intros.
         rewrite /coherent in Hchr.
         specialize (Hchr loc).
         destruct Hchr as (? & Hchr).
         rewrite /coherent_loc /contents_cohere in Hchr.
         destruct Hchr as (Hchr & ?).
         destruct (peq (loc.1) (Mem.nextblock m0)) as [Heq1 | Hneq].
         { rewrite /resource_at in H4.
           destruct (y2 !! loc) eqn: E; last first.
           { rewrite E in H4. inv H4. }
           rewrite restrPermMap_nextblock in H5.
           rewrite Heq1 in H5.
           assert (Hge: (Mem.nextblock m0 >= Mem.nextblock m0)%positive) by lia.
           by apply H5 in Hge.
         }
         apply Hchr in H4.
         rewrite /juicy_mem.contents_at mem_contents_restrPermMap in H4.
         apply free_list_contents in H.
         rewrite H.
         by rewrite mem_contents_restrPermMap.
      ** rewrite /access_cohere.
         rewrite access_at_restrPermMap_Cur.
         Unshelve.
         rewrite /coherent in Hchr.
         specialize (Hchr loc).
         destruct Hchr as (? & ?).
         rewrite /coherent_loc in H5.
         destruct H5 as (? & ?).
         rewrite /access_cohere in H6.
         by rewrite access_at_restrPermMap_Cur in H6.
Qed.

Lemma conc_state_interp_lookup `{!conc_VSTGS OK_ty Σ} i g p m perms z :
  perms !! i = Some (g, p) →
  conc_state_interp m perms z ⊢ (∃ Hp : permMapLt p (getMaxPerm m),
        thread_state_interp g (restrPermMap Hp) z) ∗
    (∀ m', ⌜OpSC i m m' p perms⌝ ∧ thread_state_interp g m' z -∗
           conc_state_interp m' (<[i:=(g, getCurPerm m')]>perms) z).
Proof.
  iIntros (?) "(H & $)".
  iDestruct (conc_mem_auth_lookup with "[$H]") as "H"; eauto.
  iDestruct "H" as "($ & H)".
  iIntros (?) "(% & (? & $))".
  iApply "H". iSplit; done.
Qed.

Lemma conc_state_interp_lookup1 `{!conc_VSTGS OK_ty Σ} i g p m perms z :
  perms !! i = Some (g, p) →
  conc_state_interp m perms z ⊢ ∃ Hp : permMapLt p (getMaxPerm m),
        thread_state_interp g (restrPermMap Hp) z ∗
    (∀ m', ⌜mem_step (restrPermMap Hp) m' /\ sc_others_lt_and_disjoint perms i m m'⌝ ∧
             thread_state_interp g m' z -∗
        conc_state_interp m' (<[i:=(g, getCurPerm m')]>perms) z).
Proof.
  iIntros (?) "(H & $)".
  iDestruct (conc_mem_auth_lookup1 with "[$H]") as (?) "($ & H)"; eauto.
  iIntros (?) "(% & (? & $))".
  iApply "H". iSplit; done.
Qed.

(* Definition lock_state `{!conc_heapGS Σ} `{lockGS Σ} γ m ls := lock_state(heapGS0 := HeapGS _ _ (thread_gen_heapGS γ) _) m ls. *)
Definition lock_state `{!conc_VSTGS Σ} (m : mem) (lG : AMap.t (option lock_info)) :=
  ∃ lcs : gmap address ((option access_map * gname * resource_map.rmapUR _ _ _) * mpred),
  ⌜forall l p, (exists g σ R, lcs !! l = Some ((p,g,σ), R)) <-> (exists ps, AMap.find l lG = Some ps /\ p = option_map snd ps)⌝ ∧
  own(inG0 := lockGS_inG) lockGS_gname (gmap_view.gmap_view_auth (dfrac.DfracOwn 1) (invariant_unfold <$> snd <$> lcs)) ∗
  ([∗ map] l ↦ '((p,g,σ),R)∈lcs,
     resource_map.resource_map_auth(H1 := gen_heapGpreS_heap(gen_heapGpreS := conc_gen_heap_inG)) g 1 σ ∗
     <affine> ⌜match p with
     | Some p => exists Hp : permMapLt p (getMaxPerm m), coherent (restrPermMap Hp) σ /\
        Mem_load_unchecked Mptr m l.1 l.2 = Vptrofs (Ptrofs.one) /\ (▷R) σ
     | None => σ = ε /\ Mem_load_unchecked Mptr m l.1 l.2 = Vptrofs (Ptrofs.zero)
     end⌝).

Lemma locks_init `{!inG Σ (gmap_view.gmap_viewR address (laterO (iPropO Σ)))} m :
  ⊢ |==> ∃ γ, ∀ (_ : conc_heapGS Σ) γh, let lG := LockGS Σ _ γ in lock_state γh m ∅.
Proof.
  unfold lock_state, semax_conc_pred.lock_state.
  iMod (own_alloc(i := inG0)) as (γ) "H".
  { apply gmap_view.gmap_view_auth_valid. }
  iModIntro; iExists γ; iIntros.
  iExists ∅; iSplit => //=.
  rewrite fmap_empty.
  iSplitL => //.
Qed.  

Lemma init_conc_VST: forall Z `{!VSTGpreS Z Σ} `{!inG Σ (gmap_view.gmap_viewR address (laterO (iPropO Σ)))} m (z : Z),
  ⊢ |==> ∀ _ : invGS_gen HasNoLc Σ, ∃ HH : conc_gen_heapGS Σ, ∃ _ : funspecGS Σ, ∃ _ : externalGS Z Σ, ∃ HL : lockGS Σ, ∃ γ0 γl γm,
    let H : conc_VSTGS Z Σ := ConcVSTGS _ _ (ConcHeapGS _ _ _ _) _ _ in
    (thread_state_interp γ0 Mem.empty z ∗ funspec_auth ∅ ∗ has_ext z) ∗
    ghost_map.ghost_map_auth(H0 := gen_heapGpreS_meta(gen_heapGpreS := conc_gen_heap_inG)) (@conc_gen_meta_name _ HH) 1 ∅ ∗
    lock_state γl m ∅ ∗ thread_mem_auth γl Mem.empty ∗
    ghost_map.ghost_map_auth(H0 := gen_heapGpreS_meta(gen_heapGpreS := conc_gen_heap_inG)) γm 1 ∅.
Proof.
  intros; iIntros.
  iMod gen_heap_init_names_empty as (??) "(? & ?)".
  iMod (own_alloc(A := gmap_view.gmap_viewR address (@funspecO' Σ)) (gmap_view.gmap_view_auth (dfrac.DfracOwn 1) ∅)) as (γf) "?".
  { apply gmap_view.gmap_view_auth_valid. }
  iMod (ext_alloc z) as (?) "(? & ?)".
  iMod gen_heap_init_names_empty as (γl ?) "(? & ?)".
  iMod (locks_init) as (?) "HL".
  iIntros "!>" (?).
  iExists (ConcGenHeapGS _ _ γm), (FunspecG _ _ γf), _, _, γh, γl, γm0.
  iFrame.
  pose proof (empty_coherent Mem.empty); repeat iSplit => //.
Qed.
(* end concurrency setup *)
*)

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
  simpl (Jext_spec_pre); simpl (Jext_spec_type); simpl (Jext_spec_post);
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
  CSL_all_safe : forall (HH : VSTGS unit CSL_Σ) (HL : lockGS CSL_Σ), @semax_prog _ _ HH (concurrent_ext_spec CSL_CS CSL_ext_link)
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

  Lemma CEspec_cases : forall `{!VSTGS unit Σ, lockGS Σ} e
    (x : Jext_spec_type (concurrent_ext_spec CS ext_link) e),
    e = LOCK \/ e = UNLOCK \/ e = MKLOCK \/ e = FREE_LOCK \/ e = CREATE.
  Proof.
    intros.
    simpl in x.
    repeat (if_tac in x; [destruct e; try done; inversion H0 as [H1];
                          apply ext_link_inj in H1 as <-; auto
      | clear H0]); last done.
  Qed.

  (* funspecs_destruct isn't working well, so prove a spec lemma for each function *)
  Ltac next_spec := subst; let Hspecs := fresh "Hspecs" in match goal with |-context[add_funspecs_rec _ _ _ ?l] =>
    destruct l eqn: Hspecs; first done;
    injection Hspecs; clear Hspecs; intros Hspecs <-; simpl;
    unfold funspec2pre, funspec2post, ef_id_sig; simpl; if_tac end.

  (*
  Ltac solve_spec x := intros; revert x;
    unfold ext_spec_post, concurrent_ext_spec;
    pose proof ext_link_inj as Hinj; fold ext_link in Hinj;
    repeat (next_spec; first absurd_ext_link_naming); next_spec; last done;
    intros; split; [|intros (? & Heq & ?)]; eauto;
    inversion Heq as [Heq0 Heq']; apply inj_pair2 in Heq'; subst; auto. *)

  Ltac solve_spec x :=
    intros;
    revert x;
    unfold ext_spec_post, concurrent_ext_spec;
    pose proof ext_link_inj as Hinj;
    fold ext_link in Hinj;
    repeat (next_spec; first absurd_ext_link_naming);
    next_spec; last done;
    let y := fresh "x" in
    intros y;
    iSplit;
    [ iIntros "H";
      iExists y;
      iSplit;
      [ iPureIntro; apply JMeq.JMeq_refl
      | iExact "H" ]
    | iIntros "H";
      iDestruct "H" as (x'') "[%Heq H]";
      let Heq0 := fresh "Heq0" in
      let Heq' := fresh "Heq'" in
      inversion Heq as [Heq0 Heq'];
      apply inj_pair2 in Heq';
      subst;
      iExact "H" ].

  (* Definition TT_ty (Σ : gFunctors) (A : TypeTree) : Type :=
    oFunctor_car
      (dependent_type_functor_rec A)
      (Ofe (iProp Σ) ouPred_ofe_mixin)
      (Ofe (iPropI Σ) (bi_ofe_mixin (iPropI Σ))). *)

(*  Lemma CEspec_acquire_pre : forall `{Hconc : conc_VSTGS unit Σ} `{Hlock : lockGS Σ} (g : gname),
    let HVST : VSTGS unit Σ := @thread_VSTGS unit Σ Hconc g in
     forall (x : Jext_spec_type (concurrent_ext_spec CS ext_link) LOCK) args,
        (Jext_spec_pre (concurrent_ext_spec CS ext_link) LOCK x (genv_symb_injective ge)
           (sig_args (ef_sig LOCK)) args) ⊣⊢
     match acquire_spec with mk_funspec _ _ A _ P _ => ∃ x'', ⌜JMeq.JMeq x x''⌝ ∧ (funspec2pre' A P x'' (genv_symb_injective ge) (sig_args (ef_sig LOCK)) args) end.
  Proof.
    solve_spec x.
  Qed.

  Lemma CEspec_acquire_post : forall `{Hconc : conc_VSTGS unit Σ, Hlock : lockGS Σ} g,
      let HVST : VSTGS unit Σ := @thread_VSTGS unit Σ Hconc g in
      forall x args,
      Jext_spec_post (concurrent_ext_spec CS ext_link) LOCK x (genv_symb_injective ge) (sig_res (ef_sig LOCK)) args ⊣⊢
        match acquire_spec with mk_funspec _ _ A _ _ Q => ∃ x'', ⌜JMeq.JMeq x x''⌝ ∧ funspec2post' A Q x'' (genv_symb_injective ge) (sig_res (ef_sig LOCK)) args end.
  Proof.
    solve_spec x.
  Qed.

  (*
  
  Search (conc_VSTGS _ _ -> VSTGS _ _).

  Lemma CEspec_acquire_pre : forall `{!conc_VSTGS unit Σ, lockGS Σ} x args,
    Jext_spec_pre (concurrent_ext_spec CS ext_link) LOCK x (genv_symb_injective ge) (sig_args (ef_sig LOCK)) args ⊣⊢
    match acquire_spec with mk_funspec _ _ A _ P _ => ∃ x'', ⌜JMeq.JMeq x x''⌝ ∧ funspec2pre' A P x'' (genv_symb_injective ge) (sig_args (ef_sig LOCK)) args end.
  Proof.
    solve_spec x.
  Qed.
  
  Lemma CEspec_acquire_post : forall `{!VSTGS unit Σ, lockGS Σ} x args,
      Jext_spec_post (concurrent_ext_spec CS ext_link) LOCK x (genv_symb_injective ge) (sig_res (ef_sig LOCK)) args ⊣⊢
        match acquire_spec with mk_funspec _ _ A _ _ Q => ∃ x'', ⌜JMeq.JMeq x x''⌝ ∧ funspec2post' A Q x'' (genv_symb_injective ge) (sig_res (ef_sig LOCK)) args end.
  Proof.
    solve_spec x.
  Qed.

  Lemma CEspec_release_pre : forall `{!VSTGS unit Σ, lockGS Σ} x args,
      Jext_spec_pre (concurrent_ext_spec CS ext_link) UNLOCK x (genv_symb_injective ge) (sig_args (ef_sig UNLOCK)) args ⊣⊢
      match release_spec with mk_funspec _ _ A _ P _ => ∃ x'', ⌜JMeq.JMeq x x''⌝ ∧ funspec2pre' A P x'' (genv_symb_injective ge) (sig_args (ef_sig UNLOCK)) args end.
  Proof.
    solve_spec x.
  Qed.

  Lemma CEspec_release_post : forall `{!VSTGS unit Σ, lockGS Σ} x args,
    Jext_spec_post (concurrent_ext_spec CS ext_link) UNLOCK x (genv_symb_injective ge) (sig_res (ef_sig UNLOCK)) args ⊣⊢
      match release_spec with mk_funspec _ _ A _ _ Q => ∃ x'', ⌜JMeq.JMeq x x''⌝ ∧ funspec2post' A Q x'' (genv_symb_injective ge) (sig_res (ef_sig UNLOCK)) args end.
  Proof.
    solve_spec x.
  Qed.

  Lemma CEspec_makelock_pre : forall `{!VSTGS unit Σ, lockGS Σ} x args,
      Jext_spec_pre (concurrent_ext_spec CS ext_link) MKLOCK x (genv_symb_injective ge) (sig_args (ef_sig MKLOCK)) args ⊣⊢
        match makelock_spec CS with mk_funspec _ _ A _ P _ => ∃ x'', ⌜JMeq.JMeq x x''⌝ ∧ funspec2pre' A P x'' (genv_symb_injective ge) (sig_args (ef_sig MKLOCK)) args end.
  Proof.
    solve_spec x.
  Qed.

  Lemma CEspec_makelock_post : forall `{!VSTGS unit Σ, lockGS Σ} x args,
    Jext_spec_post (concurrent_ext_spec CS ext_link) MKLOCK x (genv_symb_injective ge) (sig_res (ef_sig MKLOCK)) args ⊣⊢
      match makelock_spec CS with mk_funspec _ _ A _ _ Q => ∃ x'', ⌜JMeq.JMeq x x''⌝ ∧ funspec2post' A Q x'' (genv_symb_injective ge) (sig_res (ef_sig MKLOCK)) args end.
  Proof.
    solve_spec x.
  Qed.

  Lemma CEspec_freelock_pre : forall `{!VSTGS unit Σ, lockGS Σ} x args,
    Jext_spec_pre (concurrent_ext_spec CS ext_link) FREE_LOCK x (genv_symb_injective ge) (sig_args (ef_sig FREE_LOCK)) args ⊣⊢
      match freelock_spec CS with mk_funspec _ _ A _ P _ => ∃ x'', ⌜JMeq.JMeq x x''⌝ ∧ funspec2pre' A P x'' (genv_symb_injective ge) (sig_args (ef_sig FREE_LOCK)) args end.
  Proof.
    solve_spec x.
  Qed.

  Lemma CEspec_freelock_post : forall `{!VSTGS unit Σ, lockGS Σ} x args,
    Jext_spec_post (concurrent_ext_spec CS ext_link) FREE_LOCK x (genv_symb_injective ge) (sig_res (ef_sig FREE_LOCK)) args ⊣⊢
      match freelock_spec CS with mk_funspec _ _ A _ _ Q => ∃ x'', ⌜JMeq.JMeq x x''⌝ ∧ funspec2post' A Q x'' (genv_symb_injective ge) (sig_res (ef_sig FREE_LOCK)) args end.
  Proof.
    solve_spec x.
  Qed.

  Lemma CEspec_spawn_pre : forall `{!VSTGS unit Σ, lockGS Σ} x args,
    Jext_spec_pre (concurrent_ext_spec CS ext_link) CREATE x (genv_symb_injective ge) (sig_args (ef_sig CREATE)) args ⊣⊢
      match spawn_spec with mk_funspec _ _ A _ P _ => ∃ x'', ⌜JMeq.JMeq x x''⌝ ∧ funspec2pre' A P x'' (genv_symb_injective ge) (sig_args (ef_sig CREATE)) args end.
  Proof.
    solve_spec x.
  Qed.

  Lemma CEspec_spawn_post : forall `{!VSTGS unit Σ, lockGS Σ} x args,
    Jext_spec_post (concurrent_ext_spec CS ext_link) CREATE x (genv_symb_injective ge) (sig_res (ef_sig CREATE)) args ⊣⊢
      match spawn_spec with mk_funspec _ _ A _ _ Q => ∃ x'', ⌜JMeq.JMeq x x''⌝ ∧ funspec2post' A Q x'' (genv_symb_injective ge) (sig_res (ef_sig CREATE)) args end.
  Proof.
    solve_spec x.
  Qed.
*)
*)

  Program Definition spr (HH : VSTGS unit Σ) (HL : lockGS Σ) :=
    semax_prog_rule (concurrent_ext_spec CS ext_link) V G prog
      (proj1_sig init_mem) 0 tt _ (all_safe HH HL) (proj2_sig init_mem).
  Next Obligation.
  Proof. intros; iIntros (??); done. Qed.

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

  Context `{!VSTGS unit Σ} `{!lockGS Σ}.

  Fixpoint do_events (le : list mem_event) (p : access_map) : access_map :=
    match le with
    | [] => p
    | Read _ _ _ :: rest | Write _ _ _ :: rest => do_events rest p
    | Alloc b lo hi :: rest => do_events rest (do_alloc b lo hi p)
    | Free fl -> do_events rest (do_free fl p)
    end.

  Program Definition jsafe_perm_pre
    (jsafe : coPset -d> unit -d> CC_core -d> access_map -d> iPropO Σ) :
    coPset -d> unit -d> CC_core -d> access_map -d> iPropO Σ := λ E z c p,
      |={E}=> ∀ m (Hp : permMapLt p (getMaxPerm m)), state_interp m z -∗
        (∃ i, ⌜halted (cl_core_sem ge) c i⌝ ∧ state_interp m z ∗ Jext_spec_exit (concurrent_ext_spec CS ext_link) (Some (Vint i))) ∨
        (|={E}=> ∃ es c' m', ⌜ev_step (Clight_evsem.CLC_evsem ge) c m es c' m'⌝ ∧ state_interp m' z ∗ ▷ jsafe E z c' (do_events p e)) ∨
        (∃ e args x, ⌜at_external (cl_core_sem ge) c m = Some (e, args)⌝ ∧ state_interp m z ∗ Jext_spec_pre (concurrent_ext_spec CS ext_link) e x (genv_symb_injective ge) (sig_args (ef_sig e)) args ∗
           ▷ (∀ ret m' z', ⌜Val.has_type_list args (sig_args (ef_sig e)) ∧ Builtins0.val_opt_has_rettype ret (sig_res (ef_sig e))⌝ →
            |={E}=> state_interp m' z' -∗ Jext_spec_post (concurrent_ext_spec CS ext_link) e x (genv_symb_injective ge) (sig_res (ef_sig e)) ret -∗
                ∃ c', ⌜after_external (cl_core_sem ge) ret c m' = Some c'⌝ ∧ state_interp m' z' ∗ ∃ p', jsafe E z' c' p')).

  Local Instance jsafe_perm_pre_contractive : Contractive (jsafe_perm_pre).
  Proof.
    rewrite /jsafe_perm_pre => n jsafe jsafe' Hsafe E z c [??].
    do 15 f_equiv.
    - try f_contractive; repeat f_equiv. apply Hsafe.
    - do 2 f_equiv. f_contractive; repeat f_equiv. apply Hsafe.
  Qed.

  Local Definition jsafe_perm_def : coPset -> unit -> CC_core -> _ -> iProp Σ := fixpoint (jsafe_perm_pre).
  Local Definition jsafe_perm_aux : seal (jsafe_perm_def). Proof. by eexists. Qed.
  Definition jsafe_perm := jsafe_perm_aux.(unseal).
  Local Lemma jsafe_perm_unseal : jsafe_perm = jsafe_perm_def.
  Proof. rewrite -jsafe_perm_aux.(seal_eq) //. Qed.

  Lemma jsafe_perm_unfold E z c p :
    jsafe_perm E z c p ⊣⊢ jsafe_perm_pre (jsafe_perm) E z c p.
  Proof.
    rewrite jsafe_perm_unseal.
    apply (fixpoint_unfold (jsafe_perm_pre)).
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
  
  Lemma jsafe_perm_equiv : forall E z c
                             (p1 p2 : access_map), mem_equiv.access_map_equiv p1 p2 -> 
     jsafe_perm E z c p1 ⊢ jsafe_perm E z c p2.
  Proof.
    intros.
    iLöb as "IH" forall (z c p1 p2 H).
    rewrite !jsafe_perm_unfold /jsafe_perm_pre.
    iIntros ">H !>" (? Hcur) "S".
    assert (Hlt: permMapLt p1 (getMaxPerm m)).
    { by rewrite H. }
    iDestruct ("H" $! _ Hlt with "S") as "[H | [H | H]]"; auto.
  Qed.
    
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

  (*
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
*)
  
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

  Lemma jsafe_jsafe_perm : forall E z c p,
    jsafe(genv_symb := genv_symb_injective) (cl_core_sem ge) (concurrent_ext_spec CS ext_link) ge E z c ⊢
    jsafe_perm E z c p.
  Proof.
    intros.
    iLöb as "IH" forall (z c p).
    rewrite jsafe_unfold jsafe_perm_unfold /jsafe_pre /jsafe_perm_pre.
    iIntros ">H !> %% S".
    iDestruct ("H" with "S") as "[H | [H | H]]".
    - by iLeft.
    - iRight; iLeft.
      iMod "H" as (??) "(% & (? & Hsafe))".
      iIntros "!>".
      iExists c', m'.
      iSplit; auto.
      iFrame.
      by iApply "IH".
    - iRight; iRight.
      iDestruct "H" as (????) "($ & $ & H)".
      iSplit; first done.
      iIntros "!>" (????).
      iMod ("H" with "[//]") as "H".
      iIntros "!> S Hpost"; iDestruct ("H" with "S Hpost") as (?) "($ & $ & Hsafe)".
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

  (*
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

  Definition thread_safe max (tp : dtp) i g :=threads_safe max (tp : dtp) (gs : gmap nat gname) :=
    [∗ list] i ∈ seq 0 (pos.n (OrdinalPool.num_threads tp)), ∃ g, ⌜gs !! i = Some g⌝ ∧ thread_safe max tp i g.
  *)

  Definition thread_safe (tp : dtp) i :=
    ∃ cnti : containsThread tp i,
      match getThreadC cnti with
      | Krun c | Kblocked c => jsafe_perm ⊤ tt c ((getThreadR cnti).1)
      | Kresume c v =>
          ∀ c',
            (* [v] is not used here. The problem is probably coming from
           the definition of JuicyMachine.resume_thread'. *)
            ⌜cl_after_external None c = Some c'⌝ →
            jsafe_perm ⊤ tt c' ((getThreadR cnti).1)
      | Kinit v1 v2 =>
          ∃ q_new,
    ⌜cl_initial_core ge v1 (v2 :: nil) = Some q_new⌝ ∧
      jsafe_perm ⊤ tt q_new ((getThreadR cnti).1)
  end%I.

  Definition threads_safe (tp : dtp) :=
    [∗ list] i ∈ seq 0 (pos.n (OrdinalPool.num_threads tp)), thread_safe tp i.

  Definition threads_wellformed (tp : dtp) :=
    forall i (cnti : containsThread(ThreadPool := OrdinalPool.OrdinalThreadPool) tp i),
    match getThreadC cnti with
    | Krun q => Logic.True
    | Kblocked q => cl_at_external q <> None
    | Kresume q v => cl_at_external q <> None /\ v = Vundef
    | Kinit _ _ => Logic.True
    end.

  Definition access_at_nonempty (m : mem) (loc : address) : Prop :=
    access_at m loc Cur = Some Nonempty /\
      access_at m loc Max = Some Nonempty.

  Definition access_at_1 (m : Mem.mem) (l : address) : forall k : perm_kind, option permission :=
    fun k =>
      let '(b, ofs) := l in
      (Mem.mem_access m) # b ofs k.

  Definition nonEmptyRangeCur (m : Mem.mem) (l: Values.block * Z) : Prop :=
    forall (i : Z), (0 <= i < Z.of_nat (size_chunk_nat Mptr))%Z ->
                    (Mem.mem_access m) # (l.1) (l.2 + i)%Z Cur = Some Nonempty.

  Definition locks_coherent (tp : dtp) (m : mem) (ls : gset address) :=
    forall l,
      (l ∈ ls ->
       lockRes tp l <> None /\
         ((Mem_load_unchecked Mptr m l.1 l.2 = (Vptrofs Ptrofs.zero) /\
            lockRes tp l = Some (empty_map, empty_map)) \/
            (Mem_load_unchecked Mptr m l.1 l.2 = (Vptrofs Ptrofs.one))) /\
         (forall i  (cnti : containsThread tp i)
            (Hp : permMapLt (getThreadR cnti).1 (getMaxPerm m)), nonEmptyRangeCur (restrPermMap Hp) l)).

  Lemma storebytes_contents_eq :
    forall m m' b ofs bytes b0,
      Mem.storebytes m b ofs bytes = Some m' ->
      (Mem.mem_contents m') # b0 =
        if peq b0 b
        then Mem.setN bytes ofs ((Mem.mem_contents m) # b)
        else (Mem.mem_contents m) # b0.
  Proof.
    intros m m' b ofs bytes b0 H.
    unfold Mem.storebytes in H.
    destruct (Mem.range_perm_dec m b ofs (ofs + length bytes) Cur Writable) as [RP|NRP];
      try discriminate.
    inversion H; subst m'; clear H.
    destruct (peq b0 b) as [->|Hbneq].
    - rewrite PMap.gss. reflexivity.
    - rewrite PMap.gso; auto.
  Qed.

Lemma no_overlap_to_sidecond_when_bytes_nonempty (n : nat) (l2 ofs : Z) (bytes : list memval):
  (n <> 0)%nat -> bytes <> nil ->
  (forall i , (0 <= i < Z.of_nat n)%Z -> ¬ (ofs <= l2 + i < ofs + Z.of_nat (length bytes))%Z) ->
  (l2 + Z.of_nat n <= ofs)%Z \/ (ofs + Z.of_nat (length bytes) <= l2)%Z.
Proof.
  intros Hn0 Hbytes Hno.
  set (nZ := Z.of_nat n).
  set (lenZ := Z.of_nat (length bytes)).
  destruct (Z.le_gt_cases ofs l2) as [Hofs_le_l2 | Hl2_lt_ofs].
  - (* ofs <= l2 *)
    destruct (Z.le_gt_cases (ofs + lenZ) l2) as [Hend_le_l2 | Hl2_lt_end].
    + right. lia.
    + (* contradiction with i = 0 *)
      exfalso.
      specialize (Hno 0%Z).
      apply Hno; try lia.
  - (* l2 < ofs *)
    destruct (Z.le_gt_cases (l2 + nZ) ofs) as [Hend_le_ofs | Hofs_lt_end].
    + by left.
    + (* contradiction with i = ofs - l2 *)
      exfalso.
      assert (Hn_pos : (0 < nZ)%Z). lia.
      set (i := (ofs - l2)%Z).
      specialize (Hno i).
      assert (Hi_range : (0 <= i < nZ)%Z).
      { subst i; split; [lia|]. lia. }
      specialize (Hno Hi_range).
      apply Hno.
      subst i.
      split; try lia.
      pose proof (nil_or_length_pos bytes).
      destruct H; try done; try lia.
Qed.

Lemma setPermBlock_sets_range
  (b : Values.block) (ofs : Z) (pmap0 : access_map) (n : nat) :
  forall i : Z,
    (0 <= i < Z.of_nat n)%Z ->
    (setPermBlock (Some Nonempty) b ofs pmap0 n) # b (ofs + i)%Z = Some Nonempty.
Proof.
  induction n as [|n IH]; intros i Hi.
  - simpl in Hi; lia.
  - simpl setPermBlock.
    unfold setPerm.
    rewrite Maps.PMap.gss.
    destruct (compcert.lib.Coqlib.zeq (ofs + Z.of_nat n) (ofs + i)) as [Heq|Hneq].
    + done.
    + simpl.
      apply IH. lia.
Qed.

Lemma free_preserves_cur_nonempty :
  forall m m1 b lo hi (l: address),
    Mem.free m b lo hi = Some m1 ->
    (Mem.mem_access m) # (l.1) l.2 Cur = Some Nonempty ->
    (Mem.mem_access m1) # (l.1) l.2 Cur = Some Nonempty.
Proof.
  intros m m1 b lo hi l Hfree Hacc.
  destruct (peq (l.1) b) as [Hb|Hb].
  - subst.
    assert (Houtside : (l.2 < lo)%Z \/ (hi <= l.2)%Z).
    { destruct (zlt l.2 lo) as [Hlt|Hge]; [left; exact Hlt|].
      destruct (zle hi l.2) as [Hle|Hlt]; [right; exact Hle|].
      exfalso.
      pose proof (Mem.free_range_perm _ _ _ _ _ Hfree) as Hrp.
      specialize (Hrp l.2).
      assert (Hlohi : (lo <= l.2 < hi)%Z) by lia.
      apply Hrp in Hlohi.
      unfold Mem.perm in Hlohi.
      rewrite Hacc in Hlohi. inv Hlohi.
    }
    rewrite (Mem.free_result _ _ _ _ _ Hfree).
    unfold Mem.unchecked_free; simpl.
    rewrite PMap.gss.
    destruct Houtside as [Hlt | Hge].
    + destruct (zle lo l.2) eqn:Hzle; simpl; auto.
      exfalso. lia.
    + destruct (zle lo l.2) eqn:Hzle; simpl; auto.
      destruct (zlt l.2 hi) eqn:Hzlt; simpl; auto.
      lia.
  - rewrite (Mem.free_result _ _ _ _ _ Hfree).
    unfold Mem.unchecked_free; simpl.
    rewrite PMap.gso; auto.
Qed.

Lemma free_list_preserves_cur_nonempty_outside :
  forall m l m' l0 i,
    Mem.free_list m l = Some m' ->
    (Mem.mem_access m) # (l0.1) (l0.2 + i)%Z Cur = Some Nonempty ->
    (Mem.mem_access m') # (l0.1) (l0.2 + i)%Z Cur = Some Nonempty.
Proof.
  intros m l.
  revert m.
  induction l as [| [(b & lo) hi] tl IH]; intros; simpl in H.
  - inv H; try done.
  - destruct (Mem.free m b lo hi) as [m1|] eqn:Hfree; try discriminate.
    eapply IH; try done.
    eapply (free_preserves_cur_nonempty m m1 b lo hi (l0.1, (l0.2 + i)%Z)); try done.
Qed.

Lemma mem_step_preserves_nonempty_range :
  forall m m',
    mem_step m m' ->
    forall l : address,
      (forall i : Z,
          (0 <= i < size_chunk_nat Mptr)%Z ->
          (Mem.mem_access m) # (l.1) (l.2 + i)%Z Cur = Some Nonempty) ->
      forall i : Z,
        (0 <= i < size_chunk_nat Mptr)%Z ->
        (Mem.mem_access m') # (l.1) (l.2 + i)%Z Cur = Some Nonempty.
Proof.
  intros m m' Hstep.
  induction Hstep; intros.
  4 : {
    eapply IHHstep2; try done.
    intros.
    eapply IHHstep1; try done.
  }
  - erewrite Mem.storebytes_access; eauto.
  - assert (Hlneq : l.1 <> b').
    { apply Mem.alloc_result in H.
      subst.
      apply H0 in H1.
      intros Hcontra.
      assert (Hperm : Mem.perm m l.1 (l.2 + i) Cur Nonempty).
      { unfold Mem.perm, Mem.perm_order'.
        rewrite H1. apply perm_refl. }
      assert (Hvb : Mem.valid_block m l.1).
      { eapply Mem.perm_valid_block; eauto. }
      unfold Mem.valid_block in Hvb.
      rewrite Hcontra in Hvb.
      unfold Plt in Hvb. lia.
    }
    inversion H; subst; simpl.
    rewrite PMap.gso; auto.
  - eapply free_list_preserves_cur_nonempty_outside; eauto.
Qed.

Lemma mem_step_preserves_lock_bytes :
    forall m m' (l : address),
      mem_step m m' ->
      nonEmptyRangeCur m l ->
      Mem.getN (size_chunk_nat Mptr) l.2 ((Mem.mem_contents m)  # (l.1))
      = Mem.getN (size_chunk_nat Mptr) l.2 ((Mem.mem_contents m') # (l.1)).
  Proof.
    intros m m' l Hstep HNone.
    revert l HNone.
    induction Hstep; intros.
    4 : {
      unfold nonEmptyRangeCur in *.
      specialize (IHHstep1 l HNone).
      assert (HNone'' : forall i : Z, (0 <= i < size_chunk_nat Mptr)%Z ->
                 (Mem.mem_access m'') # (l.1) (l.2 + i)%Z Cur = Some Nonempty).
      { by eapply mem_step_preserves_nonempty_range. }
      specialize (IHHstep2 l HNone'').
      by rewrite IHHstep1.
    }
    - set (n := size_chunk_nat Mptr).
      have Hcontents := storebytes_contents_eq _ _ _ _ _ _ H.
      destruct (peq (l.1) b) as [Heq|Hneq].
      + subst.
        rewrite Hcontents.
        if_tac; try done.
        unfold Mem.storebytes in H.
        destruct (Mem.range_perm_dec m l.1 ofs (ofs + length bytes) Cur Writable)
          as [Hrp | Hrp]; try discriminate.
        destruct (eq_dec bytes []).
        { subst; done. }
        have Hno_overlap : forall i, (0 <= i < Z.of_nat n)%Z ->
            ¬ (ofs <= l.2 + i < ofs + Z.of_nat (length bytes))%Z.
        { intros i Hi Hover.
          have HpermW : Mem.perm m l.1 (l.2 + i) Cur Writable.
          { eapply Hrp; lia. }
          have Hacc : (Mem.mem_access m) # (l.1) (l.2 + i)%Z Cur = Some Nonempty.
          { rewrite /nonEmptyRangeCur in HNone; apply HNone; lia. }
          unfold Mem.perm in HpermW.
          rewrite Hacc in HpermW.
          inv HpermW.
        }
        rewrite Mem.getN_setN_outside; try done.
        apply no_overlap_to_sidecond_when_bytes_nonempty; try done.
      + rewrite Hcontents.
        if_tac; try done.
    - set (n := size_chunk_nat Mptr).
      Transparent Mem.alloc.
      pose proof H as Hal.
      rewrite /Mem.alloc in H.
      injection H as Hxy.
      pose proof (f_equal Mem.mem_contents (eq_sym Hxy)) as Hcnt.
      simpl in Hcnt.
      unfold nonEmptyRangeCur in HNone.
      rewrite Hcnt.
      rewrite PMap.gso; auto.
      intro Hcontra.
      assert (Hperm : Mem.perm m l.1 l.2 Cur Nonempty).
      {
        unfold Mem.perm.
        specialize (HNone 0).
        replace (l.2 + 0%nat)%Z with l.2 in HNone; try lia.
        rewrite HNone; last first. done.
        unfold Mem.perm_order'.
        apply perm_refl. }
      apply Mem.perm_valid_block in Hperm.
      unfold Mem.valid_block in Hperm.
      subst.
      rewrite <- Hcontra in Hperm.
      unfold Plt in Hperm. lia.
    - set (n := size_chunk_nat Mptr).
      Transparent Mem.free_list.
      pose proof H as Hfl.
      apply free_list_contents in Hfl.
      by rewrite Hfl.
Qed.

  (* test *)
  Definition mem_access_Cur (m : Mem.mem) : access_map :=
    Maps.PMap.map (fun f => fun ofs => f ofs Cur) (Mem.mem_access m).

  
Lemma setPermBlock_eq_implies_mem_access_range_Cur
  (m : Mem.mem) (l: Values.block * Z) (pmap0 : access_map) (n : nat) :
  setPermBlock (Some Nonempty) l.1 l.2 pmap0 n = mem_access_Cur m ->
  forall (i : Z),
    (0 <= i < Z.of_nat n)%Z ->
    (Mem.mem_access m) # (l.1) ((l.2 + i)%Z) Cur = Some Nonempty.
Proof.
  intros.
  have Hcur :
    (mem_access_Cur m) # (l.1) (l.2 + i)%Z = Some Nonempty.
  {
    rewrite <- H.
    apply setPermBlock_sets_range; try done. }
  unfold mem_access_Cur in Hcur.
  by rewrite Maps.PMap.gmap in Hcur.
Qed.

Lemma can_store_at_getCurPerm_of_perm_order'1
  (m : Mem.mem) (b : Values.block) (ofs : Z) :
  Mem.perm_order' ((Mem.mem_access m) # b ofs Cur) Writable ->
  can_store_at (getCurPerm m) (b,ofs).
Proof.
  rewrite /Mem.perm_order' /can_store_at /getCurPerm /=.
  intros H.
  rewrite PMap.gmap.
  destruct ((Mem.mem_access m) # b ofs Cur); try done.
Qed.

Lemma Mem_unchecked_restrPermMap :
  forall (m: Mem.mem) (p: access_map) (Hlt : permMapLt p (getMaxPerm m)) l,
    Mem_load_unchecked Mptr (restrPermMap Hlt) l.1 l.2 =
      Mem_load_unchecked Mptr m l.1 l.2.
Proof.
  intros m p Hlt [b ofs].
  by unfold Mem_load_unchecked.
Qed.

Definition other_threads_safe tp (perms : gmap nat (gname * access_map)) i:=
  ∀ (Ψ : nat → nat → iPropI Σ),
    □ (∀ (k y : nat), ⌜seq 0 (pos.n (OrdinalPool.num_threads tp)) !! k = Some y⌝ →
                    ⌜k ≠ i⌝ →
                    (∃ g0 : gname, ⌜(fst <$> perms) !! y = Some g0⌝ ∧ thread_safe tp y g0)
                    -∗ Ψ k y) -∗
           Ψ i i -∗ [∗ list] k↦y ∈ seq 0 (pos.n (OrdinalPool.num_threads tp)), Ψ k y.
 
(*
 Definition other_threads_safe tp (* (gs : gmap nat gname) *) i :=
    ∀ Ψ, □ (∀ k j g, ⌜seq 0 (pos.n (OrdinalPool.num_threads tp)) !! k = Some j⌝ → ⌜k ≠ i⌝ →
        thread_safe tp j g -∗ Ψ k j) -∗
      Ψ i i -∗ [∗ list] k↦y ∈ seq 0 (pos.n (OrdinalPool.num_threads tp)), Ψ k y.
*)
  
  Definition post_safe `{Hconc : conc_VSTGS unit Σ} (g : gname) sig :=
    let HVST : VSTGS unit Σ := @thread_VSTGS unit Σ Hconc g in
    fun (x : Jext_spec_type (concurrent_ext_spec CS ext_link) LOCK) c args k =>
      (∀ (ret : option val) (m' : mem) z',
          ⌜Val.has_type_list args (sig_args (ef_sig LOCK)) ∧
            Builtins0.val_opt_has_rettype ret (sig_res sig)⌝ →
          |={⊤}=>
         thread_state_interp g m' z' -∗
          Jext_spec_post (concurrent_ext_spec CS ext_link) LOCK x
             (genv_symb_injective ge) (sig_res sig) ret -∗
           ∃ c' : CC_core,
           ⌜after_external (cl_core_sem ge) ret (Callstate c args k) m' = Some c'⌝ ∧
             thread_state_interp g m' z' ∗ jsafe_perm g ⊤ z' c' (getCurPerm m')).

  (*
  Definition post_safe `{Hconc : conc_VSTGS unit Σ} g sig x c args k : mpred :=
    let HVST : VSTGS unit Σ :=
      @thread_VSTGS unit Σ Hconc g in
    ∀ (ret : option val) (m' : mem) z',
      ⌜Val.has_type_list args (sig_args (ef_sig LOCK)) ∧
        Builtins0.val_opt_has_rettype ret (sig_res sig)⌝ →
      |={⊤}=> thread_state_interp g m' z' -∗ Jext_spec_post (concurrent_ext_spec CS ext_link) LOCK x (genv_symb_injective ge) (sig_res sig) ret -∗
      ∃ c' : CC_core,
    ⌜after_external (cl_core_sem ge) ret (Callstate c args k) m' = Some c'⌝ ∧
      thread_state_interp g m' z' ∗ jsafe_perm g ⊤ z' c' (getCurPerm m'). *)

  (* join_perm as a canonical deterministic choice
     join_perm chooses the stronger of the two permissions

     Because for acquire_delta, we need to construct one concrete new permission map.
     permjoin says: p and q can be joined into some r (it may allow several r)
     (permjoin allows: Readable, Writable, Freeable given p = Some Readable, q = Some Readable)
     But after acquiring a lock, computeMap needs one exact value to put in the map.
     So join_perm chooses one canonical result (Readable + Readable = Readable)
   *)

  
  Definition join_perm (p q : option permission) : option permission :=
    match p, q with
    | None, _ => q
    | _, None => p

    | Some Nonempty, Some Nonempty => Some Nonempty
    | Some Nonempty, Some Readable => Some Readable
    | Some Readable, Some Nonempty => Some Readable

    | Some Nonempty, Some Writable => Some Writable
    | Some Writable, Some Nonempty => Some Writable

    | Some Readable, Some Readable => Some Readable
    | Some Readable, Some Writable => Some Writable
    | Some Writable, Some Readable => Some Writable

    | _, _ => None
    end.

  Lemma join_perm_correct :
    forall p q, (exists r, permjoin_def.permjoin p q r) -> permjoin_def.permjoin p q (join_perm p q).
  Proof.
    intros p q H.
    destruct p as [[]|], q as [[]|]; simpl in *;
      try constructor;
      try solve [destruct H as [r Hr]; inversion Hr].
  Qed.

  (* acquiring a lock changes the thread permission map.
- Before acquire: q = current thread permission; p = lock permission
  (old thread permission q + lock permission p = new thread permission)
- After acquire, the thread should own: join p q at each valid memory location.
But computeMap does NOT take a full permission map directly (needs a delta_map)
- Some r = update this address to r
- None   = leave it unchanged

So acquire_delta p q maxp builds the update information needed by computeMap.
acquire_delta = describes what permission updates happen during acquire
computeMap    = applies those updates


If maxp allows this location:
    update permission to p + q
If maxp has None there:
    do not update
   *)
  
  Definition acquire_delta (p q maxp : access_map) : delta_map :=
    PTree.map
      (fun b f ofs =>
         match f ofs with
         | Some _ => Some (join_perm (p # b ofs) (q # b ofs))
         | None => None (* NOT create permissions outside the memory’s maximum permissions.*)
         end
      ) maxp.2.

  Lemma perm_union_permjoin :
    forall p q r, perm_union p q = Some r -> permjoin_def.permjoin p q r.
  Proof.
    intros p q r H.
    destruct p as [p |]; destruct q as [q |]; destruct r as [r |];
      simpl in H; try discriminate; inversion H; subst; try done; try constructor;
      destruct p, q; try done; inv H; constructor.
  Qed.

  Lemma acquire_delta_permMapJoin_new :
    forall p q maxp,
      (forall b ofs, (maxp.2 !! b)%maps = None -> p # b ofs = None) ->
      permMapLt p maxp ->
      permMapsDisjoint p q ->
      permMapJoin p q (computeMap q (acquire_delta p q maxp)).
  Proof.
    intros p q maxp Houtside Hlt Hdisj.
    unfold permMapJoin.
    intros b ofs.

    unfold acquire_delta, computeMap.
    rewrite /PMap.get /=.
    rewrite PTree.gcombine; auto.
    rewrite PTree.gmap.
    destruct ((maxp.2 !! b)%maps) as [fmax |] eqn:Hmaxb.
    - destruct (fmax ofs) as [mx |] eqn:Hmaxofs.
      + (* maxp has permission here, so acquire_delta updates to join_perm *)
        rewrite Hmaxb /=.
        destruct ((q.2 !! b)%maps) as [fq |] eqn:Hqb; simpl.
        * rewrite Hmaxofs /=.
          (* Hqb : (q.2 !! b)%maps = Some fq
             q permission comes from block-specific function fq *)
          apply join_perm_correct.
          rewrite /permMapsDisjoint in Hdisj.
          specialize (Hdisj b ofs).
          destruct Hdisj as (pu & Hdisj).
          exists pu.
          rewrite /PMap.get in Hdisj.
          rewrite Hqb in Hdisj.
          by apply perm_union_permjoin.
        * rewrite Hmaxofs.
          (* None case: q permission comes from default function q.1. *)
          apply join_perm_correct.
          specialize (Hdisj b ofs).
          destruct Hdisj as (pu & Hdisj).
          exists pu.
          rewrite /PMap.get in Hdisj.
          rewrite Hqb in Hdisj.
          by apply perm_union_permjoin.
      + (* maxp has no permission at this offset, so no update *)
        rewrite Hmaxb /=.
        assert (Hpnone : p # b ofs = None).
        { specialize (Hlt b ofs).
          unfold PMap.get in Hlt.
          rewrite Hmaxb Hmaxofs in Hlt.
          destruct (p # b ofs) eqn: E; auto.
          rewrite /PMap.get in E.
          rewrite E in Hlt.
          easy.
        }
        destruct ((q.2 !! b)%maps) as [fq |] eqn:Hqb; simpl.
        * rewrite Hmaxofs.
          rewrite /PMap.get in Hpnone.
          rewrite Hpnone.
          constructor.
        * rewrite Hmaxofs.
          rewrite /PMap.get in Hpnone.
          rewrite Hpnone. constructor.
    - (* maxp has no block b, so no update *)
      rewrite Hmaxb /=.
      assert (Hpnone : p # b ofs = None).
      { by apply Houtside. }
      rewrite /PMap.get in Hpnone.
      rewrite Hpnone.
      constructor.
  Qed.

  Lemma computeMap_acquire_delta_permMapLt :
    forall p q maxp, permMapLt p maxp -> permMapLt q maxp ->
      (forall b ofs, Mem.perm_order'' (maxp # b ofs) (join_perm (p # b ofs) (q # b ofs))) ->
      permMapLt (computeMap q (acquire_delta p q maxp)) maxp.
  Proof.
    intros p q maxp Hp Hq Hjoin b ofs.
    rewrite /computeMap /acquire_delta /PMap.get /=.
    rewrite PTree.gcombine; auto.
    rewrite PTree.gmap.
    destruct ((maxp.2 !! b)%maps) as [fmax |] eqn:Hmaxb.
    - destruct ((q.2 !! b)%maps) as [fq |] eqn:Hqb; simpl;
        destruct (fmax ofs) as [mx |] eqn:Hmaxofs; simpl.
      + (* max has permission; delta uses join_perm *)
        specialize (Hjoin b ofs).
        by rewrite /PMap.get Hmaxb /= Hmaxofs Hqb /= in Hjoin.
      + specialize (Hq b ofs).
        unfold PMap.get in Hq.
        by rewrite Hmaxb /= Hmaxofs Hqb in Hq.
      + specialize (Hjoin b ofs).
        by rewrite /PMap.get Hmaxb /= Hmaxofs Hqb /Mem.perm_order'' /= in Hjoin.
      + specialize (Hq b ofs).
        by rewrite /PMap.get Hmaxb /= Hmaxofs Hqb in Hq.
    - specialize (Hq b ofs).
      by rewrite /PMap.get Hmaxb /= in Hq.
  Qed.

  Lemma join_perm_below_max :
    forall p q maxp b ofs, permMapLt p maxp -> permMapLt q maxp -> permMapsDisjoint p q ->
      Mem.perm_order'' (maxp # b ofs) (join_perm (p # b ofs) (q # b ofs)).
  Proof.
    intros p q maxp b ofs Hp Hq Hdisj.
    specialize (Hp b ofs).
    specialize (Hq b ofs).
    specialize (Hdisj b ofs).
    destruct Hdisj as (pu & Hdisj).
    destruct (p # b ofs) as [pp |] eqn:Hpbo;
      destruct (q # b ofs) as [qq |] eqn:Hqbo;
      simpl in *; try done.
    - destruct pp, qq; try done.
    - destruct pp; try done.
  Qed.

  Lemma computeMap_acquire_delta_empty_get :
    forall q maxp b ofs, (computeMap q (acquire_delta empty_map q maxp)) # b ofs = q # b ofs.
  Proof.
    intros q maxp b ofs.
    unfold computeMap, acquire_delta.
    rewrite /PMap.get /=.
    rewrite PTree.gcombine; auto.
    rewrite PTree.gmap.
    destruct ((maxp.2 !! b)%maps) as [fmax |] eqn:Hmaxb;
      destruct ((q.2 !! b)%maps) as [fq |] eqn:Hqb; simpl; try done.
    - destruct (fmax ofs); simpl; reflexivity.
    - destruct (fmax ofs); simpl; reflexivity.
  Qed.

  Lemma permMapsDisjoint2_empty_l :
    forall rmap, permMapsDisjoint2 (empty_map, empty_map) rmap.
  Proof.
    intros rmap.
    rewrite /permMapsDisjoint2 /=.
    split; apply empty_disjoint'.
  Qed.

  Lemma permMapsDisjoint2_empty_r :
    forall rmap, permMapsDisjoint2 rmap (empty_map, empty_map).
  Proof.
    intros rmap.
    rewrite /permMapsDisjoint2 /=.
    split; apply permMapsDisjoint_comm; apply empty_disjoint'.
  Qed.

  Lemma join_perm_disjoint3 :
    forall a b c, (exists ab, perm_union a b = Some ab) ->
             (exists ac, perm_union a c = Some ac) ->
             (exists bc, perm_union b c = Some bc) ->
             exists u, perm_union (join_perm a b) c = Some u.
  Proof.
    intros a b c [ab Hab] [ac Hac] [bc Hbc].
    destruct a as [a|], b as [b|], c as [c|];
      simpl in *; try discriminate; eauto;
    try destruct a, b, c; simpl in *; try discriminate; eauto.
    destruct a, b; simpl in *; try discriminate; eexists; eauto.
    destruct a, c; simpl in *; try discriminate; eexists; eauto.
    destruct a; simpl in *; try discriminate; eexists; eauto.
  Qed.

  Lemma acquire_delta_preserves_disjoint3 :
    forall l p maxp x,
      permMapsDisjoint l p ->
      permMapsDisjoint l x ->
      permMapsDisjoint p x ->
      permMapsDisjoint (computeMap p (acquire_delta l p maxp)) x.
  Proof.
    intros l p maxp x Hlp Hlx Hpx b ofs.
    rewrite /acquire_delta /computeMap /PMap.get /=.
    rewrite PTree.gcombine; auto.
    rewrite PTree.gmap.
    specialize (Hlp b ofs) as [pu_lp Hlp].
    specialize (Hlx b ofs) as [pu_lx Hlx].
    specialize (Hpx b ofs) as [pu_px Hpx].
    rewrite /PMap.get in Hlp, Hlx, Hpx.
    destruct ((maxp.2 !! b)%maps) as [fmax|] eqn:Hmax.
    - destruct ((p.2 !! b)%maps) as [fp|] eqn:Hp; simpl.
      + destruct ((l.2 !! b)%maps) as [fl|] eqn:Hl; simpl.
        * (* updated case: new permission = join_perm l p *)
          destruct (fmax ofs) as [mx|] eqn:Hmax_ofs; simpl.
          ++ apply join_perm_disjoint3; eexists; done.
          ++ eexists; done.
        * (* lock permission l comes from its default function l.1 *)
          destruct (fmax ofs) as [mx |] eqn:Hmax_ofs; simpl.
          ++ apply join_perm_disjoint3; eexists; done.
          ++ eexists; done.
      + (* default permission function p.1 because Hp : (p.2 !! b)%maps = None *)
        destruct (fmax ofs) as [mx |] eqn:Hmax_ofs; simpl.
        * apply join_perm_disjoint3; eexists; eauto.
        * eexists; done.
    - (* no update because Hmax : (maxp.2 !! b)%maps = None *)
      simpl.
      eexists; done.
  Qed.

  Lemma join_perm_coh_right :
    forall a l p, perm_coh a l -> perm_coh a p -> perm_coh a (join_perm l p).
  Proof.
    intros a l p H1 H2.
    destruct a as [a|], l as [l|], p as [p|];
      simpl in *; try contradiction; auto;
      try destruct a, l, p; simpl in *; try contradiction; try done.
    - destruct a, l; try done.
    - destruct l, p; try done.
    - destruct l; try done.
  Qed.

  Lemma join_perm_coh_left :
    forall l p x, perm_coh l x -> perm_coh p x -> perm_coh (join_perm l p) x.
  Proof.
    intros l p x H1 H2.
    destruct l as [l|], p as [p|], x as [x|];
      simpl in *; try contradiction; auto;
      try destruct l, p, x; simpl in *; try contradiction; auto.
    - destruct l, p; try done.
    - destruct l, x; try done.
    - destruct l; try done.
  Qed.

  Lemma acquire_delta_preserves_coherence_right :
    forall a l p maxp, permMapCoherence a l -> permMapCoherence a p ->
      permMapCoherence a (computeMap p (acquire_delta l p maxp)).
  Proof.
    intros a l p maxp Hal Hap.
    unfold permMapCoherence in *.
    intros b ofs.
    specialize (Hal b ofs).
    specialize (Hap b ofs).
    unfold computeMap, acquire_delta.
    rewrite /PMap.get /=.
    rewrite PTree.gcombine; auto.
    rewrite PTree.gmap.
    destruct ((maxp.2 !! b)%maps) as [fmax|] eqn:Hmax;
      destruct ((p.2 !! b)%maps) as [fp|] eqn:Hp;
      destruct ((l.2 !! b)%maps) as [fl|] eqn:Hl;
      simpl in *;
      unfold PMap.get in Hal, Hap;
      rewrite Hl in Hal;
      rewrite Hp in Hap;
      simpl in Hal, Hap;
      try (
          destruct (fmax ofs) as [mx|]; simpl;
          [ eapply join_perm_coh_right; eauto
          | exact Hap ]
        ); exact Hap.
  Qed.

  Lemma acquire_delta_preserves_coherence_left :
    forall l p x maxp, permMapCoherence l x -> permMapCoherence p x ->
      permMapCoherence (computeMap p (acquire_delta l p maxp)) x.
  Proof.
    intros l p x maxp Hlx Hpx.
    unfold permMapCoherence in *.
    intros b ofs.
    specialize (Hlx b ofs).
    specialize (Hpx b ofs).
    unfold computeMap, acquire_delta.
    rewrite /PMap.get /=.
    rewrite PTree.gcombine; auto.
    rewrite PTree.gmap.
    destruct ((maxp.2 !! b)%maps) as [fmax|] eqn:Hmax;
      destruct ((p.2 !! b)%maps) as [fp|] eqn:Hp;
      destruct ((l.2 !! b)%maps) as [fl|] eqn:Hl;
      simpl in *;
      unfold PMap.get in Hlx, Hpx;
      rewrite Hl in Hlx;
      rewrite Hp in Hpx;
      simpl in Hlx, Hpx;
      try (
          destruct (fmax ofs) as [mx|]; simpl;
          [ eapply join_perm_coh_left; eauto
          | exact Hpx ]
        ); exact Hpx.
  Qed.

  Lemma permMapCoherence_writable_bound_r :
    forall p q, permMapCoherence p q ->
      forall b ofs, Mem.perm_order'' (Some Writable) (q # b ofs).
  Proof.
    intros p q Hcoh b ofs.
    specialize (Hcoh b ofs).
    unfold perm_coh in Hcoh.
    destruct (p # b ofs) as [pp|];
      destruct (q # b ofs) as [qq|];
      simpl in *; try contradiction; auto;
      try destruct pp, qq; simpl in *; try contradiction; auto.
    - constructor.
    - constructor.
    - constructor.
    - destruct qq; try done; try constructor.
  Qed.

  Lemma updLockSet_lr_valid_existing
    (tp : OrdinalPool.t) addr
    (old new : lock_info) :
    OrdinalPool.lr_valid (OrdinalPool.lockRes tp) ->
    OrdinalPool.lockRes tp addr = Some old ->
    OrdinalPool.lr_valid
      (OrdinalPool.lockRes (OrdinalPool.updLockSet tp addr new)).
  Proof.
    intros Hvalid Hold.
    unfold OrdinalPool.lr_valid in *.
    intros b ofs.
    destruct (eq_dec (b, ofs) addr) as [Heq | Hneq].
    - subst addr.
      rewrite OrdinalPool.gssLockRes.
      intros ofs0 Hrange.
      rewrite OrdinalPool.gsoLockRes.
      + specialize (Hvalid b ofs).
        rewrite Hold in Hvalid.
        exact (Hvalid ofs0 Hrange).
      + intro Hsame.
        inversion Hsame; subst.
        lia.
    - rewrite OrdinalPool.gsoLockRes; auto.
      destruct (OrdinalPool.lockRes tp (b, ofs)) as [r|] eqn:Hcur; auto.
      intros ofs0 Hrange.
      destruct (eq_dec (b, ofs0) addr) as [Heq0 | Hneq0].
      + exfalso.
        specialize (Hvalid b ofs).
        rewrite Hcur in Hvalid.
        specialize (Hvalid ofs0 Hrange).
        rewrite <- Heq0 in Hold.
        rewrite Hold in Hvalid.
        discriminate.
      + rewrite OrdinalPool.gsoLockRes; auto.
        specialize (Hvalid b ofs).
        rewrite Hcur in Hvalid.
        exact (Hvalid ofs0 Hrange).
  Qed.
  
  Lemma invariant_acquire_lock :
    forall (tp : dtp) i (cnti : containsThread tp i) c addr l0 maxp,
      invariant tp -> lockRes tp addr = Some l0 ->
      invariant (updLockSet (updThread cnti c
          (computeMap (getThreadR cnti).1 (acquire_delta l0.1 (getThreadR cnti).1 maxp),
           computeMap (getThreadR cnti).2 (acquire_delta l0.2 (getThreadR cnti).2 maxp)))
           addr (empty_map, empty_map)).
  Proof.
    intros tp i cnti c addr l0 lmaxp Hinvariant Hlock.
    set (r1 := computeMap (getThreadR cnti).1 (acquire_delta l0.1 (getThreadR cnti).1 lmaxp)).
    set (r2 := computeMap (getThreadR cnti).2 (acquire_delta l0.2 (getThreadR cnti).2 lmaxp)).
    destruct Hinvariant.
    constructor.
    - intros.
      destruct (Nat.eq_dec i0 i) as [Hi0 | Hi0]; destruct (Nat.eq_dec j i) as [Hj | Hj].
      + subst. easy.
      + subst i0.
        assert (cntj_old : containsThread tp j).
        { eapply cntUpdateL'; eauto. }
        pose proof (cntUpdateL' _ _ cnti0) as cnti0_upd.
        pose proof (cntUpdateL' _ _ cntj) as cntj_upd.
        do 2 rewrite gLockSetRes.
        rewrite (gssThreadRes cnti c (r1, r2) cnti0_upd).
        rewrite gsoThreadRes; auto.
        split.
        * unfold r1.
          eapply acquire_delta_preserves_disjoint3.
          ** destruct (no_race0 i addr cnti l0 Hlock) as [Hi_l0 _].
             apply permMapsDisjoint_comm; auto.
          ** destruct (no_race0 j addr cntj_old l0 Hlock) as [Hj_l0 _].
             apply permMapsDisjoint_comm; auto.
          ** destruct (no_race_thr0 i j cnti cntj_old Hneq) as [Hij _]; auto.
        * unfold r2.
          eapply acquire_delta_preserves_disjoint3.
          ** destruct (no_race0 i addr cnti l0 Hlock) as [_ Hi_l0].
             apply permMapsDisjoint_comm; auto.
          ** destruct (no_race0 j addr cntj_old l0 Hlock) as [_ Hj_l0].
             apply permMapsDisjoint_comm; auto.
          ** destruct (no_race_thr0 i j cnti cntj_old Hneq) as [_ Hij]; auto.
      + subst.
        pose proof
          (cntUpdateL' (tp := updThread cnti c (r1, r2)) (j := i0)
             addr ((empty_map, empty_map) : lock_info) cnti0) as cnti0_upd.
        pose proof
          (cntUpdateL' (tp := updThread cnti c (r1, r2)) (j := i)
             addr ((empty_map, empty_map) : lock_info) cntj) as cntj_upd.
        rewrite gLockSetRes.
        rewrite gLockSetRes.
        pose proof (cntUpdate' _ _ _ cnti0_upd) as cnti0_old.
        rewrite gsoThreadRes.
        rewrite (gssThreadRes cnti c (r1, r2) _).
        split; apply permMapsDisjoint_comm; auto.
        * unfold r1.
          eapply acquire_delta_preserves_disjoint3.
          ** destruct (no_race0 i addr cnti l0 Hlock) as [Hi_l0 _].
             apply permMapsDisjoint_comm; auto.
          ** destruct (no_race0 i0 addr cnti0_old l0 Hlock) as [Hi0_l0 _].
             apply permMapsDisjoint_comm; auto.
          ** destruct (no_race_thr0 i i0 cnti cnti0_old) as [Hii0 _]; auto.
        * unfold r2.
          eapply acquire_delta_preserves_disjoint3.
          ** destruct (no_race0 i addr cnti l0 Hlock) as [_ Hi_l0].
             apply permMapsDisjoint_comm; auto.
          ** destruct (no_race0 i0 addr cnti0_old l0 Hlock) as [_ Hi0_l0].
             apply permMapsDisjoint_comm; auto.
          ** destruct (no_race_thr0 i i0 cnti cnti0_old) as [_ Hii0].
             ++ intro Heq. apply Hi0; auto.
             ++ auto.
        * auto.
      + pose proof
          (cntUpdateL' (tp := updThread cnti c (r1, r2)) (j := i0)
             addr ((empty_map, empty_map) : lock_info) cnti0) as cnti0_upd.
        pose proof
          (cntUpdateL' (tp := updThread cnti c (r1, r2)) (j := j)
             addr ((empty_map, empty_map) : lock_info) cntj) as cntj_upd.
        rewrite gLockSetRes.
        rewrite gLockSetRes.
        pose proof (cntUpdate' _ _ _ cnti0_upd) as cnti0_old.
        pose proof (cntUpdate' _ _ _ cntj_upd) as cntj_old.
        rewrite gsoThreadRes; auto.
        rewrite (gsoThreadRes cnti _ _ _ _ cntj_upd).
        apply (no_race_thr0 i0 j cnti0_old cntj_old Hneq); auto. done.
    - intros.
      destruct (eq_dec laddr1 addr) as [H1eq | H1neq];
        destruct (eq_dec laddr2 addr) as [H2eq | H2neq].
      + subst laddr2. easy.
      + subst laddr1.
        rewrite gssLockRes in Hres1.
        inv Hres1.
        apply permMapsDisjoint2_empty_l.
      + subst laddr2.
        rewrite gssLockRes in Hres2.
        inv Hres2.
        apply permMapsDisjoint2_empty_r.
      + rewrite gsoLockRes in Hres1; auto.
        rewrite gsoLockRes in Hres2; auto.
        rewrite gsoThreadLPool in Hres1.
        rewrite gsoThreadLPool in Hres2.
        apply (no_race_lr0 laddr1 laddr2 rmap1 rmap2); auto.
    - intros i0 laddr cnti0 rmap Hres.
      destruct (eq_dec laddr addr) as [Heq | Hneq_addr].
      + subst laddr.
        rewrite gssLockRes in Hres.
        inv Hres.
        split; apply permMapsDisjoint2_empty_r.
      + rewrite gsoLockRes in Hres; auto.
        rewrite gsoThreadLPool in Hres.
        pose proof
          (cntUpdateL' (tp := updThread cnti c (r1, r2)) (j := i0)
             addr ((empty_map, empty_map) : lock_info)
             cnti0) as cnti0_upd.
        rewrite (gLockSetRes addr _ cnti0_upd cnti0).
        destruct (Nat.eq_dec i0 i) as [Heq_i | Hneq_i].
        * subst i0.
          rewrite (gssThreadRes cnti c (r1, r2) cnti0_upd).
          split.
          ** unfold r1.
             eapply acquire_delta_preserves_disjoint3.
             ++ destruct (no_race0 i addr cnti l0 Hlock) as [Hi_l0 _].
                apply permMapsDisjoint_comm; exact Hi_l0.
             ++ destruct (no_race_lr0 addr laddr l0 rmap) as [Hdisj _]; auto.
             ++ destruct (no_race0 i laddr cnti rmap Hres) as [Hdisj _]; auto.
         ** unfold r2.
            eapply acquire_delta_preserves_disjoint3.
             ++ destruct (no_race0 i addr cnti l0 Hlock) as [_ Hi_l0].
                apply permMapsDisjoint_comm; auto.
             ++ destruct (no_race_lr0 addr laddr l0 rmap) as [_ Hdisj]; auto.
             ++ destruct (no_race0 i laddr cnti rmap Hres) as [_ Hdisj]; auto.
        * pose proof (cntUpdate' _ _ _ cnti0_upd) as cnti0_old.
          rewrite gsoThreadRes; auto.
          apply (no_race0 i0 laddr cnti0_old rmap Hres).
    - intros i0 cnti0.
      split.
      + intros j cntj.
        pose proof
          (cntUpdateL' (tp := updThread cnti c (r1, r2)) (j := i0)
             addr ((empty_map, empty_map) : lock_info) cnti0) as cnti0_upd.
        pose proof
          (cntUpdateL' (tp := updThread cnti c (r1, r2)) (j := j)
             addr ((empty_map, empty_map) : lock_info) cntj) as cntj_upd.
        rewrite (gLockSetRes addr _ cnti0_upd cnti0).
        rewrite (gLockSetRes addr _ cntj_upd cntj).
        destruct (Nat.eq_dec i0 i) as [Hi0 | Hi0];
          destruct (Nat.eq_dec j i) as [Hj | Hj].
        * subst.
          rewrite (gssThreadRes cnti c (r1, r2) cntj_upd).
          rewrite (gssThreadRes cnti c (r1, r2) cnti0_upd).
          unfold r2.
          eapply acquire_delta_preserves_coherence_right.
          ** unfold r1.
             eapply acquire_delta_preserves_coherence_left.
             ++ destruct (locks_data_lock_coh0 addr l0 Hlock) as [_ Hlocks].
                apply (Hlocks addr l0 Hlock).
             ++ destruct (locks_data_lock_coh0 addr l0 Hlock) as [Hthreads _].
                apply (Hthreads i cnti).
         ** unfold r1.
            eapply acquire_delta_preserves_coherence_left.
            ++ destruct (thread_data_lock_coh0 i cnti) as [_ Hlock_thread].
               apply (Hlock_thread addr l0 Hlock).
            ++ destruct (thread_data_lock_coh0 i cnti) as [Hthreads _].
               apply (Hthreads i cnti).
        * subst i0.
          rewrite (gssThreadRes cnti c (r1, r2) cnti0_upd).
          pose proof (cntUpdate' _ _ _ cntj_upd) as cntj_old.
          rewrite gsoThreadRes; auto.
          unfold r2.
          eapply acquire_delta_preserves_coherence_right.
          ** destruct (locks_data_lock_coh0 addr l0 Hlock) as [Hlocks _].
             apply (Hlocks j cntj_old).
          ** destruct (thread_data_lock_coh0 i cnti) as [Hthreads _].
             apply (Hthreads j cntj_old).
        * subst j.
          rewrite gssThreadRes.
          pose proof (cntUpdate' _ _ _ cnti0_upd) as cnti0_old.
          rewrite gsoThreadRes; auto.
          unfold r1.
          eapply acquire_delta_preserves_coherence_left.
          ** destruct (thread_data_lock_coh0 i0 cnti0_old) as [_ Hlocks].
             apply (Hlocks addr l0 Hlock).
          ** destruct (thread_data_lock_coh0 i0 cnti0_old) as [Hthreads _].
             apply (Hthreads i cnti).
        * pose proof (cntUpdate' _ _ _ cnti0_upd) as cnti0_old.
          pose proof (cntUpdate' _ _ _ cntj_upd) as cntj_old.
          rewrite gsoThreadRes; auto.
          rewrite gsoThreadRes; auto.
          apply thread_data_lock_coh0.
      + intros.
        destruct (eq_dec laddr addr) as [Heq_addr | Hneq_addr].
        * subst laddr.
          rewrite gssLockRes in H.
          inv H.
          eapply permCoh_empty.
          intros b0 ofs0.
          eapply (permMapCoherence_writable_bound_r (getThreadR cnti0).1).
          pose proof
            (cntUpdateL' (tp := updThread cnti c (r1, r2)) (j := i0) addr
               ((empty_map, empty_map) : lock_info) cnti0) as cnti0_upd.
          rewrite (gLockSetRes addr _ cnti0_upd cnti0).
          destruct (Nat.eq_dec i0 i) as [Hi0 | Hi0].
          ** subst i0.
             rewrite (gssThreadRes cnti c (r1, r2) cnti0_upd).
             unfold r2.
             eapply acquire_delta_preserves_coherence_right.
             ++ unfold r1.
                eapply acquire_delta_preserves_coherence_left.
                -- destruct (locks_data_lock_coh0 addr l0 Hlock) as [_ Hlocks].
                   apply (Hlocks addr l0 Hlock).
                -- destruct (locks_data_lock_coh0 addr l0 Hlock) as [Hthreads _].
                   apply (Hthreads i cnti).
            ++ unfold r1.
               eapply acquire_delta_preserves_coherence_left.
               -- destruct (thread_data_lock_coh0 i cnti) as [_ Hlock_thread].
                  apply (Hlock_thread addr l0 Hlock).
               -- destruct (thread_data_lock_coh0 i cnti) as [Hthreads _].
                  apply (Hthreads i cnti).
        ** pose proof (cntUpdate' _ _ _ cnti0_upd) as cnti0_old.
           rewrite gsoThreadRes; auto.
           destruct (thread_data_lock_coh0 i0 cnti0_old) as [Hthreads _].
           apply (Hthreads i0 cnti0_old).
     * rewrite gsoLockRes in H; auto.
       rewrite gsoThreadLPool in H.
       pose proof
         (cntUpdateL' (tp := updThread cnti c (r1, r2)) (j := i0)
            addr ((empty_map, empty_map) : lock_info) cnti0) as cnti0_upd.
       rewrite gLockSetRes.
       destruct (Nat.eq_dec i0 i) as [Hi0 | Hi0].
       ** subst i0.
          rewrite (gssThreadRes cnti c (r1, r2) cnti0_upd).
          unfold r2.
          eapply acquire_delta_preserves_coherence_right.
          ++ destruct (locks_data_lock_coh0 addr l0 Hlock) as [_ Hlocks].
             apply (Hlocks laddr rmap H).
          ++ destruct (thread_data_lock_coh0 i cnti) as [_ Hthread_locks].
             apply (Hthread_locks laddr rmap H).
      ** pose proof (cntUpdate' _ _ _ cnti0_upd) as cnti0_old.
         rewrite gsoThreadRes; auto.
         destruct (thread_data_lock_coh0 i0 cnti0_old) as [_ Hthread_locks].
         apply (Hthread_locks laddr rmap H).
   - intros.
     split.
     + intros.
       destruct (eq_dec laddr addr) as [Heq_addr | Hneq_addr].
       * subst laddr.
         rewrite gssLockRes in Hres.
         inv Hres.
         apply permCoh_empty'.
       * rewrite gsoLockRes in Hres; auto.
         rewrite gsoThreadLPool in Hres.
         pose proof
           (cntUpdateL' (tp := updThread cnti c (r1, r2)) (j := j)
              addr ((empty_map, empty_map) : lock_info) cntj) as cntj_upd.
         rewrite gLockSetRes.
         destruct (Nat.eq_dec j i) as [Hj | Hj].
         ** subst j.
            rewrite gssThreadRes.
            unfold r1.
            eapply acquire_delta_preserves_coherence_left.
            ++ destruct (locks_data_lock_coh0 laddr rmap Hres) as [_ Hlocks].
               apply (Hlocks addr l0 Hlock).
            ++ destruct (locks_data_lock_coh0 laddr rmap Hres) as [Hthreads _].
               apply (Hthreads i cnti).
         ** pose proof (cntUpdate' _ _ _ cntj_upd) as cntj_old.
            rewrite gsoThreadRes; auto.
            destruct (locks_data_lock_coh0 laddr rmap Hres) as [Hthreads _].
            apply (Hthreads j cntj_old).
      + intros.
        destruct (eq_dec laddr addr) as [Heq | Hneq].
        * subst laddr.
          rewrite gssLockRes in Hres.
          inv Hres.
          apply permCoh_empty'.
        * rewrite gsoLockRes in Hres; auto.
          rewrite gsoThreadLPool in Hres.
          destruct (eq_dec laddr' addr) as [Heq' | Hneq'].
          ** subst laddr'.
             rewrite gssLockRes in H.
             inv H.
             eapply permCoh_empty.
             intros.
             destruct (locks_data_lock_coh0 laddr rmap Hres) as [_ Hlocks].
             eapply permMapCoherence_writable_bound_r; eauto.
          ** rewrite gsoLockRes in H; auto.
             rewrite gsoThreadLPool in H.
             destruct (locks_data_lock_coh0 laddr rmap Hres) as [_ Hlocks].
             apply (Hlocks laddr' rmap' H).
   - eapply updLockSet_lr_valid_existing; try done.
     Unshelve. done. done.
  Qed.

  Lemma threads_wellformed_acquire_lock :
  forall (tp : dtp) i (cnti : containsThread tp i) q addr l0 maxp,
    threads_wellformed tp -> getThreadC cnti = Kblocked q -> lockRes tp addr = Some l0 ->
    threads_wellformed
      (updLockSet
         (updThread cnti (Kresume q Vundef)
            (computeMap (getThreadR cnti).1
               (acquire_delta l0.1 (getThreadR cnti).1 maxp),
             computeMap (getThreadR cnti).2
               (acquire_delta l0.2 (getThreadR cnti).2 maxp)))
         addr (empty_map, empty_map)).
 Proof.
   intros tp i cnti c addr l0 lmaxp Hwf Hcode Hlock.
   unfold threads_wellformed in *.
   intros.
   rewrite gLockSetCode.
   destruct (Nat.eq_dec i0 i) as [Heq | Hneq].
   - (* updated thread: its new code is Kresume q Vundef *)
     subst i0.
     rewrite gssThreadCode.
     split; auto.
     specialize (Hwf i cnti).
     rewrite Hcode in Hwf; auto.
   - (* other threads: code is unchanged *)
     rewrite gsoThreadCode; auto.
     apply Hwf.
 Qed.

 Lemma lock_inv_in_lock_state : forall `{Hconc : conc_VSTGS unit Σ} (g : gname),
   let HVST : VSTGS unit Σ := @thread_VSTGS unit Σ Hconc g in
     forall γl m ls sh l (R : mpred),
      lock_state γl m ls -∗ lock_inv sh l R -∗
        ⌜∃ l_addr, val2adr l l_addr ∧ l_addr ∈ ls⌝.
 Proof.
   intros.
   iIntros "Hstate Hlock".
   iDestruct "Hstate" as (I) "((%Hdom & %Hldisj) & Hauth & _)".
   iDestruct "Hlock" as (l1) "(%Hval & _ & Hfrag)".
   iPoseProof (own_valid_2 (A := gmap_view.gmap_viewR address _) with "Hauth Hfrag")
     as "#Hvalid".
   iDestruct (algebra.gmap_view_both_validI with "[$Hvalid]") as "(%Hvalid & #Hlookup)".
   destruct (I !! l1) as [RI |] eqn:HI.
   - iPureIntro.
     exists l1; split; auto; rewrite -Hdom elem_of_dom; by eexists.
   - rewrite lookup_fmap HI. 
     iSimpl in "Hlookup".
     iDestruct (option_equivI with "Hlookup") as "[]".
 Qed.

 Ltac get_lk g n dq rsh Hvalid Hincl Hlk :=
   let Hseq := fresh "Hseq" in
   let Hlookup := fresh "Hlookup" in
   assert (Hseq : seq 0 (Z.to_nat LKSIZE) !! n = Some n) by
     (vm_compute; reflexivity);
   iDestruct (big_sepL_lookup_acc with "HLK") as "[HLKi Hclose]";
   first exact Hseq;
   iEval (change g with (gen_heap_name heapGS_gen_heapGS)) in "Hm";
   iPoseProof (mapsto_lookup with "Hm HLKi") as "%Hlookup";
   destruct Hlookup as (dq & rsh & Hvalid & Hincl & Hlk);
   iDestruct ("Hclose" with "HLKi") as "HLK".


Ltac norm_adr_add :=
  repeat match goal with
    | H : context[adr_add (?b, ?o) ?n] |- _ =>
        replace (adr_add (b, o) n) with (b, (o + Z.of_nat n)%Z) in H
          by (unfold adr_add; simpl; f_equal; lia)
    end.

Ltac solve_LK_VAL_contra :=
  norm_adr_add;
  match goal with
  | Hval : (resR_to_resource (?σ !! _)).2 = Some (VAL _) |- False =>
      erewrite resR_to_resource_eq in Hval; eauto;
      rewrite /= elem_of_to_agree in Hval;
      inversion Hval
  end.

 Lemma mem_auth_store_unchecked_lock_zero : forall `{Hconc : conc_VSTGS unit Σ} (g : gname),
    let HVST : VSTGS unit Σ := @thread_VSTGS unit Σ Hconc g in
    forall (m : mem) (sh : share) (b : Values.block) o v,
      mem_auth m -∗ LKspec LKSIZE sh (b, o) ==∗
      mem_auth (Mem_store_unchecked Mptr m b o v) ∗
      LKspec LKSIZE sh (b, o).
 Proof.
   intros; iIntros "(%σ & %Hcoh & Hm) HLK".
   iDestruct (resource_map.resource_map_auth_valid with "Hm") as %(_ & Hvalid).
   rewrite /LKspec /=.
   (* Mptr store changes 8 bytes
      -> coherent must be re-proved for all 8 bytes
      -> need LK facts for all 8 addresses
    *)
   get_lk g 0%nat dq0 rsh0 Hvalid0 Hincl0 Hlk0.
   get_lk g 1%nat dq1 rsh1 Hvalid1 Hincl1 Hlk1.
   get_lk g 2%nat dq2 rsh2 Hvalid2 Hincl2 Hlk2.
   get_lk g 3%nat dq3 rsh3 Hvalid3 Hincl3 Hlk3.
   get_lk g 4%nat dq4 rsh4 Hvalid4 Hincl4 Hlk4.
   get_lk g 5%nat dq5 rsh5 Hvalid5 Hincl5 Hlk5.
   get_lk g 6%nat dq6 rsh6 Hvalid6 Hincl6 Hlk6.
   get_lk g 7%nat dq7 rsh7 Hvalid7 Hincl7 Hlk7.
   iSplitL "Hm"; auto.
   rewrite /mem_auth.
   iExists σ.
   iFrame "Hm".
   iPureIntro; split; last done.
     (* the store changes only these bytes: (b,o)+0 ... (b,o)+7
        and LKspec says exactly those bytes are LK, not VAL.
        coherent requires concrete memory contents to match σ only for VAL locations.
        -> contradiction

       - outside range: memory unchanged, use old coherence
       - inside range: locations are LK, so no VAL-content obligation
     *)
   unfold coherent, resource_at in *.
   intro loc.
   destruct (Hcoh loc) as (Hnext & Hcontents & Haccess).
   split3; try done.
   unfold contents_cohere, contents_at in *.
   intros mv Hval.
   destruct (adr_range_dec (b, o) (size_chunk Mptr) loc) as [Hin | Hout].
   - (* loc is inside the stored range *)
     destruct loc as [bb ofs].
     destruct Hin as (Hb & Hlo & Hhi); simpl in *.
     subst bb.
     change (size_chunk Mptr) with 8%Z in Hhi.
     assert (ofs = o \/ ofs = o + 1 \/ ofs = o + 2 \/ ofs = o + 3 \/
               ofs = o + 4 \/ ofs = o + 5 \/ ofs = o + 6 \/ ofs = o + 7)%Z as Hor by lia.
     exfalso.
     repeat destruct Hor as [-> | Hor]; repeat solve_LK_VAL_contra.
     (* solve_LK_VAL_contra doesn't work well with adr_add (b, o) 0 and adr_add (b, o) 7  *)
     + replace (adr_add (b, o) 0%nat) with (b, o) in Hlk0; last first.
       { rewrite /adr_add //=; f_equal. lia. }
       erewrite resR_to_resource_eq in Hval; eauto.
       rewrite /= elem_of_to_agree in Hval.
       inversion Hval.
     + subst ofs.
       erewrite resR_to_resource_eq in Hval; eauto.
       rewrite /= elem_of_to_agree in Hval.
       inv Hval.
   - (* outside range: memory unchanged, use old coherence *)
     rewrite <- (Hcontents mv Hval).
     rewrite /juicy_mem.contents_at /Mem_store_unchecked /=.
     rewrite /Mem_store_unchecked_contents.
     destruct loc as (b' & ofs); simpl in *.
     destruct (Pos.eq_dec b' b) as [Hb | Hb].
     + subst b'.
       rewrite Maps.PMap.gss Mem.setN_other; auto.
       intros.
       intro Heq; subst r.
       apply Hout.
       split; auto.
       rewrite encode_val_length in H.
       by rewrite size_chunk_conv.
     + rewrite Maps.PMap.gso; auto.
 Qed.

 Lemma Mem_load_unchecked_store_unchecked_other:
   forall m b ofs b' ofs' v,
     b' <> b \/ (ofs' + size_chunk Mptr <= ofs \/ ofs + size_chunk Mptr <= ofs')%Z ->
     Mem_load_unchecked Mptr (Mem_store_unchecked Mptr m b ofs v) b' ofs' =
       Mem_load_unchecked Mptr m b' ofs'.
 Proof.
   intros.
   rewrite /Mem_load_unchecked /= /Mem_store_unchecked_contents.
   destruct (eq_dec b' b) as [Hb | Hb].
   - subst b'.
     rewrite PMap.gss.
     f_equal.
     rewrite Mem.getN_setN_outside; auto.
     rewrite encode_val_length -size_chunk_conv.
     destruct H; done.
   - by rewrite PMap.gso.
 Qed.

 Lemma Mem_load_unchecked_store_unchecked_lock_addresses_disjoint
   (m : mem) (ls : gset (Values.block * Z))
   (b b1 : Values.block) (o : ptrofs) (o1 : Z) :
   lock_addresses_disjoint ls ->
   (b1, o1) ∈ ls ->
   (b, Ptrofs.unsigned o) ∈ ls ->
   (b1, o1) <> (b, Ptrofs.unsigned o) ->
   Mem_load_unchecked Mptr (Mem_store_unchecked Mptr m b (Ptrofs.unsigned o) (Vptrofs Ptrofs.zero)) b1 o1 = Mem_load_unchecked Mptr m b1 o1.
  Proof.
    intros Hdisj Hin1 Hin2 Hneq.
    pose proof (Hdisj (b, Ptrofs.unsigned o) (b1, o1) Hin2 Hin1) as Hsep.
    assert ((b, Ptrofs.unsigned o) <> (b1, o1)) by congruence.
    specialize (Hsep H).
    simpl in Hsep.
    unfold Mem_load_unchecked, Mem_store_unchecked.
    destruct (Mem.store Mptr m b (Ptrofs.unsigned o) (Vptrofs Ptrofs.zero))
      as [m'|] eqn:Hstore; simpl; auto;
    eapply Mem_load_unchecked_store_unchecked_other; eauto.
  Qed.

  Lemma lock_inv_acquire :
    forall `{Hconc : conc_VSTGS unit Σ} (g : gname),
      let HVST : VSTGS unit Σ := @thread_VSTGS unit Σ Hconc g in
      forall γl m ls sh b o (R : mpred) (old : access_map),
        getCurPerm m = old ->
        Mem_load_unchecked Mptr m b (Ptrofs.unsigned o) = Vptrofs Ptrofs.one ->
        mem_auth m -∗ lock_state γl m ls -∗ lock_inv sh (Vptr b o) R ==∗
     let m' := Mem_store_unchecked Mptr m b (Ptrofs.unsigned o) (Vptrofs Ptrofs.zero) in
     ∃ p (Hp : permMapLt p (getMaxPerm m')),
     <affine>⌜∀ b0, (p.2 !! b0)%maps = None -> (old.2 !! b0)%maps = None⌝ ∗
     let m'' := restrPermMap Hp in
     juicy_mem.mem_auth m'' ∗ lock_state γl m'' ls ∗ lock_inv sh (Vptr b o) R ∗ ▷ R.
  Proof.
    Print lock_state.
    Print semax_conc_pred.lock_state .
    intros; rewrite /lock_state /lock_inv.
    iIntros "Hm (% & (%Hdom & %Hldisj) & HI & HRs) (% & % & Hl & Hi)".
    rewrite /val2adr in H1.
    rewrite H1.
    iDestruct (own_valid_2 with "HI Hi") as "#Heq".
    rewrite gmap_view_both_validI bi.and_elim_r lookup_fmap option_equivI.
    destruct (invariant_unfold <$> I !! (b, Ptrofs.unsigned o)) as [Q|] eqn: HI; simpl.
    2 : { by rewrite /invariant_unfold HI. }
    rewrite HI.
    rewrite later_equivI.
    apply fmap_Some in HI as (R0 & HIR0 & HQ).
    rewrite (big_sepM_delete _ _ (b, Ptrofs.unsigned o)); eauto.
    iDestruct "HRs" as "([HR | %Hload] & HRs)".
    - iDestruct "HR" as "(? & HR)".
      subst Q.
      simpl in *.
      simpl in *.
      set m' := Mem_store_unchecked
                  Mptr m b (Ptrofs.unsigned o) (Vptrofs Ptrofs.zero).
      set p := getCurPerm m'.
      assert (Hp : permMapLt p (getMaxPerm m')) by apply cur_lt_max.
      iExists p, Hp.
      assert (HNone: ∀ b0 : positive, (p.2 !! b0)%maps = None → (old.2 !! b0)%maps = None).
      { intros b0 Hnone.
        subst p.
        subst m'.
        simpl in Hnone.
        rewrite <- H.
        by unfold getCurPerm; simpl. }
     iAssert (▷ R)%I with "[Heq HR]" as "HR".
     { iNext; by iRewrite "Heq" in "HR". }
     iMod (mem_auth_store_unchecked_lock_zero with "Hm Hl") as "[Hm Hl]".
     rewrite restrPermMap_eq.
     rewrite /m'.
     iFrame.
     iModIntro.
     repeat iSplit; auto.
     set (lk := (b, Ptrofs.unsigned o)).
     rewrite -(insert_delete I lk R0); last exact HIR0.
     iApply big_sepM_insert; try apply lookup_delete.
     iSplitR.
     + iRight.
       subst lk.
       iPureIntro.
       rewrite /semax_conc_pred.Mem_load_unchecked /Mem_store_unchecked /=
         /Mem_store_unchecked_contents.
       by rewrite Maps.PMap.gss -(encode_val_length Mptr (Vptrofs Ptrofs.zero)) Mem.getN_setN_same.
     + rewrite delete_insert_delete delete_idemp.
       iApply (big_sepM_mono with "HRs").
       iIntros ((b1 & o1) y Hky) "Hk".
       rewrite lookup_delete_Some in Hky.
       destruct Hky as [Hlk_ne HkI].
       rewrite /lock_addresses_disjoint in Hldisj.
       assert (Hin: (b1, o1) ∈ ls /\ (b, Ptrofs.unsigned o) ∈ ls).
       { rewrite <- Hdom; split; eapply elem_of_dom_2; eauto. }
       destruct Hin as (Hin1 & Hin2).
       rewrite /lk in Hlk_ne.
       apply not_eq_sym in Hlk_ne.
       assert (semax_conc_pred.Mem_load_unchecked Mptr
                 (Mem_store_unchecked Mptr m b (Ptrofs.unsigned o) (Vptrofs Ptrofs.zero)) b1 o1 =
                 Mem_load_unchecked Mptr m b1 o1).
       { eapply Mem_load_unchecked_store_unchecked_lock_addresses_disjoint; eauto. }
       iDestruct "Hk" as "[[%Hload Hy] | %Hload]".
       ++ iLeft; iFrame; iPureIntro; by rewrite <- Hload.
       ++ iRight. iPureIntro. simpl in Hload.
          rewrite H2. done.
   - rewrite /semax_conc_pred.Mem_load_unchecked /Mem_load_unchecked in Hload, H0.
     by rewrite Hload in H0.
  Qed.
      
  
 (* It's vitally important that these lemmas use conc_VSTGS, not VSTGS, so that we're not assuming
   invariants belong to a specific thread. *)
  Lemma lock_inv_acquire1 : forall `{Hconc : conc_VSTGS unit Σ} (g : gname),
   let HVST : VSTGS unit Σ := @thread_VSTGS unit Σ Hconc g in
      forall γl m ls sh b o (R : mpred),
        Mem_load_unchecked Mptr m b (Ptrofs.unsigned o) = Vptrofs (Ptrofs.one) →
        mem_auth m -∗ lock_state γl m ls -∗ lock_inv sh (Vptr b o) R ==∗
   let m' := Mem_store_unchecked Mptr m b (Ptrofs.unsigned o) (Vptrofs (Ptrofs.zero)) in
      ∃ p (Hp : permMapLt p (getMaxPerm m')),
        let m'' := restrPermMap Hp in
        juicy_mem.mem_auth m'' ∗ lock_state γl m'' ls ∗ lock_inv sh (Vptr b o) R ∗ ▷ R.
  Proof.
   intros; rewrite /lock_state /lock_inv.
   iIntros "Hm (% & (%Hdom & %Hldisj) & HI & HRs) (% & % & Hl & Hi)".
   rewrite /val2adr in H0.
   rewrite H0.
   iDestruct (own_valid_2 with "HI Hi") as "#Heq".
   rewrite gmap_view_both_validI bi.and_elim_r lookup_fmap option_equivI.
   destruct (invariant_unfold <$> I !! (b, Ptrofs.unsigned o)) as [Q|] eqn: HI; simpl.
   2 : { by rewrite /invariant_unfold HI. }
   rewrite HI.
   rewrite later_equivI.
   apply fmap_Some in HI as (R0 & HIR0 & HQ).
   rewrite (big_sepM_delete _ _ (b, Ptrofs.unsigned o)); eauto.
   iDestruct "HRs" as "([HR | %Hload] & HRs)".
   - iDestruct "HR" as "(? & HR)".
     subst Q.
     simpl in *.
     set m' := Mem_store_unchecked
                 Mptr m b (Ptrofs.unsigned o) (Vptrofs Ptrofs.zero).
     set p := getCurPerm m'.
     assert (Hp : permMapLt p (getMaxPerm m')) by apply cur_lt_max.
     iExists p, Hp.
     iAssert (▷ R)%I with "[Heq HR]" as "HR".
     { iNext; by iRewrite "Heq" in "HR". }
     iMod (mem_auth_store_unchecked_lock_zero with "Hm Hl") as "[Hm Hl]".
     rewrite restrPermMap_eq.
     rewrite /m'.
     iFrame.
     iSplitL; auto.
     iModIntro.
     iSplit; auto.
     set (lk := (b, Ptrofs.unsigned o)).
     rewrite -(insert_delete I lk R0); last exact HIR0.
     iApply big_sepM_insert; try apply lookup_delete.
     iSplitR.
     + iRight.
       subst lk.
       iPureIntro.
       rewrite /semax_conc_pred.Mem_load_unchecked /Mem_store_unchecked /=
         /Mem_store_unchecked_contents.
       by rewrite Maps.PMap.gss -(encode_val_length Mptr (Vptrofs Ptrofs.zero)) Mem.getN_setN_same.
     + rewrite delete_insert_delete delete_idemp.
       iApply (big_sepM_mono with "HRs").
       iIntros ((b1 & o1) y Hky) "Hk".
       rewrite lookup_delete_Some in Hky.
       destruct Hky as [Hlk_ne HkI].
       rewrite /lock_addresses_disjoint in Hldisj.
       assert (Hin: (b1, o1) ∈ ls /\ (b, Ptrofs.unsigned o) ∈ ls).
       { rewrite <- Hdom; split; eapply elem_of_dom_2; eauto. }
       destruct Hin as (Hin1 & Hin2).
       rewrite /lk in Hlk_ne.
       apply not_eq_sym in Hlk_ne.
       assert (semax_conc_pred.Mem_load_unchecked Mptr
                 (Mem_store_unchecked Mptr m b (Ptrofs.unsigned o) (Vptrofs Ptrofs.zero)) b1 o1 =
                 Mem_load_unchecked Mptr m b1 o1).
       { eapply Mem_load_unchecked_store_unchecked_lock_addresses_disjoint; eauto. }
       iDestruct "Hk" as "[[%Hload Hy] | %Hload]".
       ++ iLeft; iFrame; iPureIntro; by rewrite <- Hload.
       ++ by iRight; iPureIntro; simpl in Hload |- *; rewrite H1.
   - rewrite /semax_conc_pred.Mem_load_unchecked /Mem_load_unchecked in Hload, H.
     by rewrite Hload in H.
  Qed.

 (*
 Lemma mem_auth_restrPermMap `{!VSTGS unit Σ, !conc_VSTGS unit Σ} m p
   (Hp : permMapLt p (getMaxPerm m)) :
   mem_auth (restrPermMap Hp) ⊣⊢ mem_auth m.
 Proof.
   rewrite /mem_auth /coherent.
   iSplit.
   - iDestruct 1 as (σ) "[%Hcoh Hauth]".
     iExists σ.
     iFrame.
     iPureIntro.
     split; auto.
     intros.
     specialize (Hcoh loc).
     split.
     + apply Hcoh.
     + Print coherent_loc.
       Print access_cohere.
       rewrite /coherent_loc /access_cohere in Hcoh |- *.
       Print Mem.perm_order''.
       Search Mem.perm_order'' access_at restrPermMap.
     eapply mem_coherent_equiv; [| exact Hcoh].
   Search coherent mem_equiv.mem_equiv.
   iSplit.
   - 
   rewrite restrPermMap_contents.
   done.
 Qed.
*)

 Lemma getMaxPerm_Mem_store_unchecked :
   forall chunk (m : mem) b ofs v,
     getMaxPerm (Mem_store_unchecked chunk m b ofs v) = getMaxPerm m.
 Proof.
   intros chunk m b ofs v.
   unfold Mem_store_unchecked.
   destruct (Mem.store chunk m b ofs v) as [m'|] eqn:Hstore; simpl.
   - pose proof (Mem.store_access _ _ _ _ _ _ Hstore) as Hacc.
     by unfold getMaxPerm.
   - reflexivity.
 Qed.

 Lemma restrPermMap_eq_same_p :
  forall (m1 m2 : mem) (p : access_map)
         (H1 : permMapLt p (getMaxPerm m1))
         (H2 : permMapLt p (getMaxPerm m2)),
    Mem.mem_contents m1 = Mem.mem_contents m2 ->
    Mem.nextblock m1 = Mem.nextblock m2 ->
    getMaxPerm m1 = getMaxPerm m2 ->
    restrPermMap H1 = restrPermMap H2.
Proof.
  intros m1 m2 p H1 H2 Hcontents Hnext Hmax.

  destruct m1 as [c1 [d1 t1] nb1 am1 nna1 cd1].
  destruct m2 as [c2 [d2 t2] nb2 am2 nna2 cd2].
  simpl in *.
  subst c2 nb2.

  unfold getMaxPerm in Hmax.
  simpl in Hmax.

  assert (Hacc :
    (fun ofs k =>
       match k with
       | Cur => None
       | Max => d1 ofs k
       end,
     PTree.map
       (fun b f ofs k =>
          match k with
          | Cur => PMap.get b p ofs
          | Max => f ofs Max
          end) t1)
    =
    (fun ofs k =>
       match k with
       | Cur => None
       | Max => d2 ofs k
       end,
     PTree.map
       (fun b f ofs k =>
          match k with
          | Cur => PMap.get b p ofs
          | Max => f ofs Max
          end) t2)).
  {
    f_equal.
    - apply functional_extensionality; intro ofs.
      apply functional_extensionality; intro k.
      destruct k; simpl.
      + exact (f_equal (fun q => fst q ofs) Hmax).
      + by pose proof (f_equal fst Hmax) as Hd.
    - apply PTree.extensionality; intro b.
      rewrite !PTree.gmap.
      pose proof (f_equal (fun q => PTree.get b (snd q)) Hmax) as Hb.
      simpl in Hb.
      rewrite !PTree.gmap1 in Hb.
      destruct (t1 !! b)%maps as [f1|] eqn:E1;
        destruct (t2 !! b)%maps as [f2|] eqn:E2;
        simpl in Hb; try discriminate; try reflexivity.
      inversion Hb as [Hf]; clear Hb.
      simpl.
      f_equal.
      apply functional_extensionality; intro ofs.
      apply functional_extensionality; intro k.
      destruct k; simpl; try done.
      exact (f_equal (fun h => h ofs) Hf).
  }
  unfold restrPermMap.
  eapply Mem.mkmem_ext; simpl; done.
Qed.

Definition delta_to (p pmax : access_map) : delta_map :=
  Maps.PTree.map
    (fun b pmax_b =>
     fun ofs =>
       match pmax_b ofs with
       | Some _ => Some (p # b ofs)
       | None => None
       end)
    pmax.2.

Lemma permMapLt_none :
  forall p maxp b ofs,
    permMapLt p maxp ->
    maxp # b ofs = None ->
    p # b ofs = None.
Proof.
  intros p maxp b ofs Hlt Hmax.
  specialize (Hlt b ofs).
  rewrite Hmax in Hlt.
  destruct (p # b ofs) eqn:Hp; auto.
  inversion Hlt.
Qed.

Lemma computeMap_delta_to_correct_pointwise :
  forall old target maxp b ofs,
    permMapLt old maxp ->
    permMapLt target maxp ->
    (forall ofs, maxp.1 ofs = None) ->
    (computeMap old (delta_to target maxp)) # b ofs =
      target # b ofs.
Proof.
  intros old target maxp b ofs Hold Htarget Hmax_default.
  destruct old as [old0 oldt].
  destruct target as [target0 targett].
  destruct maxp as [max0 maxt].
  simpl in *.

  unfold computeMap, delta_to.
  simpl.
  rewrite /PMap.get /=.
  rewrite PTree.gcombine; auto.
  rewrite PTree.gmap.
  destruct (maxt !! b)%maps as [maxrow |] eqn:Hmaxb.
  - simpl.
    destruct (oldt !! b)%maps as [oldrow |] eqn:Holdb; simpl;
      destruct (maxrow ofs) as [pm |] eqn:Hmaxofs; simpl.
    + auto.
    + assert (Hmax_none : (max0, maxt) # b ofs = None).
      { unfold PMap.get.
        by rewrite Hmaxb. }
      assert (Hold_none : oldrow ofs = None).
      { pose proof (permMapLt_none (old0, oldt) (max0, maxt)
                      b ofs Hold Hmax_none) as Hnone.
        simpl in Hnone.
        rewrite /PMap.get /= in Hnone.
        by rewrite Holdb in Hnone.
      }
      assert (Htarget_none : (target0, targett) # b ofs = None).
      { eapply permMapLt_none; eauto. }
      rewrite Hold_none.
      by rewrite /PMap.get /= in Htarget_none.
    + auto.
    + assert (Hmax_none : (max0, maxt) # b ofs = None).
      { rewrite /PMap.get /=.
        by rewrite Hmaxb.
      }
      assert (Hold_none : old0 ofs = None).
      { pose proof (permMapLt_none (old0, oldt) (max0, maxt)
                      b ofs Hold Hmax_none) as Hnone.
        rewrite /PMap.get /= in Hnone.
        by rewrite Holdb in Hnone.
      }

      assert (Htarget_none :
               (target0, targett) # b ofs = None).
      {
        eapply permMapLt_none; eauto.
      }

      rewrite Hold_none.
      by rewrite /PMap.get /= in Htarget_none.
  - simpl.
    assert (Hmax_none :
             (max0, maxt) # b ofs = None).
    { rewrite /PMap.get /=.
      by rewrite Hmaxb.
    }
    assert (Hold_none :
             (old0, oldt) # b ofs = None).
    {
      eapply permMapLt_none; eauto.
    }

    assert (Htarget_none :
             (target0, targett) # b ofs = None).
    {
      eapply permMapLt_none; eauto.
    }
    rewrite /PMap.get /= in Hold_none.
    rewrite Hold_none. done.
 Qed.

(*
delta_to_tree target converts an access_map into a delta_map by wrapping every permission in Some.
 *)
Definition delta_to_tree (target : access_map) : delta_map :=
  PTree.map
    (fun b target_row ofs =>
       Some (target_row ofs))
    target.2.

Lemma computeMap_delta_to_tree_exact :
  forall old target,
    isCanonical old ->
    isCanonical target ->
    (forall b : positive,
        PTree.get b target.2 = None ->
        PTree.get b old.2 = None) ->
    computeMap old (delta_to_tree target) = target.
Proof.
  intros old target Hcan_old Hcan_target Hsupport.
  destruct old as [old0 oldt].
  destruct target as [target0 targett].
  unfold isCanonical in *.
  simpl in *.
  unfold computeMap, delta_to_tree.
  simpl.
  f_equal.
  - rewrite Hcan_old.
    rewrite Hcan_target.
    reflexivity.
  - apply PTree.extensionality; intros b.
    rewrite PTree.gcombine; auto.
    rewrite PTree.gmap.
    destruct (PTree.get b targett) as [target_row |] eqn:Htargetb.
    + destruct (PTree.get b oldt) as [old_row |] eqn:Holdb; simpl;
        f_equal;
        apply functional_extensionality;
        intro ofs;
        reflexivity.
    + rewrite (Hsupport b Htargetb).
      simpl.
      reflexivity.
 Qed.
    

 
 (* these lemmas could be split off again into semax_acquire_safety, etc. *)
Lemma acquire_safe : forall `{(*!VSTGS unit Σ , *) Hconc : conc_VSTGS unit Σ } g,
   let HVST : VSTGS unit Σ :=
     @thread_VSTGS unit Σ Hconc g in
   forall γl tp m ls perms i
    (Htp_wf : threads_wellformed tp) (Hinvariant : invariant tp)
    (Hcompat : (*HybridMachineSig.*)mem_compatible tp m)
    (Hlocks : locks_coherent tp m ls) (Hperms : ∀ (i : nat) (r : access_map),
        snd <$> perms !! i = Some r ↔ ∃ cnti : containsThread tp i, (getThreadR cnti).1 = r)
    (cnti : containsThread tp i) argsty retty cc k args
    (Hi : getThreadC cnti = Kblocked (Callstate (Ctypes.External LOCK argsty retty cc) args k))
    (Hpi : perms !! (0 + i) = Some (g, (OrdinalPool.getThreadR cnti).1))
    (* (Hmax : permMapLt p (getMaxPerm m)) *)
    (Hp : permMapLt (OrdinalPool.getThreadR cnti).1 (getMaxPerm m))
    x 
   (*(Hpre : ext_spec_pre (concurrent_ext_spec CS ext_link) LOCK x (genv_symb_injective ge) (sig_args (ef_sig LOCK)) args () (restrPermMap Hp))*),
    ⊢ other_threads_safe (* (getMaxPerm m) *) tp perms i -∗
      Jext_spec_pre (concurrent_ext_spec CS ext_link) LOCK x (genv_symb_injective ge)
        (sig_args (ef_sig LOCK)) args -∗
      ▷ post_safe g (ef_sig LOCK) x (Ctypes.External LOCK argsty retty cc) args k -∗
      lock_state γl m ls -∗ thread_state_interp g (restrPermMap Hp) () -∗
      |={⊤}[∅]▷=> ∃ (tp' : t) (m' : mem) (ev : Events.sync_event) (perms' : gmap nat (gname * access_map)),
        ⌜threads_wellformed tp' ∧ invariant tp' ∧ mem_compatible tp' m' ∧ locks_coherent tp' m' ls ∧ syncStep true cnti Hcompat tp' m' ev /\
          (∀ (i0 : nat) (r : access_map),
              snd <$> perms' !! i0 = Some r
              ↔ ∃ cnti0 : OrdinalPool.containsThread tp' i0,
                 (OrdinalPool.getThreadR cnti0).1 = r)⌝ ∧
          threads_safe tp' (fst <$> perms')  ∗
            (conc_mem_auth m (delete i perms) -∗ conc_mem_auth m' (delete i perms')) ∗
            (∃ p (Hlt : permMapLt p (getMaxPerm m')),
                ⌜perms' !! i = Some (g, p)⌝ ∧ thread_state_interp g (restrPermMap Hlt) ()) ∗
  lock_state γl m' ls.
  Proof.
    intros; iIntros "Hsafe Hpre Hpost Hls (Hths & Hext)".
    rewrite /locks_coherent in Hlocks.
    rewrite CEspec_acquire_pre /=.
    iDestruct "Hpre" as (x' Heqx) "Hpre".
    destruct x' as ((l, sh), R); rewrite /funspec2pre' /=.
    set (c := Callstate (Ctypes.External LOCK argsty retty cc) args k).
    iDestruct "Hpre" as (Hty (Hsh & _) Hargs) "Hpre"; simpl in Hargs; subst.
    rewrite /SEPx /GLOBALSx /LOCALx; monPred.unseal.
    iDestruct "Hpre" as "(_ & Hl & _)".
    clear Hty.
    rewrite /post_safe /other_threads_safe.
    setoid_rewrite CEspec_acquire_post.
    iDestruct (lock_inv_in_lock_state with "Hls Hl") as "%Hin".
    destruct Hin as (l1 & Hval & Hl).
    specialize (Hlocks l1 Hl).
    destruct Hlocks as (HlockRes & ? & ?).
    destruct (lockRes tp l1) eqn: E; last done.
    (* If we have lock_inv sh l R, then lock_address l ∈ dom ls  *)
    (* We need to define lock_set to make that (lock_address l ∈ dom ls) true
     if we have lock_inv *)
    (* rewrite <- H1 in E. *)
    (* --------------- *)
    assert (l = Vptr l1.1 (Ptrofs.repr l1.2)) as Hl1.
    { destruct l; simpl in Hval; try contradiction.
      destruct l1 as [b1 ofs1].
      inv Hval.
      simpl.
      by rewrite Ptrofs.repr_unsigned.
    }
    assert (Hofs : Ptrofs.Z_mod_modulus l1.2 = l1.2).
    { unfold val2adr in Hval.
      destruct l; try discriminate.
      pose proof (f_equal snd Hval) as Hofs.
      subst. simpl.
      change (Ptrofs.Z_mod_modulus (Ptrofs.unsigned i0))
        with (Ptrofs.unsigned (Ptrofs.repr (Ptrofs.unsigned i0))).
      by rewrite Ptrofs.repr_unsigned.
    }
    assert (HlR: lockRes tp (l1.1, Ptrofs.intval (Ptrofs.repr l1.2)) = Some l0).
    { destruct l1; simpl; by rewrite Hofs. }
    
    destruct H as [[Ho Hl0_empty] | Ho].
    - (* acquire fails *)
      admit.
    - rewrite /thread_state_interp /thread_mem_auth Hl1.
      Print permMapJoin.
      iPoseProof (lock_inv_acquire _
                   γl (restrPermMap Hp) ls sh l1.1 (Ptrofs.repr l1.2) R
                                  with "[Hths] [Hls] [Hl]") as "Hauth"; auto.
      { rewrite /Mem_load_unchecked mem_contents_restrPermMap.
        rewrite /Mem_load_unchecked in Ho.
        rewrite Ptrofs.unsigned_repr; auto.
        pose proof (Ptrofs.Z_mod_modulus_range l1.2) as Hrange.
        rewrite Hofs in Hrange. unfold Ptrofs.max_unsigned in *.
        lia. }
      
      set m1 := Mem_store_unchecked Mptr (restrPermMap Hp) l1.1
                  (Ptrofs.unsigned (Ptrofs.repr l1.2))
                  (Vptrofs Ptrofs.zero).
      set m2 := Mem_store_unchecked Mptr m l1.1
                  (Ptrofs.unsigned (Ptrofs.repr l1.2))
                  (Vptrofs Ptrofs.zero).
      iMod "Hauth" as (p Hp0) "(%Hdom & Hm & Hls & Hl & HR)".
      assert (Hmax: getMaxPerm m1 = getMaxPerm m2).
      { subst m1 m2; rewrite !getMaxPerm_Mem_store_unchecked; by rewrite restr_Max_eq. }
      (* set (p' :=
             computeMap (getThreadR cnti).1
               (acquire_delta l0.1 (getThreadR cnti).1 (getMaxPerm m2),
                 acquire_delta l0.2 (getThreadR cnti).2 (getMaxPerm m2)).1). *)

      assert (Hlt : permMapLt p (getMaxPerm m2)).
      { rewrite <- Hmax; done. }

      
      iAssert (mem_auth (restrPermMap Hp0) ∗ lock_state γl (restrPermMap Hp0) ls -∗
             ∃ (* (p0 : access_map) (Hlt : permMapLt p0 (getMaxPerm m2)) *)
               (perms' : gmap nat (gname * access_map)), ⌜perms' = <[i := (g, p)]> perms⌝ ∧ mem_auth (restrPermMap Hlt) ∗
                  lock_state γl m2 ls)%I as "Hmem_auth".
      { iIntros "(Hmem & Hlock)".
        set (perms' := <[i := (g, p)]> perms).
        iExists (<[i := (g, p)]> perms).
        iSplit; try iPureIntro; subst perms'; try rewrite lookup_insert; auto.
        iFrame.
        erewrite restrPermMap_eq_same_p; eauto.
      }
      iDestruct ("Hmem_auth" with "[$Hm $Hls]") as (perms1 Hperms1) "(Hm & Hls)".
      iAssert ((∃ (p1 : access_map) (Hlt0 : permMapLt p1 (getMaxPerm m2)),
                   ⌜perms1 !! i = Some (g, p1)⌝ ∧ mem_auth (restrPermMap Hlt0) ∗ ext_auth ()) ∗
                 lock_state γl m2 ls) with "[Hm Hls Hext]" as  "(Hmem & Hls)".
      { iSplitR "Hls"; last first; try done.
        iExists _, _. iFrame.
        iPureIntro; split; auto.
        rewrite Hperms1. by rewrite lookup_insert. }
     iDestruct "Hmem" as (p' ?) "(% & Hmem)".
     assert (p' = p).
     {
       rewrite Hperms1 in H.
       rewrite lookup_insert in H.
       inversion H. auto. }
     subst p'.

      (*
        if perms' := <[i := (g, p)]> perms
        But the RHS depends on tp': getThreadR cnti0
        So must prove p = (OrdinalPool.getThreadR cnti').1 for the updated thread i.
       *)

     Print conc_mem_auth.
     

    set (vt1 := delta_to_tree p).
    set (vt2 := acquire_delta l0.2 (getThreadR cnti).2 (getMaxPerm m)).
    set (virtueThread := (vt1, vt2)).
    set (tp' :=
           updLockSet
             (updThread cnti
                (Kresume (Callstate (Ctypes.External LOCK argsty retty cc) [l] k) Vundef)
                (p, computeMap (getThreadR cnti).2 vt2))
             (l1.1, Ptrofs.intval (Ptrofs.repr l1.2))
             (empty_map, empty_map)).
    assert (exists m' ev,
               syncStep true cnti Hcompat tp' m' ev /\ threads_wellformed tp' /\
                 invariant tp' /\ mem_compatible tp' m') as Hstep.
    {
      (* acquire succeeds *)
      eexists _, _.
        split.
        eapply step_acquire
          with
          (pmap := l0)
           (* (tp' :=
             updThread cnti
               (Kresume
                  (Callstate (Ctypes.External LOCK argsty retty cc) [l] k)
                  Vundef)
               (p0, pmax_new)) *)
          (*  (tp'' :=
             updLockSet
               (updThread cnti
                  (Kresume
                     (Callstate (Ctypes.External LOCK argsty retty cc) [l] k)
                     Vundef)
                  (p0, pmax_new))
               (l1.1, Ptrofs.intval (Ptrofs.repr l1.2)) 
               (empty_map, empty_map))  *)
          (virtueThread := virtueThread);
          try done.
        - admit.
        - simpl. rewrite Hl1. done.
        - admit.
        - admit.
        - simpl.
          rewrite /vt1.
          rewrite /delta_to_tree.
          

          admit.
        - admit.
        - f_equal.
          unfold virtueThread, vt1, vt2.
          do 2 f_equal.
          symmetry.
          eapply computeMap_delta_to_tree_exact.
          + admit.
          + admit.
          + simpl.
            
            Search computeMap.
          simpl.
          
          Search isCanonical.
          Search isCanan
          apply PMap.extensionality.
          simpl.
          Print computeMap.
          
          


          
          apply pair_equal_spec.
          split.
          + unfold virtueThread, vt1.
            (* p0.1 = (getThreadR cnti).1.1 *)
            (* Hp0_compute : computeMap (getThreadR cnti).1 vt1 = p0 *)
            simpl.
            symmetry.
            Print computeMap.
            Print computeMap.
            assert (Hjoin_compute :
                     permMapJoin l0.1 (getThreadR cnti).1
                       (computeMap (getThreadR cnti).1
                          (acquire_delta l0.1 (getThreadR cnti).1 (getMaxPerm m)))).
            {
              eapply acquire_delta_permMapJoin_new.
              admit. admit. admit.
            }
            assert (Hp0_compute :
                     computeMap (getThreadR cnti).1
                       (acquire_delta l0.1 (getThreadR cnti).1 (getMaxPerm m)) = p0).
            {
              Search permMapJoin.
              eapply permMapJoin_unique.
              - exact Hjoin_compute.
              - exact Hangel1.
            }

            
            assert (Hp0_compute :
                     computeMap (getThreadR cnti).1 virtueThread.1 = p0).
            {
              unfold virtueThread, vt1.
              simpl.
              Search computeMap acquire_delta permMapJoin.
            eapply computeMap_acquire_delta.
          exact Hangel1.
          set (vt1 :=
                 acquire_delta pmap.1 (getThreadR cnti).1 (getMaxPerm m)).

          set (vt2 :=
                 acquire_delta pmap.2 (getThreadR cnti).2 (getMaxPerm m)).

          set (virtueThread := (vt1, vt2)).

          set (pmax_new :=
                 computeMap (getThreadR cnti).2 vt2).
          apply pair_equal_spec.
          split.
          


        
        (* syncStep *)
        eapply step_acquire
          with
          (pmap := l0)
          (b := l1.1)
          (ofs := Ptrofs.repr l1.2)
          (virtueThread := (vt1, vt2))
          (tp' :=
             updThread cnti
               (Kresume
                  (Callstate (Ctypes.External LOCK argsty retty cc) [l] k)
                  Vundef)
               newThreadPerm)
          (tp'' := tp');
          try done.
        - admit.
        - admit.
        - admit.
        - admit.
        - simpl.
          pose proof (compat_lp _ _ Hcompat _ _ E) as [Hl0_1_lt Hl0_2_lt].
          pose proof (compat_th _ _ Hcompat cnti) as [Hth_1_lt Hth_2_lt].
          pose proof (no_race _ Hinvariant i l1 cnti l0 E) as Hnr.
          unfold permMapsDisjoint2 in Hnr.
          destruct Hnr as [Hdisj1 Hdisj2].
          assert (forall (b0 : positive) (ofs0 : Z),
                     ((getMaxPerm m).2 !! b0)%maps = None → (l0.1) # b0 ofs0 = None).
          { intros b0 ofs0 Hmax_none.
            pose proof (Max_isCanonical m) as Hmax_canon.
            rewrite /isCanonical in Hmax_canon.
            specialize (Hl0_1_lt b0 ofs0).
            rewrite /PMap.get Hmax_canon Hmax_none in Hl0_1_lt.
            rewrite /PMap.get.
            destruct ((l0.1.2 !! b0)%maps) eqn: Hperm.
            - pose proof (perm_order''_None (o ofs0)) as Hperm1.
              by specialize (perm_order_antisym None (o ofs0) Hl0_1_lt Hperm1).
            - pose proof (perm_order''_None (l0.1.1 ofs0)) as Hperm1.
              by specialize (perm_order_antisym None (l0.1.1 ofs0) Hl0_1_lt Hperm1).
          }
          eapply acquire_delta_permMapJoin_new; try apply permMapsDisjoint_comm; auto.
        - admit.
        - 

        
        eapply step_acquire
          with (pmap := l0) (b := l1.1) (ofs:= Ptrofs.repr l1.2)
               (virtueThread :=
                  (acquire_delta l0.1 (getThreadR cnti).1 (getMaxPerm m),
                    acquire_delta l0.2 (getThreadR cnti).2 (getMaxPerm m))); try done.
        + split.
          * rewrite /acquire_delta /bounded_maps.sub_map.
            intros p1 f1 Hf1.
            rewrite PTree.gmap in Hf1.
            destruct ((PTree.map1
                       (fun (f : Z -> perm_kind -> option permission) (ofs0 : Z) =>
                          f ofs0 Max)
                       (Mem.mem_access m).2 !! p1)%maps) as [f2 |] eqn:Hf2.
            ** exists f2. split; auto.
               intros p2 Hsome.
               unfold getMaxPerm in Hf1.
               simpl in Hf1.
               rewrite Hf2 in Hf1.
               inversion Hf1; subst.
               destruct (f2 p2); simpl in *; auto.
            ** rewrite /getMaxPerm /= in Hf1.
               rewrite Hf2 in Hf1.
               simpl in Hf1.
               discriminate.
          * rewrite /acquire_delta /bounded_maps.sub_map.
            intros p1 f1 Hf1.
            rewrite PTree.gmap in Hf1.
            destruct ((PTree.map1
                         (fun (f : Z -> perm_kind -> option permission) (ofs0 : Z) =>
                            f ofs0 Max)
                         (Mem.mem_access m).2 !! p1)%maps) as [f2 |] eqn:Hf2.
            ** exists f2. split; auto.
               intros p2 Hsome.
               unfold getMaxPerm in Hf1.
               simpl in Hf1.
               rewrite Hf2 in Hf1.
               inversion Hf1; subst.
               destruct (f2 p2); simpl in *; auto.
            ** rewrite /getMaxPerm /= in Hf1.
               rewrite Hf2 in Hf1.
               simpl in Hf1.
               discriminate.
        + by rewrite Hl1.
        + rewrite /Mem_load_unchecked /=.
          by rewrite Hofs.
        + simpl.
          split.
          * pose proof (compat_lp _ _ Hcompat _ _ E) as [Hl0_1_lt Hl0_2_lt].
            pose proof (compat_th _ _ Hcompat cnti) as [Hth_1_lt Hth_2_lt].
            eapply computeMap_acquire_delta_permMapLt; eauto.
            intros.
            apply join_perm_below_max; auto.
            destruct Hinvariant.
            apply permMapsDisjoint_comm.
            eapply no_race0; eauto.
          * pose proof (compat_lp _ _ Hcompat _ _ E) as [Hl0_1_lt Hl0_2_lt].
            pose proof (compat_th _ _ Hcompat cnti) as [Hth_1_lt Hth_2_lt].
            eapply computeMap_acquire_delta_permMapLt; eauto.
            intros.
            apply join_perm_below_max; auto.
            destruct Hinvariant.
            apply permMapsDisjoint_comm.
            eapply no_race0; eauto.
        + 
          simpl.
          pose proof (compat_lp _ _ Hcompat _ _ E) as [Hl0_1_lt Hl0_2_lt].
          pose proof (compat_th _ _ Hcompat cnti) as [Hth_1_lt Hth_2_lt].
          pose proof (no_race _ Hinvariant i l1 cnti l0 E) as Hnr.
          unfold permMapsDisjoint2 in Hnr.
          destruct Hnr as [Hdisj1 Hdisj2].
          assert (forall (b0 : positive) (ofs0 : Z),
                     ((getMaxPerm m).2 !! b0)%maps = None → (l0.1) # b0 ofs0 = None).
          { intros b0 ofs0 Hmax_none.
            pose proof (Max_isCanonical m) as Hmax_canon.
            rewrite /isCanonical in Hmax_canon.
            specialize (Hl0_1_lt b0 ofs0).
            rewrite /PMap.get Hmax_canon Hmax_none in Hl0_1_lt.
            rewrite /PMap.get.
            destruct ((l0.1.2 !! b0)%maps) eqn: Hperm.
            - pose proof (perm_order''_None (o ofs0)) as Hperm1.
              by specialize (perm_order_antisym None (o ofs0) Hl0_1_lt Hperm1).
            - pose proof (perm_order''_None (l0.1.1 ofs0)) as Hperm1.
              by specialize (perm_order_antisym None (l0.1.1 ofs0) Hl0_1_lt Hperm1).
          }
          eapply acquire_delta_permMapJoin_new; try apply permMapsDisjoint_comm; auto.
        + simpl.
          pose proof (compat_lp _ _ Hcompat _ _ E) as [Hl0_1_lt Hl0_2_lt].
          pose proof (compat_th _ _ Hcompat cnti) as [Hth_1_lt Hth_2_lt].
          pose proof (no_race _ Hinvariant i l1 cnti l0 E) as Hnr.
          unfold permMapsDisjoint2 in Hnr.
          destruct Hnr as [Hdisj1 Hdisj2].
          assert (forall (b0 : positive) (ofs0 : Z),
                     ((getMaxPerm m).2 !! b0)%maps = None → (l0.2) # b0 ofs0 = None).
          { intros b0 ofs0 Hmax_none.
            pose proof (Max_isCanonical m) as Hmax_canon.
            rewrite /isCanonical in Hmax_canon.
            specialize (Hl0_2_lt b0 ofs0).
            rewrite /PMap.get Hmax_canon Hmax_none in Hl0_2_lt.
            rewrite /PMap.get.
            destruct ((l0.2.2 !! b0)%maps) eqn: Hperm.
            - pose proof (perm_order''_None (o ofs0)) as Hperm1.
              by specialize (perm_order_antisym None (o ofs0) Hl0_2_lt Hperm1).
            - pose proof (perm_order''_None (l0.2.1 ofs0)) as Hperm1.
              by specialize (perm_order_antisym None (l0.2.1 ofs0) Hl0_2_lt Hperm1).
          }
          eapply acquire_delta_permMapJoin_new; try apply permMapsDisjoint_comm; auto.
       + split.
         (* threads_wellformed *)
         eapply threads_wellformed_acquire_lock; auto.
         split.
         (* invariant *)
         * eapply invariant_acquire_lock; eauto.
         * (* mem_compatible *)
           rewrite /Mem_store_unchecked /=.
           admit.
      }

    set tp' :=
      (updLockSet
         (updThread cnti
            (Kresume
               (Callstate (Ctypes.External LOCK argsty retty cc) [l] k)
               Vundef)
            (p',
              computeMap (getThreadR cnti).2
                (acquire_delta l0.2 (getThreadR cnti).2 (getMaxPerm m))))
         (l1.1, Ptrofs.intval (Ptrofs.repr l1.2))
         (empty_map, empty_map)).
      assert (forall (i0 : nat) (r : access_map),
                 snd <$> perms1 !! i0 = Some r
                                          ↔ ∃ cnti0 : OrdinalPool.containsThread tp' i0, (OrdinalPool.getThreadR cnti0).1 = r).
      {
        subst perms1.
        intros i0 r.
        destruct (decide (i0 = i)) as [-> | Hneq].
        - split.
          rewrite lookup_insert.
          intros.
          simpl in H.
          inversion H.
          rewrite lookup_insert in H3.
          inversion H3.
          subst.
          simpl in H1.
          inversion H1. subst.
          subst tp'.
          eexists.
          Search getThreadR updLockSet.
          rewrite gThreadResLockSet.
          rewrite gssThreadRes.
          rewrite <- H2.
          rewrite /tp'.
          eexists.
          simpl.
          simpl.
          inv H.
        (*
          when i0 = i, we need p0 = new thread permission in tp'
          p0 =
computeMap (getThreadR cnti).1
  (acquire_delta l0.1 (getThreadR cnti).1 (getMaxPerm m),
   acquire_delta l0.2 (getThreadR cnti).2 (getMaxPerm m)).1
         *)
          admit.
          admit.
        - admit.
      }

      (*
      iDestruct (lock_inv_get_R m ls sh l R with "[Hl Hls]") as "(HR & HR1 & HR2)". admit.
      iFrame.
      
      iAssert (▷ ∀ (ret : option val) (m' : mem) (z' : ()),
                   ⌜Val.has_type_list [l] (sig_args (ef_sig LOCK))
                   ∧ Builtins0.val_opt_has_rettype ret (sig_res UNLOCK_SIG)⌝
                   → |={⊤}=>
                 thread_state_interp g m' z' -∗
                                                match acquire_spec with
                                                | mk_funspec _ _ A _ _ Q =>
                                                    ∃ x'' : dtfr A,
                 ⌜JMeq.JMeq x x''⌝
                 ∧ funspec2post' A Q x'' (genv_symb_injective ge) (sig_res (ef_sig LOCK)) ret
               end )%I with "[HR HR1]" as "Hpost1".
    {
      iNext.
      iIntros (ret m' z') "%Hty".
      iIntros "!> Hthr". 
      unfold acquire_spec.
      simpl.
      iExists (l, sh, R).
      iSplit; auto.
      destruct z'.
      rewrite /PROPx /PARAMSx /GLOBALSx /LOCALx /SEPx /=.
      iSplit; auto.
      iFrame.
      *)

      (*
pose (vt1 := acquire_delta l0.1 (getThreadR cnti).1 (getMaxPerm m)).

      pose (vt2 := acquire_delta l0.2 (getThreadR cnti).2 (getMaxPerm m)).

      pose (p_new := computeMap (getThreadR cnti).1 vt1).

      pose (pmax_new := computeMap (getThreadR cnti).2 vt2).

      pose (newThreadPerm := (p_new, pmax_new)).
      assert (forall (i0 : nat) (r : access_map), snd <$> perms1 !! i0 = Some r ↔
          ∃ cnti0 : OrdinalPool.containsThread tp' i0, (OrdinalPool.getThreadR cnti0).1 = r).
      {
        subst perms1.
        intros i0 r.
        destruct (decide (i0 = i)) as [-> | Hneq].
        - rewrite lookup_insert; auto.
          split; intros.
          + admit.
          + destruct H1 as (ctni & H1).
            simpl.
            apply f_equal.
            rewrite <- H1.
            symmetry.
            subst tp'.
            set (c' := Kresume (Callstate (Ctypes.External LOCK argsty retty cc) [l] k) Vundef).

            set (pmap :=
                   (p0,
                     computeMap (getThreadR cnti).2
                       (acquire_delta l0.2 (getThreadR cnti).2 (getMaxPerm m)))).
            set (addr := (l1.1, Ptrofs.intval (Ptrofs.repr l1.2))).
            set (lmap := (empty_map, empty_map)).
            assert (cntiL : OrdinalPool.containsThread (updLockSet tp addr lmap) i).
            {
              change (OrdinalPool.containsThread tp i).
              exact cnti.
            }
            pose proof (OrdinalPool.updLock_updThread_comm cnti c' pmap) as Hcomm.
            pose proof (Hcomm addr lmap cntiL) as Hcomm'.

            destruct (eq_sym Hcomm').
            pose proof
              (@OrdinalPool.gssThreadRes
                 _ _
                 i
                 (updLockSet tp addr lmap)
                 cntiL
                 c'
                 pmap
                 ctni) as Hres.
            rewrite Hres.
            by unfold pmap.
       - rewrite lookup_insert_ne; auto.
         split; intros.
         + simpl in H1.
           subst tp'.
           destruct (proj1 (Hperms i0 r) H1) as [cnti0_old Hr_old].
           assert (cnti0' :
                    OrdinalPool.containsThread
                      (updThread cnti
                         (Kresume (Callstate (Ctypes.External LOCK argsty retty cc) [l] k) Vundef)
                         newThreadPerm) i0).
           { eapply OrdinalPool.cntUpdate; done. }
           set (c_upd :=
                  Kresume (Callstate (Ctypes.External LOCK argsty retty cc) [l] k) Vundef).

           set (pmap :=
                  (p0,
                    computeMap (getThreadR cnti).2
                      (acquire_delta l0.2 (getThreadR cnti).2 (getMaxPerm m)))).

           set (addr := (l1.1, Ptrofs.intval (Ptrofs.repr l1.2))).
           set (lmap := (empty_map, empty_map)).
           
           assert (cnti0_mid :
                    OrdinalPool.containsThread
                      (OrdinalPool.updThread cnti c_upd pmap) i0).
           {
             apply OrdinalPool.cntUpdate.
             exact cnti0_old.
           }

           assert (cnti0_final :
                    OrdinalPool.containsThread
                      (OrdinalPool.updLockSet
                         (OrdinalPool.updThread cnti c_upd pmap) addr lmap) i0).
           {
             change (OrdinalPool.containsThread
                       (OrdinalPool.updThread cnti c_upd pmap) i0).
             exact cnti0_mid.
           }
           exists cnti0_final.
           assert (Hneq' : i <> i0) by auto.
           assert (Hmid :
                    (OrdinalPool.getThreadR cnti0_mid).1 =
                      (OrdinalPool.getThreadR cnti0_old).1).
           { erewrite OrdinalPool.gsoThreadRes; eauto. }
           pose proof
             (@OrdinalPool.gLockSetRes
                _ _
                i0
                (OrdinalPool.updThread cnti c_upd pmap)
                addr
                lmap
                cnti0_mid
                cnti0_final) as Hlock.
           pose proof (f_equal (fun x => x.1) Hlock) as Hlock1.
           etransitivity; try apply Hmid; eauto.
           exact (eq_trans Hmid Hr_old).
         + admit. }

*)
      
      
 Admitted.
 (*
    iMod ("Hpost").

    
    assert (ext_step cnti Hcompat (updLockSet (updThread cnti (Kresume c Vundef) newThreadPerm) (b, Ptrofs.intval ofs) (empty_map, empty_map)) m' (Events.acquire (b, Ptrofs.intval ofs) (Some (build_delta_content virtueThread.1 m')))) as Hstep.
    
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

  Theorem dry_safety `{!VSTGpreS unit Σ} `{!inG Σ (gmap_view.gmap_viewR address unitR)}
    `{!inG Σ (gmap_view.gmap_viewR address (laterO (iPropO Σ)))} sch n : exists b c_init,
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
    iMod (@init_conc_VST _ _ VSTGpreS0 _ (`init_mem) tt) as "H".
    iDestruct ("H" $! Hinv) as (?? HE ????) "(H & ? & locks & ? & ?)".
    set (HC := ConcVSTGS _ _ (ConcHeapGS _ _ _ _) HE _).
    destruct (spr (thread_VSTGS γ0) _) as (b & q & (? & ? & Hinit) & Hsafe); [| done..].
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
    iAssert (threads_safe (*(getMaxPerm (`init_mem)) *) tp (fst <$> perms)) with "[Hsafe]" as "Hsafe".
    { rewrite /threads_safe /=.
      iSplit; last done.
      iExists γ0; iSplit; first done.
      unshelve iExists _; first done; simpl.
      iApply (jsafe_jsafe_perm with "Hsafe").
    }
    assert (locks_coherent tp (`init_mem) ∅) as Hlocks by done.
    forget (proj1_sig init_mem) as m.
    forget (@nil Events.machine_event) as tr.
    assert (forall i r, snd <$> (perms !! i) = Some r <-> ∃ cnti : containsThread tp i, (getThreadR cnti).1 = r)
      as Hperms.
    { intros [|] ?; rewrite /perms /tp /= /OrdinalPool.containsThread /=.
      * rewrite lookup_insert /=.
        split; [by inversion 1; exists eq_refl | by intros (? & <-)].
      * rewrite lookup_insert_ne // lookup_empty.
        split; first done.
        intros (? & ?); done.
    }
    clearbody perms tp.
    set (ls := ∅) in Hlocks |- *.
    clearbody ls.
    clear dependent b x q.
    iLöb as "IH" forall (sch tr tp m perms n ls Htp_wf Hinvariant Hcompat Hlocks Hperms).
    destruct n as [|n].
    { iPureIntro. constructor. }
    destruct sch as [|i sch].
    { iApply step_fupdN_intro; first done; iPureIntro. constructor; done. }
    simpl; destruct (lt_dec i (pos.n (OrdinalPool.num_threads tp))).
    2: {
      Local Opaque lock_state.
      iApply step_fupd_intro; try done. iNext.
      iAssert (|={⊤}[∅]▷=>^n ∀ U'', ⌜HybridMachineSig.HybridCoarseMachine.csafe (U'', tr, tp) m n⌝) with "[-]" as "H".
      { rewrite step_fupdN_plain_forall //.
        iIntros.
        iApply ("IH" with "[%] [%] [%] [%] [%]  locks S Hsafe"); done.
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
        iAssert (threads_safe (*(getMaxPerm m)*) tp (fst <$> perms))
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
          + iApply "Hsafe".
            * iIntros "!>" (?? (-> & ?)%lookup_seq ?) "(% & $ & % & Hsafe)".
              iExists (cntUpdateC _ _ _); rewrite -gsoThreadCC // gThreadCR //.
            * iFrame "%"; iExists (cntUpdateC _ _ _); rewrite gssThreadCC gThreadCR.
              by iApply "Hsafei".
        }
        iApply (step_fupdN_mono with "H"); iPureIntro; intros Hsafe.
        eapply HybridMachineSig.HybridCoarseMachine.AngelSafe with (tr := []); simpl; rewrite seq.cats0; last apply Hsafe.
        eapply HybridMachineSig.suspend_step; eauto.
      + (* corestep: HybridMachineSig.thread_step *)
        edestruct Hperms as [_ Hpermi].
        spec Hpermi; first by exists cnti.
        rewrite !lookup_fmap in Hgi Hpermi.
        destruct (perms !! (0 + i)) as [(?, p)|] eqn: Hpi; inv Hgi; inv Hpermi.
        iDestruct (conc_state_interp_lookup1 with "S") as "(% & S & H)"; first done.
        rewrite jsafe_perm_unfold /jsafe_perm_pre.
        iMod ("Hsafei" with "[%] S") as "[Hhalt | [Hstep | Hext]]".
        { apply mem_equiv.getCur_restr. (*
          split; [apply mem_equiv.getCur_restr | apply restr_Max_eq]. *) }
        { iDestruct "Hhalt" as (? Hhalt') "?"; done. }
        2: { iDestruct "Hext" as (??? Hext) "?". simpl in Hext; congruence. }
        (* HStep *)
        iMod "Hstep" as (?? Hstep) "(S & Hsafei)".
        assert (corestep (cl_core_sem ge) s (restrPermMap (ssrfun.pair_of_and (Hcompat i cnti)).1) c' m') as Hstep'.
        { by erewrite restrPermMap_irr. }
        iApply step_fupd_intro; first done; iNext.
        apply (ev_step_ax2 (Clight_evsem.CLC_evsem ge)) in Hstep' as (? & Hstep').
        assert (mem_compatible (updThread cnti (Krun c') (getCurPerm m', (getThreadR cnti).2)) m') as Hcompat'
          by by eapply (CoreLanguageDry.corestep_compatible(Sem := Sem)).
        iDestruct ("H" with "[$S]") as "S".
        { iPureIntro; split; last done. split.
          * by eapply CLC_corestep_mem.
          * split.
            - intros ???? Hj.
              specialize (Hperms j); rewrite Hj /= in Hperms.
              edestruct Hperms as [(cntj & <-) _]; first done.
              inv Hcompat'.
              unshelve exploit compat_th0.
              2: by eapply cntUpdate.
              rewrite gsoThreadRes //.
              by intros (? & ?).
            - split.
              + intros j g0 p _ Hj.
                have Hj_snd : snd <$> perms !! j = Some p by rewrite Hj /=.
                have [cntj Hrj] := (proj1 (Hperms j p) Hj_snd).
                have Hj_lt : permMapLt (getThreadR cntj).1 (getMaxPerm m) :=
                  (ssrfun.pair_of_and (Hcompat j cntj)).1.
                by rewrite Hrj in Hj_lt.
              + inv Hinvariant.
                unfold permMapsDisjoint_at; intros.
                rewrite Hpi.
                destruct (perms !! j) as [(?,?)|] eqn: Hj; last done.
                specialize (Hperms j); rewrite Hj /= in Hperms.
                edestruct Hperms as [(cntj & <-) _]; first done.
                by apply no_race_thr0.
        }
        iAssert (lock_state γl m' ls) with "[locks]" as "locks". admit.
        iSpecialize ("IH" $! _ _ (updThread cnti (Krun c') (getCurPerm m', (getThreadR cnti).2)) m' (<[i := (g, getCurPerm m')]> perms) _ with "[%] [%] [%] [%] [%] locks S [Hsafe Hsafei]").
        * intros j cntj.
          destruct (eq_dec j i); first by subst; rewrite gssThreadCode.
          pose proof (cntUpdate' _ _ cnti cntj).
          rewrite gsoThreadCode //; apply Htp_wf.
        * eapply (CoreLanguageDry.corestep_invariant(Sem := Sem)); try done.
          by eapply ev_step_ax1.
        * apply Hcompat'.
        * admit. (* intros ??; rewrite gsoThreadLPool.
          intros.
          rewrite /locks_coherent in Hlocks.
          pose proof Hlocks as Hlocks1.
          specialize (Hlocks l0).
          pose proof H1 as Hl0.
          assert (Hm: Mem_load_unchecked Mptr m l0.1 l0.2 =
                        Mem_load_unchecked Mptr (restrPermMap Hp) l0.1 l0.2) by done.
          rewrite Hm in Hlocks.
          apply Hlocks in Hl0.
          destruct Hl0 as (? & Hl1 & Hn).
          split; try apply Hl1; try done.
          split; intros.
          split; intros.
          ** eapply Hl1; try done.
             rewrite /Mem_unchecked in H2 |- *.
             rewrite <- H2.
             do 2 f_equal.
             eapply mem_step_preserves_lock_bytes; eauto.
             apply CLC_corestep_mem in Hstep; auto.
          ** apply Hl1 in H2.
             rewrite /Mem_unchecked in H2 |- *.
             rewrite <- H2.
             do 2 f_equal.
             symmetry.
             eapply mem_step_preserves_lock_bytes.
             apply CLC_corestep_mem in Hstep; auto.
             exact Hn.
          ** specialize (Hlocks1 l0).
             destruct (decide (i0 = i)); subst.
             ++ assert (HsameR : (getThreadR cnti0).1 = getCurPerm m').
                { by rewrite gssThreadRes. }
                assert (Hpcur : permMapLt (getCurPerm m') (getMaxPerm m')).
                { by rewrite <- HsameR. }
                replace (restrPermMap Hp0) with (restrPermMap Hpcur).
                2 : { eapply restrPermMap_irr'; auto. }
                rewrite restrPermMap_eq.
                rewrite /nonEmptyRangeCur in Hn |- *.
                eapply (mem_step_preserves_nonempty_range (restrPermMap Hp)).
                by apply CLC_corestep_mem in Hstep; auto. exact Hn.
             ++ assert (Hres0 : ∃ cntj : containsThread tp i0, getThreadR cnti0 = getThreadR cntj).
                { eexists. apply gsoThreadRes; done. }
                destruct Hres0 as [cntj Hres0].
                assert (Hpj : permMapLt (getThreadR cntj).1 (getMaxPerm m)) by apply Hcompat.
                specialize (Hlocks1 i0 cntj Hpj H0).
                destruct Hlocks1 as (_ & _ & Hne).
                assert (Hperm : (getThreadR cnti0).1 = (getThreadR cntj).1).
                { by rewrite Hres0. }
                pose proof Hp0 as Hp0'.
                rewrite Hperm in Hp0'.
                rewrite /nonEmptyRangeCur in Hne |- *.
                intros.
                specialize (Hne i1 H2).
                rewrite <- Hperm in Hp0'.
                assert (Heq_restr : restrPermMap Hp0 = restrPermMap Hp0').
                { apply restr_proof_irr. }
                rewrite restrPermMap_Cur_eq in Hne.
                rewrite restrPermMap_Cur_eq.
                by rewrite Hperm. *)
        * intros j r.
          destruct (decide (i = j)).
          { subst; rewrite lookup_insert; setoid_rewrite (gssThreadRes cnti); split.
            - inversion 1; by exists (OrdinalPool.cntUpdate _ _ cnti cnti).
            - by intros (? & <-). }
          { rewrite lookup_insert_ne // Hperms.
            setoid_rewrite (gsoThreadRes cnti); last done.
            split; intros (? & ?); eauto. }
        * iApply "Hsafe".
          ** iIntros "!>" (?? (-> & ?)%lookup_seq ?) "(% & % & % & Hsafe)".
             rewrite lookup_fmap in H2.
             rewrite lookup_fmap lookup_insert_ne //; iExists _; iSplit; first done.
             iExists (cntUpdate _ _ cnti cnti0).
             rewrite gsoThreadCode // gsoThreadRes //.
          ** rewrite lookup_fmap lookup_insert /=; iExists _; iSplit; first done.
             iExists (cntUpdate _ _ cnti cnti).
             rewrite gssThreadCode gssThreadRes //.
        * iApply (step_fupdN_mono with "IH").
          iPureIntro; intros.
          eapply HybridMachineSig.HybridCoarseMachine.CoreSafe; last done.
          rewrite /HybridMachineSig.MachStep /=.
          change (i :: sch) with (HybridMachineSig.yield (i :: sch)) at 2.
          change m' with (HybridMachineSig.diluteMem m') at 3.
          eapply HybridMachineSig.thread_step; first done.
          by eapply step_dry.
    - (* Kblocked: HybridMachineSig.sync_step *)
      pose proof (Htp_wf _ cnti) as Hwfi; rewrite Hi in Hwfi.
      edestruct Hperms as [_ Hpermi].
      spec Hpermi; first by exists cnti.
      rewrite !lookup_fmap in Hgi Hpermi.
      destruct (perms !! (0 + i)) as [(?, p)|] eqn: Hpi; inv Hgi; inv Hpermi.
      iDestruct (conc_state_interp_lookup2 with "S") as "(% & S & H)"; first done.
      rewrite jsafe_perm_unfold /jsafe_perm_pre.
      iMod ("Hsafei" with "[%] S") as "[Hhalt | [Hstep | Hext]]".
      { apply mem_equiv.getCur_restr. }
      { iDestruct "Hhalt" as (? Hhalt') "?"; destruct s; done. }
      { iMod "Hstep" as (?? Hstep) "?".
        apply cl_corestep_not_at_external in Hstep; done.
      }
      (* cl_at_external s = Some (e, args) *)
      iDestruct "Hext" as (??? Hat_ext) "(S & Hpre & Hpost)".
      simpl in Hat_ext.
      iAssert (|={⊤}[∅]▷=> ∃ (tp' : t(ThreadPool := OrdinalPool.OrdinalThreadPool)) m' ev perms',
                ⌜threads_wellformed tp' ∧ invariant tp' ∧ mem_compatible tp' m' ∧
                 locks_coherent tp' m' ls ∧ syncStep true cnti Hcompat tp' m' ev /\
                  (∀ (i0 : nat) (r : access_map), snd <$> perms' !! i0 = Some r
                    ↔ ∃ cnti0 : OrdinalPool.containsThread tp' i0,
                      (OrdinalPool.getThreadR cnti0).1 = r)⌝ ∧
                  threads_safe (* (getMaxPerm m') *)
                    tp' (fst <$> (* <[i:=(g, getCurPerm m')]> *) perms') ∗
                    (conc_mem_auth m (delete i perms) -∗ conc_mem_auth m' (delete i perms')) ∗

                    (∃ (p : access_map) (Hlt : permMapLt p (getMaxPerm m')),
                     ⌜(perms' !! i = Some (g, p))⌝ ∧ 
                       thread_state_interp g (restrPermMap Hlt) (* z'  state_interp (restrPermMap Hlt) *) tt) ∗
                    lock_state γl m' ls  (* ∗ lock_set ls*) )
        with "[Hpost Hsafe locks Hpre S]" as "Hsafe".
      2 : {
        iMod "Hsafe".
        iIntros "!> !>".
        iMod "Hsafe" as (???? (? & ? & ? & ? & ? & ?)) "(Hsafe & SC & S1 & locks1)".
        iAssert (|={⊤}[∅]▷=>^n ∀ U'', ⌜HybridMachineSig.HybridCoarseMachine.csafe (U'', tr ++ [Events.external i ev], tp') m' n⌝) with "[-]" as "H".
        { rewrite step_fupdN_plain_forall //.
          iIntros.
          iSpecialize ("SC" with "H"). 
          replace (0 + i) with i; auto.
          assert (snd <$> perms !! i = Some (OrdinalPool.getThreadR cnti).1).
          { by rewrite Hpi. }
          iDestruct "S1" as (??) "(% & S1)".
          assert (Hperms'i : snd <$> perms' !! i = Some p).
          { by rewrite H7. }
          destruct (proj1 (H5 i p) Hperms'i) as [cnti' Hcnti'].
          iDestruct (thread_state_interp_conc_state_interp_delete_insert_restr
                      with "[$S1 $SC]") as "SC".
          subst.
          (* iDestruct (lock_state_empty_mem_irrel m m' with "locks1") as "locks1". *)
          iApply ("IH" with "[%] [%] [%] [%] [%] locks1 SC"); try done.
          intros i0 r.
          replace (<[i := (g, (OrdinalPool.getThreadR cnti').1)]> perms') with perms'.
          - apply H5.
          - symmetry; by apply insert_id.
          - rewrite (insert_id perms' i (g, (OrdinalPool.getThreadR cnti').1)); auto.
        }
        iApply (step_fupdN_mono with "H"); iPureIntro.
        intros Hsafe.
        eapply HybridMachineSig.HybridCoarseMachine.AngelSafe; simpl; last apply Hsafe.
        eapply HybridMachineSig.sync_step; eauto.
      }
      
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
      admit.
    - (* Kresume: HybridMachineSig.resume_step *)
      pose proof (Htp_wf _ cnti) as Hwfi; rewrite Hi in Hwfi; destruct Hwfi as (? & ->).
      destruct s; try done.
      destruct f; try done.
      assert (HybridMachineSig.resume_thread m cnti (updThreadC cnti (Krun (Returnstate Vundef c)))) as Hresume.
      { unfold cl_at_external in *; destruct (ef_inline e) eqn: Hinline; try done.
        eapply (HybridMachineSig.ResumeThread _ _ _ _ _ _ _ _ _ Hcompat); try done; simpl; by rewrite ?Hinline. }
      iApply step_fupd_intro; first done; iNext.
      iSpecialize ("IH" $! _ _ (updThreadC cnti (Krun (Returnstate Vundef c))) with "[%] [%] [%] [%] [%] [$] [S] [Hsafei Hsafe]").
      + intros j cntj.
        destruct (eq_dec j i).
        * subst; rewrite gssThreadCC //.
        * pose proof (cntUpdateC' _ cnti cntj) as cntj0.
          rewrite -gsoThreadCC //; apply Htp_wf.
      + by apply ThreadPoolWF.updThreadC_invariant.
      + by apply StepLemmas.updThreadC_compatible.
      + rewrite /locks_coherent in Hlocks |- *.
        intros. 
        rewrite gsoThreadCLPool.
        destruct (eq_nat_dec i i0) as [<- | Hneq].
        * assert (HsameR : (getThreadR cnti).1 = (getThreadR cnti0).1).
          { erewrite <- gThreadCR; eauto. }
          pose proof Hp as Hp'.
          rewrite <- HsameR in Hp'.
          specialize (Hlocks l1 i cnti Hp' H1).
          destruct Hlocks as (? & ? & ?).
          replace (restrPermMap Hp) with (restrPermMap Hp').
          2 : { eapply restr_proof_irr'; done. }
          split; try done.
        * (* Up *)
          by apply Hlocks.
      + intros.
        instantiate (1 := perms).
        split.
        ++ intros.
           destruct (eq_dec i0 i) as [-> | Hneq].
           * apply (proj1 (Hperms i r) H1).
           * apply (proj1 (Hperms i0 r) H1).
       ++ intros.
          set tp' := OrdinalPool.updThreadC cnti (Krun (Returnstate Vundef c)).
          destruct (eq_dec i0 i) as [-> | Hneq].
           * apply (proj2 (Hperms i r)).
             case: H1 => cntj Hcntj.
             exists cnti.
             by have ->: cnti = cntj by apply proof_irrelevance.
           * apply (proj2 (Hperms i0 r)).
             case: H1 => cntj Hcntj.
             have cnti0 : OrdinalPool.containsThread tp i0 by auto.
             exists cnti0.
             by have ->: cnti0 = cntj by apply proof_irrelevance.
      + done.
      + iApply "Hsafe".
        * iIntros "!>" (?? (-> & ?)%lookup_seq ?) "(% & % & Hsafe)".
          iExists g0.
          iSplit; auto.
          iDestruct "Hsafe" as (cntk) "Hthr".
          rewrite /thread_safe.
          erewrite gsoThreadCC; eauto.
        * iExists g.
          iSplit; auto.
          rewrite /thread_safe.
          assert (cnti' : containsThread (updThreadC cnti (Krun (Returnstate Vundef c))) i); try done.
          iExists cnti'.
          rewrite gssThreadCC.
          have -> : (getThreadR cnti').1 = (getThreadR cnti).1.
          { rewrite /getThreadR /=.
            have <- : fintype.Ordinal cnti = fintype.Ordinal cnti'.
            { f_equal; apply proof_irrelevance. }
            reflexivity.
          }
          by iApply ("Hsafei" $! (Returnstate Vundef c)).
      + iApply (step_fupdN_mono with "IH"); iPureIntro; intros Hsafe.
        eapply HybridMachineSig.HybridCoarseMachine.CoreSafe with (tr := []); simpl; rewrite seq.cats0; last apply Hsafe.
        change (i :: sch) with (HybridMachineSig.yield (i :: sch)) at 2.
        eapply HybridMachineSig.resume_step; eauto. 
    - (* Kinit: HybridMachineSig.start_step *)
      iDestruct "Hsafei" as (? Hinit) "Hsafei".
      set (m' := restrPermMap (ssrfun.pair_of_and (Hcompat i cnti)).1).
      set (tp' := updThread cnti (Krun q_new) (HybridMachineSig.add_block Hcompat cnti m')).
      assert (HybridMachineSig.start_thread m cnti tp' m').
      { econstructor; done. }
      iApply step_fupd_intro; first done; iNext.
      iSpecialize ("IH" $! _ _ tp' m' with "[%] [%] [%] [%] [%] [$] [S] [Hsafei Hsafe]").
      + intros j cntj.
        destruct (eq_dec j i).
        * subst; rewrite gssThreadCode //.
        * pose proof (cntUpdate' _ _ cnti cntj).
          rewrite gsoThreadCode //; apply Htp_wf.
      + by eapply (CoreLanguageDry.initial_core_invariant(Sem := Sem)).
      + eapply InternalSteps.start_compatible; try done.
      + (* Up: locks_coherent *)
        rewrite /locks_coherent in Hlocks |- *.
        intros.
        assert (Hlockeq : lockRes tp' l0 = lockRes tp l0).
        { by rewrite /tp' gsoThreadLPool. }
        assert (Hm : Mem_unchecked Mptr m' l0.1 l0.2 = Mem_unchecked Mptr m l0.1 l0.2) by done.
        destruct (eq_nat_dec i i0) as [<- | Hneq].
        * specialize (Hlocks l0 i cnti (ssrfun.pair_of_and (Hcompat i cnti)).1 H1).
          destruct Hlocks as (Hn & Hmem & Hnone).
          split; try by rewrite Hlockeq.
          split.
          ** split.
             intros.
             apply Hmem. by rewrite <- Hm.
             intros.
             apply Hmem. by rewrite Hlockeq in H2.
          ** rewrite /nonEmptyRangeCur in Hnone |- *.
             intros.
             specialize (Hnone i0 H2).
             rewrite restrPermMap_Cur_eq.
             rewrite restrPermMap_Cur_eq in Hnone.
             assert (Hget :
                      getThreadR cnti0 = HybridMachineSig.add_block Hcompat cnti m').
             { eapply gssThreadRes. }
             rewrite Hget.
             unfold HybridMachineSig.add_block.
             simpl.
             rewrite /m'.
             simpl.
             pose proof (mem_equiv.getCur_restr ((getThreadR cnti).1) m
                           (ssrfun.pair_of_and (Hcompat i cnti)).1) as Hcur.
             unfold mem_equiv.access_map_equiv in Hcur.
             by rewrite (Hcur (l0.1)).
        * assert (cnti0_old : containsThread tp i0).
          { subst tp'; eapply cntUpdate'; eauto. }
          assert (Hr_eq : (getThreadR cnti0).1 = (getThreadR cnti0_old).1).
          { subst tp'; rewrite gsoThreadRes; auto. }
          assert (Hp0 : permMapLt (getThreadR cnti0_old).1 (getMaxPerm m)).
          { replace ((getThreadR cnti0_old).1) with ((getThreadR cnti0).1). 
            subst m'.
            by rewrite restr_Max_eq in Hp.
          }
          specialize (Hlocks l0 i0 cnti0_old Hp0 H1).
          destruct Hlocks as (Hn & Hmem & Hnone).
          split; try by rewrite Hlockeq.
          split.
          ** split; rewrite Hlockeq.
             intros.
             apply Hmem. by rewrite <- Hm.
             intros.
             by apply Hmem.
          ** rewrite /nonEmptyRangeCur in Hnone |- *.
             intros.
             specialize (Hnone i1 H2).
             rewrite restrPermMap_Cur_eq in Hnone.
             rewrite restrPermMap_Cur_eq.
             by rewrite Hr_eq.
      + intros.
        instantiate (1 := <[i := (g, getCurPerm m')]> perms).
        split.
        ++ intros.
           destruct (eq_dec i0 i) as [-> | Hneq].
           * rewrite lookup_insert /= in H1.
             inv H1.
             exists (OrdinalPool.cntUpdate (Sem := Sem) (Krun q_new)
                      (HybridMachineSig.add_block Hcompat cnti m') cnti cnti).
             rewrite /tp' /m' OrdinalPool.gssThreadRes //.
           * rewrite lookup_insert_ne // in H1.
             have [cntj Hcntj] :
               exists cntj : OrdinalPool.containsThread tp i0, (OrdinalPool.getThreadR cntj).1 = r.
             { exact (proj1 (Hperms i0 r) H1). }
             exists (OrdinalPool.cntUpdate (Sem := Sem) (Krun q_new)
                      (HybridMachineSig.add_block Hcompat cnti m') cnti cntj).
             by rewrite OrdinalPool.gsoThreadRes.
        ++ intros.
           destruct (eq_dec i0 i) as [-> | Hneq].
           * rewrite lookup_insert /=.
             f_equal.
             rewrite /tp' in H1.
             destruct H1 as (cntj & <-).
             by rewrite OrdinalPool.gssThreadRes.
           * rewrite lookup_insert_ne //.
             destruct H1 as (cntj & Hcntj).
             set (cnt0 := OrdinalPool.cntUpdate' (Sem := Sem) (i := 0 + i) (j := i0) (tp := tp)
                            (c := Krun q_new)
                            (p := HybridMachineSig.add_block Hcompat cnti m') (cnti := cnti) cntj).
             apply (proj2 (Hperms i0 r)).
             exists cnt0.
             simpl.
             have Hres : OrdinalPool.getThreadR cntj = OrdinalPool.getThreadR cnt0.
             { eapply OrdinalPool.gsoThreadRes. lia. }
             have Hr0 : (OrdinalPool.getThreadR cnt0).1 = r; auto.
             { apply (f_equal fst) in Hres; by rewrite <- Hres. }
      + iDestruct "S" as "(S & ?)".
        iFrame.
        rewrite /m'.
        change (0 + i) with i in *.
        have Hsnd : snd <$> perms !! i = Some (getThreadR cnti).1.
        { apply (Hperms i (getThreadR cnti).1); by eexists. }
        have Hlookup : perms !! i = Some (g, (getThreadR cnti).1).
        { destruct (perms !! i) as [[g' r']|] eqn:Hp; simpl in *; try discriminate.
          f_equal.
          have Hg' : g' = g.
          { move: Hgi.
            rewrite lookup_fmap Hp /=.
            intros; by inv Hgi.
          }
          have Hr' : r' = (OrdinalPool.getThreadR cnti).1.
          { exact (Some_inj _ _ Hsnd). }
          by subst.
        }
        iDestruct (conc_mem_auth_lookup1 with "[$S]") as "H"; eauto.
        iDestruct "H" as (Hp) "[Hth Hk]".
        iApply ("Hk" $! (restrPermMap Hp)).
        iFrame.
        iPureIntro.
        repeat split.
        * apply semantics_lemmas.mem_step_refl.
        * intros ???? Hj.
          rewrite restr_Max_eq.
          specialize (Hperms j); rewrite Hj /= in Hperms.
          edestruct Hperms as [(cntj & <-) _]; first done.
          by destruct (Hcompat j cntj).
        * intros j g0 p _ Hj.
          have Hj_snd : snd <$> perms !! j = Some p by rewrite Hj /=.
          have [cntj Hcntj] := (proj1 (Hperms j p) Hj_snd).
          have Hj_lt : permMapLt (getThreadR cntj).1 (getMaxPerm m) :=
                  (ssrfun.pair_of_and (Hcompat j cntj)).1.
          by subst.
        * inv Hinvariant.
          unfold permMapsDisjoint_at; intros.
          rewrite Hlookup.
          destruct (perms !! j) as [(?,?)|] eqn: Hj; last done.
          specialize (Hperms j); rewrite Hj /= in Hperms.
          edestruct Hperms as [(cntj & <-) _]; first done; by apply no_race_thr0.
      + iApply "Hsafe".
        * iIntros "!>" (?? (-> & ?)%lookup_seq ?) "(% & Hsafe)".
          iExists g0.
          iDestruct "Hsafe" as "(% & Hthr)".
          change (0 + k) with k in *.
          iSplit; auto.
          iPureIntro.
          rewrite lookup_fmap lookup_insert_ne //.
          by rewrite lookup_fmap in H3.
          iDestruct "Hthr" as (cntk) "Hthr".
          iExists (OrdinalPool.cntUpdate (Sem:=Sem) (Krun q_new)
                   (HybridMachineSig.add_block Hcompat cnti m') cnti cntk).
          rewrite gsoThreadCode // gsoThreadRes //.
        * rewrite lookup_fmap lookup_insert /= /thread_safe.
          iExists g.
          iSplit; auto.
          iExists (OrdinalPool.cntUpdate (Sem:=Sem) (Krun q_new)
                     (HybridMachineSig.add_block Hcompat cnti m') cnti cnti).
          rewrite gssThreadCode // gssThreadRes // /m'.
          iApply (jsafe_perm_equiv with "Hsafei").
          set Hlt:=proj1 (Hcompat i cnti).
          eapply Equivalence_Symmetric; eauto.
          eapply mem_equiv.getCur_restr.
          (* Unshelve
             9 : { exact mem_equiv.access_map_equiv_Equivalence. *) 
      + iApply (step_fupdN_mono with "IH"); iPureIntro; intros Hsafe.
        eapply HybridMachineSig.HybridCoarseMachine.CoreSafe with (tr := []); simpl;
          rewrite seq.cats0; last apply Hsafe.
        change (i :: sch) with (HybridMachineSig.yield (i :: sch)) at 2.
        change m' with (HybridMachineSig.diluteMem m').
        eapply HybridMachineSig.start_step; eauto.
  Admitted.

End Safety.
