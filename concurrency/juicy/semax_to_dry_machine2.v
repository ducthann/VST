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

(* Require Import VST.msl.Coqlib2. *)

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
Require Import VST.veric.Clight_initial_world.
Require Import VST.concurrency.juicy.initial_world_with_rmap.
Require Import VST.veric.initialize.
Require Import iris_ora.algebra.gmap.
Require Import VST.concurrency.common.permjoin.
From iris_ora.algebra Require Import frac_auth.
From iris_ora.algebra Require Import gmap_view.


Import ThreadPool.
Set Bullet Behavior "Strict Subproofs".

Definition funspec_auth `{!funspecGS Σ} m :=
  own (inG0 := funspec_inG) funspec_name (gmap_view.gmap_view_auth (dfrac.DfracOwn 1) m).

Section semax_prog_with_rmap.
  Context `{!VSTGS OK_ty Σ} (OK_spec : Jext_spec Σ).

  Definition state_interp_with_rmap (m : mem) (z : OK_ty) (σ : rmap) : iProp Σ :=
    frag_mem_auth m σ ∗ ext_auth z.

  Check state_interp.
  
  Lemma semax_prog_rule_with_rmap {CS : compspecs} :
    forall V G prog m h z (σ0 : rmap),
      postcondition_allows_exit OK_spec Ctypesdefs.tint ->
      semax_prog OK_spec (C := CS) prog z V G  ->
      Genv.init_mem prog = Some m ->
      { b : Values.block & { q : CC_core &
                            (Genv.find_symbol
                               (globalenv prog) (prog_main prog) = Some b) *
      (exists m',
         semantics.initial_core (cl_core_sem (globalenv prog)) h m q m' (Vptr b Ptrofs.zero) nil) *
                              (state_interp Mem.empty σ0 z ∗ funspec_auth ∅ ∗ has_ext z
       ⊢ |==> ∃ σ : rmap,
           state_interp_with_rmap m z σ ∗
             ⌜mem_equiv.access_map_equiv (perm_of_rmap σ) (getCurPerm m)⌝ ∗
           (jsafeN OK_spec (globalenv prog) ⊤ z q ∧
            matchfunspecs (globalenv prog) G))
    } }%type.
  Proof.
    intros until σ0.
    intro EXIT.
    intros ? H1.
    generalize H; intros [? [AL [HGG [[? [GC ?]] [GV ?]]]]].
    destruct (find_id (prog_main prog) G) as [fspec |] eqn:Hfind; last first.
    rewrite Hfind in H4; try contradiction.
    assert (H4' : exists post, In (prog_main prog, main_spec_ext' prog z post) G /\
                            fspec = main_spec_ext' prog z post).
    { rewrite Hfind in H4.
      destruct H4 as [post ?].
      pose proof Hfind as Hin.
      apply find_id_e in Hin.
      exists post.
      subst fspec.
      split; auto.
    }
    clear H4.
    rename H4' into H4.
    assert (H5 : { f | In (prog_main prog, f) (prog_funct prog) }).
    forget (prog_main prog) as id.
    assert (H4' : In id (map fst G)).
    { destruct H4 as [? [H4 _]].
      apply in_map_fst in H4; auto. }
    pose proof (initialize.match_fdecs_in _ _ _ H4' H2).
    apply in_map_sig in H5.
    2: decide equality.
    destruct H5 as [[? ?] [? ?]]; subst.
    eauto.
    destruct H5 as [f H5].
    apply compute_list_norepet_e in H0.
    assert (indefs : In (prog_main prog, Gfun f) (AST.prog_defs prog)).
    { apply in_prog_funct_in_prog_defs; auto. }
    pose proof (find_funct_ptr_exists prog (prog_main prog) f) as EXx.
    apply find_symbol_funct_ptr_ex_sig in EXx; auto.
    destruct EXx as [b [Hsymbol Hfunct]]; auto.
    destruct fspec as [[params retty] cc A E P Q].
    assert (cc = cc_default /\ params = nil) as (-> & ->).
    { clear -H4; destruct H4 as [? [? ?]]; inv H0; auto. }
    assert (Hretty : retty = Ctypesdefs.tint).
    { destruct H4 as [post [? ?]]; by inv H6. }
    subst retty.
    assert (SPEP := semax_prog_entry_point OK_spec V G prog b (prog_main prog)
                      nil nil A E P Q h z EXIT H Hsymbol Hfind).
    spec SPEP.
    constructor.
    set (gargs := (filter_genv (globalenv prog), @nil val)) in *.
    cbv beta iota zeta in SPEP.
    destruct SPEP as [q [Hinit Hsafe]].
    exists b, q.
    split; [split |]; auto.
    clear Hinit.
    iIntros "((Hm & Hext) & Hf & Hz)".
    iMod (initialize_mem_with_rmap' with "[$Hm $Hf]")
      as "((%σ & Hσ & %Hperm) & Hm & Hcore & Hmatch)"; [done.. |].
    iModIntro.
    iExists σ.
    iSplitL "Hσ Hext".
    { rewrite /state_interp_with_rmap; iFrame. }
    iSplit.
    { iPureIntro; done. }
    iSplit; last done.
    destruct H4 as [post [H4 H4']].
    unfold main_spec_ext' in H4'.
    injection H4' as -> HP HQ.
    apply inj_pair2 in HP as ->.
    apply inj_pair2 in HQ as ->.
    iApply (Hsafe (initialize.globals_of_genv (filter_genv (globalenv prog)))).
    iCombine "Hcore Hmatch" as "Hcore".
    rewrite (initial_core_funassert _ V _ _ (Map.empty _) (Map.empty _)) //; iFrame.
    iIntros "!>".
    iSplit; first done.
    iApply global_initializers; eauto.
  Qed.
 
End semax_prog_with_rmap.

(* up *)
Existing Instance shared.shared_equiv.
Lemma coherent_equiv m σ1 σ2 :
  ✓ (σ1 : resource_map.rmapUR _ _ _) → σ1 ≡ σ2 → coherent m σ1 ↔ coherent m σ2.
Proof.
  intros Hv H; rewrite /coherent.
  apply Morphisms_Prop.all_iff_morphism; intros l.
  specialize (H l).
  f_equiv.
  - split; intros Hnone H1; apply Hnone in H1; rewrite H1 in H; inv H; auto.
  - rewrite /resource_at; erewrite resR_to_resource_eq; done.
Qed.

Definition can_store_at (p : access_map) (l : positive * Z) : Prop :=
  match (p # (fst l)) (snd l) with
  | Some q => perm_order q Writable
  | None   => False
  end.

Definition contents_at (m : mem) (l : positive * Z) : memval :=
  ZMap.get (snd l) ((Mem.mem_contents m) # (fst l)).

Lemma writable_at_perm_order_cases (p : access_map) (loc : positive * Z) (x : option permission) :
  can_store_at p loc -> p # (loc.1) loc.2 = x -> x = Some Freeable \/ x = Some Writable.
Proof.
  rewrite /can_store_at.
  destruct (p # (loc.1) loc.2) as [q|] eqn: Hp; [|contradiction].
  intros; destruct x as [r|]; try tauto; try discriminate.
  inv H0. inv H. by right. by left.
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

Lemma restrPermMap_Cur_eq m p (Hlt : permMapLt p (getMaxPerm m)) :
  forall b ofs, (Mem.mem_access (restrPermMap Hlt)) # b ofs Cur = p # b ofs.
Proof.
  intros b ofs.
  pose proof (mem_equiv.getCur_restr p m Hlt) as Heq.
  assert (Heq1: forall b ofs m, Maps.PMap.get b (getCurPerm m) ofs =
                          Maps.PMap.get b (Mem.mem_access m) ofs Cur).
  { rewrite /getCurPerm. intros. by rewrite Maps.PMap.gmap. }
  specialize (Heq1 b ofs (restrPermMap Hlt)).
  specialize (Heq b).
  rewrite -Heq1 Heq //.
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

Lemma permMapLt_trans (p q r : access_map): permMapLt p q -> permMapLt q r -> permMapLt p r.
Proof. intros Hpq Hqr b ofs; eapply mem_lemmas.po_trans; eauto. Qed.

Lemma can_store_at_getCurPerm_of_perm_order' (m : Mem.mem) (b : Values.block) (ofs : Z):
  Mem.perm_order' ((Mem.mem_access m) # b ofs Cur) Writable ->
  can_store_at (getCurPerm m) (b,ofs).
Proof.
  rewrite /Mem.perm_order' /can_store_at /getCurPerm /=.
  intros H; rewrite PMap.gmap.
  destruct ((Mem.mem_access m) # b ofs Cur); done.
Qed.
  
Lemma storebytes_contents_or_canstore_cur p m (Hlt : permMapLt p (getMaxPerm m))
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
  Require Import Classical_Prop.
  destruct (peq b0 b) as [-> | Hbneq].
  - destruct (classic (ofs <= ofs0 < ofs + Z.of_nat (length bytes))%Z) as [Hin | Hout].
    + right; apply can_store_at_getCurPerm_of_perm_order'; by apply Hf.
    + left; rewrite /contents_at /= PMap.gss Mem.setN_outside; auto. lia.
   - left; rewrite /contents_at PMap.gso //=.
Qed.

Local Transparent Mem.alloc.
Local Transparent Mem.storebytes.
Local Transparent Mem.free.

Lemma free_contents : forall m b lo hi m',
    Mem.free m b lo hi = Some m' -> Mem.mem_contents m' = Mem.mem_contents m.
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
  induction l as [| [[b lo] hi] tl IH]; intros; simpl in H; first inv H; auto.
  destruct (Mem.free m b lo hi) as [m1|] eqn:Hfree; try discriminate.
  specialize (IH m1 m').
  apply IH in H.
  apply free_contents in Hfree.
  rewrite -Hfree //.
Qed.

Lemma mem_contents_restrPermMap {p m} (Hlt : permMapLt p (getMaxPerm m)) :
  Mem.mem_contents (restrPermMap Hlt) = Mem.mem_contents m.
Proof. reflexivity. Qed.

Lemma free_preserve_disjoint_and_lt :
  forall (m m1 : mem) (b : positive) (lo hi : Z) (a : access_map),
    permMapLt a (getMaxPerm m) ->
    permMapsDisjoint (getCurPerm m) a ->
    Mem.free m b lo hi = Some m1 ->
    permMapsDisjoint (getCurPerm m1) a /\ permMapLt a (getMaxPerm m1).
Proof.
  intros m m1 b lo hi a Hlt Hdis Hfree.
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
    permMapsDisjoint (getCurPerm m') a /\ permMapLt a (getMaxPerm m').
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
        { rewrite /getCurPerm !PMap.gmap.
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

Lemma free_preserves_other_cur (q : access_map) (m m' : mem) (b : Values.block) (lo hi : Z) :
  permMapLt q (getCurPerm m) -> permMapsDisjoint (getCurPerm m) q -> Mem.free m b lo hi = Some m' ->
    permMapLt q (getCurPerm m') /\ permMapsDisjoint (getCurPerm m') q.
Proof.
    intros Hq Hdisj Hfree.
    split.
    - (* q remains below the current permissions *)
      intros b' ofs.
      destruct (q # b' ofs) as [pq |] eqn:Hq_at.
      2: { apply perm_order''_None. }
      assert (Hperm : Mem.perm m b' ofs Cur pq).
      { unfold Mem.perm.
        specialize (Hq b' ofs).
        unfold getCurPerm in Hq.
        rewrite Hq_at in Hq.
        rewrite mem_lemmas.po_oo.
        by rewrite PMap.gmap in Hq. }
      pose proof (Mem.perm_free_inv m b lo hi m' Hfree b' ofs Cur pq Hperm) as Hinv.
      destruct Hinv as [[Hb Hin] | Hperm'].
      + subst b'.
        (* A successful free requires Freeable here. *)
        exfalso.
        unfold permMapLt in Hq.
        specialize (Hq b ofs).
        rewrite Hq_at in Hq.
        pose proof (Mem.free_range_perm _ _ _ _ _ Hfree) as Hfreeable.
        specialize (Hfreeable ofs Hin).
        unfold permMapsDisjoint in Hdisj.
        specialize (Hdisj b ofs).
        destruct Hdisj as (pu & Hdisj).
        rewrite Hq_at in Hdisj.
        unfold getCurPerm in Hdisj.
        rewrite PMap.gmap in Hdisj.
        destruct ((Mem.mem_access m) # b ofs Cur) as [pm |] eqn:Hm.
        * unfold Mem.perm, Mem.perm_order' in Hfreeable.
          rewrite Hm in Hfreeable.
          assert (pm = Freeable) as ->.
          { destruct pm; inversion Hfreeable; reflexivity. }
          simpl in Hdisj. done.
        * unfold Mem.perm, Mem.perm_order' in Hfreeable.
          by rewrite Hm in Hfreeable.
      + unfold getCurPerm.
        rewrite PMap.gmap.
        by rewrite perm_access /access_at /= in Hperm'.
    - (* Removing permissions preserves disjointness. *)
      unfold permMapsDisjoint in *.
      intros b' ofs.
      specialize (Hdisj b' ofs).
      pose proof (Mem.free_result _ _ _ _ _ Hfree) as Hres.
      rewrite Hres.
      unfold getCurPerm.
      rewrite PMap.gmap.
      unfold Mem.unchecked_free; simpl.
      unfold getCurPerm in Hdisj.
      rewrite PMap.gmap in Hdisj.
      rewrite PMap.gsspec.
      destruct (peq b' b) as [-> | Hneq].
      + destruct (zle lo ofs && zlt ofs hi).
        * exists (q # b ofs); simpl; done.
        * done.
      + done.
  Qed.

  Lemma free_list_preserves_other_cur (q : access_map) :
    forall (l : list (Values.block * Z * Z)) (m m' : mem),
      permMapLt q (getCurPerm m) -> permMapsDisjoint (getCurPerm m) q ->
      Mem.free_list m l = Some m' ->
      permMapLt q (getCurPerm m') /\ permMapsDisjoint (getCurPerm m') q.
  Proof.
    induction l as [| [[b lo] hi] l IH]; intros m m' Hq Hdisj Hfree; simpl in Hfree.
    - inv Hfree; split; assumption.
    - destruct (Mem.free m b lo hi) as [m1 |] eqn:Hfree1; try discriminate.
      pose proof (free_preserves_other_cur q m m1 b lo hi Hq Hdisj Hfree1) as (Hq1 & Hdisj1).
      eapply IH; eauto.
  Qed.

  Lemma permMapLt_free_list_other (p q : access_map) (m m' : mem)
    (Hlt : permMapLt p (getMaxPerm m)) (l : list (Values.block * Z * Z)) :
    permMapLt q p -> permMapsDisjoint p q -> Mem.free_list (restrPermMap Hlt) l = Some m' ->
    permMapLt q (getCurPerm m').
  Proof.
    intros Hqp Hdisj Hfree.
    pose proof (free_list_preserves_other_cur q l (restrPermMap Hlt) m') as Hpres.
    apply Hpres; auto.
    - pose proof (mem_equiv.getCur_restr _ _ Hlt) as Heq.
      rewrite /mem_equiv.access_map_equiv in Heq.
      unfold permMapLt in Hqp |- *.
      intros.
      specialize (Heq b).
      specialize (Hqp b ofs).
      rewrite Heq //.
    - unfold permMapsDisjoint in Hdisj |- *.
      intros.
      specialize (Hdisj b ofs).
      destruct Hdisj as (pu & Hdisj).
      pose proof (mem_equiv.getCur_restr _ _ Hlt) as Heq.
      rewrite /mem_equiv.access_map_equiv in Heq.
      specialize (Heq b).
      rewrite Heq; eexists; done.
  Qed.

  Lemma access_map_equiv_permMapLt (p q : access_map) :
    mem_equiv.access_map_equiv p q -> permMapLt p q.
  Proof. intros Heq b ofs; rewrite (Heq b); apply po_refl. Qed.

  Lemma coherent_mem_step_other_aux (m m' : mem) (p : access_map) (σ : rmap)
    (Hp : permMapLt p (getMaxPerm m))
    (Hσ : permMapLt (perm_of_rmap σ) (getMaxPerm m))
    (Hσ' : permMapLt (perm_of_rmap σ) (getMaxPerm m')) :
    coherent (restrPermMap Hσ) σ -> mem_step (restrPermMap Hp) m' ->
    permMapsDisjoint p (perm_of_rmap σ) ->
    coherent (restrPermMap Hσ') σ.
  Proof.
    intros Hchr Hstep Hother.
    remember (restrPermMap Hp) as ms eqn:Hsrc in Hstep.
    revert Hσ'.
    generalize dependent m.
    generalize dependent p.
    induction Hstep; intros; subst; last first.
    have Hcur : mem_equiv.access_map_equiv (getCurPerm (restrPermMap Hp)) p.
    { apply mem_equiv.getCur_restr. }
    have Hmid : permMapsDisjoint (getCurPerm m'') (perm_of_rmap σ) /\
          permMapLt (perm_of_rmap σ) (getMaxPerm m'').
    { eapply (mem_step_preserve_disjoint_and_lt (restrPermMap Hp) m'' (perm_of_rmap σ)); eauto.
      - by rewrite restr_Max_eq.
      - rewrite /mem_equiv.access_map_equiv in Hcur.
        rewrite /permMapsDisjoint in Hother |- *.
        intros b ofs.
        specialize (Hcur b).
        rewrite Hcur.
        apply (Hother b ofs).
    }
    destruct Hmid as (Hother'' & Hσ'').
    have Hchr'' : coherent (restrPermMap Hσ'') σ.
    { eapply (IHHstep1 p Hother m0 Hp Hσ Hchr eq_refl Hσ''); eauto. }
    eapply (IHHstep2 (getCurPerm m'') Hother'' m'' (cur_lt_max m'') Hσ'' Hchr'').
    symmetry.
    apply restrPermMap_eq.
    - unfold coherent in *.
      intros.
      specialize (Hchr loc).
      split.
      + intro Hge.
        apply Hchr.
        assert (Hnxt: Mem.nextblock m' = Mem.nextblock m0).
        { apply (mem_lemmas.nextblock_freelist l (restrPermMap Hp) m'); auto. }
        rewrite restrPermMap_nextblock in Hge.
        rewrite restrPermMap_nextblock.
        by rewrite Hnxt in Hge.
      + unfold coherent_loc in *.
        split.
        * rewrite /contents_cohere /juicy_mem.contents_at /=.
          intros.
          rewrite /coherent in Hchr.
          destruct Hchr as (? & Hchr).
          rewrite /coherent_loc /contents_cohere in Hchr.
          destruct Hchr as (Hchr & ?).
          destruct (peq (loc.1) (Mem.nextblock m0)) as [Heq1 | Hneq].
          { rewrite /resource_at in H0.
            destruct (σ !! loc) eqn: E; last first.
            { rewrite E in H0. inv H0. }
            rewrite restrPermMap_nextblock in H1.
            rewrite Heq1 in H1.
            assert (Hge: (Mem.nextblock m0 >= Mem.nextblock m0)%positive) by lia.
            apply H1 in Hge. inv Hge.
          }
          apply Hchr in H0.
          rewrite /juicy_mem.contents_at in H0.
          apply free_list_contents in H.
          rewrite mem_contents_restrPermMap in H0.
          by rewrite H mem_contents_restrPermMap.
        * rewrite /access_cohere.
          Unshelve.
          rewrite /coherent in Hchr.
          destruct Hchr as (? & ? & ?).
          rewrite /access_cohere in H2.
          rewrite access_at_restrPermMap_Cur in H2.
          rewrite access_at_restrPermMap_Cur.
          done.
       - (* Alloc *)
         rewrite /Mem.alloc /= in H.
         injection H as Hxy.
         pose proof (f_equal Mem.mem_access (eq_sym Hxy)) as Hacc.
         simpl in Hacc.
         assert (mem_equiv.access_map_equiv (getCurPerm (restrPermMap Hp)) p).
         { apply mem_equiv.getCur_restr. }
         pose proof (f_equal Mem.mem_contents (eq_sym Hxy)) as Hcnt.
         simpl in Hcnt.
         pose proof (f_equal Mem.nextblock (eq_sym Hxy)) as Hnxt.
         simpl in Hnxt.
         clear Hxy.
         unfold coherent in *.
         intros.
         specialize (Hchr loc).
         split.
         + intro Hge.
           apply Hchr.
           rewrite restrPermMap_nextblock in Hge.
           rewrite /coherent in Hchr.
           rewrite restrPermMap_nextblock.
           subst; lia.
         + rewrite /coherent_loc.
           split.
           ** rewrite /contents_cohere restrPermMap_contents /juicy_mem.contents_at /=.
              intros.
              rewrite /coherent in Hchr.
              destruct Hchr as (? & Hchr).
              rewrite /coherent_loc /contents_cohere in Hchr.
              destruct Hchr as (Hchr & ?).
              destruct (peq (loc.1) (Mem.nextblock m0)) as [Heq1 | Hneq].
              { destruct (σ !! loc) eqn: E; last first.
                { rewrite /resource_at in H1.
                  rewrite E in H1. inv H1.
                }
                rewrite restrPermMap_nextblock in H2.
                rewrite Heq1 in H2.
                assert (Hge: (Mem.nextblock m0 >= Mem.nextblock m0)%positive) by lia.
                by apply H2 in Hge.
              }
              apply Hchr in H1.
              rewrite /juicy_mem.contents_at mem_contents_restrPermMap in H1.
              rewrite Hcnt.
              rewrite PMap.gso //.
           ** rewrite /access_cohere access_at_restrPermMap_Cur.
              rewrite /coherent in Hchr.
              destruct Hchr as (? & ?).
              rewrite /coherent_loc in H2.
              destruct H2 as (? & ?).
              rewrite /access_cohere access_at_restrPermMap_Cur // in H3.
       - (* Mem.storebytes  *)
         pose proof H as Hst.
         pose proof H as Hst1.
         rewrite /Mem.storebytes in H.
         destruct (Mem.range_perm_dec _ _ _ _ Cur Writable) as [Hf | Hf]; last first; try done.  
         injection H as Hxy.
         pose proof (f_equal Mem.mem_access (eq_sym Hxy)) as Hacc.
         simpl in Hacc.
         assert (Hcur : getCurPerm m' = getCurPerm (restrPermMap Hp)).
         { rewrite /getCurPerm.
           rewrite Hacc. done. }
         assert (Hmax : getMaxPerm m' = getMaxPerm (restrPermMap Hp)).
         { by rewrite /getMaxPerm Hacc. }
         pose proof (f_equal Mem.mem_contents (eq_sym Hxy)) as Hcnt.
         simpl in Hcnt.
         pose proof (f_equal Mem.nextblock (eq_sym Hxy)) as Hnxt.
         simpl in Hnxt.
         clear Hxy.
         unfold coherent in *.
         intros.
         split; auto.
         + intros. apply Hchr; auto; simpl in *; rewrite Hnxt // in H.
         + unfold Mem.range_perm, Mem.perm in Hf.
           assert (Hloc: forall loc, contents_at m' loc = contents_at (restrPermMap Hp) loc
                                     \/ can_store_at (getCurPerm (restrPermMap Hp)) loc).
           { eapply storebytes_contents_or_canstore_cur; eauto. }
           destruct (Hchr loc) as (_ & Hcoh).
           destruct (Hloc loc) as [Hmem_eq | Hwrite].
           * rewrite /contents_at in Hmem_eq.
             rewrite /coherent_loc /contents_cohere /resource_at /juicy_mem.contents_at
               in Hcoh |- *.
             split; simpl.
             intros.
             rewrite Hmem_eq mem_contents_restrPermMap.
             rewrite mem_contents_restrPermMap in Hcoh.
             apply Hcoh; auto.
             rewrite /access_cohere !access_at_restrPermMap_Cur in Hcoh |- *.
             apply Hcoh.
           * rewrite / coherent_loc in Hcoh |- *.
             rewrite /contents_cohere /access_cohere /= in Hcoh |- *.
             rewrite ! access_at_restrPermMap_Cur in Hcoh |- *.
             split; try apply Hcoh.
             intros ? Hres.
             destruct Hcoh as (Hv & _); specialize (Hv _ Hres).
             rewrite !restrPermMap_contents in Hv |- *.
             rewrite /resource_at /resR_to_resource in Hres.
             rewrite /permMapsDisjoint in Hother.
             specialize (Hother loc.1 loc.2).
             destruct (σ !! loc) eqn: E; last first.
             { rewrite E in Hres. inv Hres. } 
             rewrite E /= in Hres.
             destruct s; last first. inv Hres.
             rewrite /resource_at in Hchr.
             specialize (Hchr loc).
             destruct Hchr as (_ & _ & HpermHlt1).
             rewrite E in HpermHlt1.
             apply writable_at_perm_order_cases
               with (x := access_at (restrPermMap Hp) loc Cur) in Hwrite; auto.
             2 : { by rewrite /getCurPerm /access_at PMap.gmap. }
             rewrite /access_at in Hwrite.
             rewrite restrPermMap_Cur_eq in Hwrite.
             pose proof (access_at_restrPermMap_Cur (perm_of_rmap σ) m0 loc Hσ) as Haccess1.
             rewrite /access_cohere Haccess1 in HpermHlt1.
             assert (Hread: Mem.perm_order' ((perm_of_rmap σ) # (loc.1) loc.2) Readable).
             { rewrite mem_lemmas.po_oo.
               eapply readable_dfrac_perm_order with (Hlt:= Hσ) (rsh := rsh) ; try eauto.
               rewrite Haccess1 HpermHlt1.
               apply po_refl.
             }
             assert (Hwrite1: Mem.perm_order' (p # (loc.1) loc.2) Writable).
             { destruct Hwrite as [Hwrite | Hwrite];
                 rewrite mem_lemmas.po_oo; rewrite Hwrite;
                 [try apply perm_F_any | apply perm_refl].
             }
             assert (¬ ∃ pu : option permission,
                    perm_union ((perm_of_rmap σ) # (loc.1) loc.2) (p # (loc.1) loc.2) = Some pu).
             { apply (perm_order_clash ((perm_of_rmap σ) # (loc.1) loc.2) (p # (loc.1) loc.2)); auto. }
             rewrite perm_union_comm // in H.
  Qed.

Lemma permMapLt_decay_disjoint (pmap : access_map) (m m' : mem) (Hdecay : decay m m')
  (Hltp : permMapLt pmap (getMaxPerm m)) (Hdisj : permMapsDisjoint (getCurPerm m) pmap) :
  permMapLt pmap (getMaxPerm m').
Proof.
  intros b ofs.
  destruct (mem_lemmas.valid_block_dec m b) as [Hvalid | Hinvalid].
  - destruct (Hdecay b ofs) as [_ Hold].
    specialize (Hold Hvalid).
    destruct Hold as [Hfree | Hsame].
    + (* The step freed this location. *)
      assert (Hpnone : pmap # b ofs = None).
      { specialize (Hdisj b ofs) as [pu Hunion].
        rewrite getCurPerm_correct in Hunion.
        unfold permission_at in Hunion.
        destruct (Hfree Cur) as [Hfree_cur _].
        rewrite Hfree_cur in Hunion.
        destruct (pmap # b ofs) as [p |] eqn:Hp; last auto.
        destruct p; simpl in Hunion; discriminate.
      }
      rewrite Hpnone.
      apply perm_order''_None.
    + (* Maximum permission is unchanged. *)
      specialize (Hsame Max).
      specialize (Hltp b ofs).
      rewrite getMaxPerm_correct in Hltp |- *.
      unfold permission_at in Hltp |- *.
      rewrite Hsame in Hltp.
      rewrite getMaxPerm_correct //.
  - (* σ0 has no permission on an initially invalid block. *)
    assert (Hpnone : pmap # b ofs = None).
    { eapply permMapLt_invalid_block; eauto. }
    rewrite Hpnone.
    apply perm_order''_None.
Qed.
(*
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
  CSL_init_mem_not_none : Genv.init_mem CSL_prog <> None; }.

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
    destruct (Genv.init_mem (CSL_prog CPROOF)); last done; eauto.
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
                          apply ext_link_inj in H1 as <-; auto | clear H0]); last done.
  Qed.

  (* funspecs_destruct isn't working well, so prove a spec lemma for each function *)
  Ltac next_spec := subst; let Hspecs := fresh "Hspecs" in match goal with |-context[add_funspecs_rec _ _ _ ?l] =>
    destruct l eqn: Hspecs; first done;
    injection Hspecs; clear Hspecs; intros Hspecs <-; simpl;
    unfold funspec2pre, funspec2post, ef_id_sig; simpl; if_tac end.

  Ltac solve_spec x :=
    intros; revert x; unfold ext_spec_post, concurrent_ext_spec; pose proof ext_link_inj as Hinj;
    fold ext_link in Hinj; repeat (next_spec; first absurd_ext_link_naming); next_spec; last done;
    let y := fresh "x" in
    intros y;
    iSplit;
    [ iIntros "H"; iExists y; iSplit; [ iPureIntro; apply JMeq.JMeq_refl | iExact "H" ]
    | iIntros "H"; iDestruct "H" as (x'') "[%Heq H]"; let Heq0 := fresh "Heq0" in let Heq' := fresh "Heq'" in inversion Heq as [Heq0 Heq']; apply inj_pair2 in Heq'; subst; iExact "H" ].

  Lemma CEspec_acquire_pre `{!VSTGS unit Σ, !lockGS Σ}
    (x : Jext_spec_type (concurrent_ext_spec CS ext_link) LOCK)
    (args : list val) :
    Jext_spec_pre (concurrent_ext_spec CS ext_link) LOCK x (genv_symb_injective ge) (sig_args (ef_sig LOCK)) args ⊣⊢
      match acquire_spec with
      | mk_funspec _ _ A _ P _ =>
          ∃ x'',
    ⌜JMeq.JMeq x x''⌝ ∧ funspec2pre' A P x'' (genv_symb_injective ge) (sig_args (ef_sig LOCK)) args
  end.
  Proof. solve_spec x. Qed.

  Lemma CEspec_acquire_post `{!VSTGS unit Σ, !lockGS Σ} (x : Jext_spec_type (concurrent_ext_spec CS ext_link) LOCK) (ret : option val) :
    Jext_spec_post (concurrent_ext_spec CS ext_link) LOCK x (genv_symb_injective ge) (sig_res (ef_sig LOCK)) ret ⊣⊢
      match acquire_spec with
      | mk_funspec _ _ A _ _ Q => ∃ x'', ⌜JMeq.JMeq x x''⌝ ∧ funspec2post' A Q x'' (genv_symb_injective ge) (sig_res (ef_sig LOCK)) ret
  end.
  Proof. solve_spec x. Qed.

  Lemma CEspec_release_pre `{!VSTGS unit Σ, !lockGS Σ}
    (x : Jext_spec_type (concurrent_ext_spec CS ext_link) UNLOCK) (args : list val) :
  Jext_spec_pre (concurrent_ext_spec CS ext_link) UNLOCK x (genv_symb_injective ge) (sig_args (ef_sig UNLOCK)) args ⊣⊢
  match release_spec with
  | mk_funspec _ _ A _ P _ => ∃ x'', ⌜JMeq.JMeq x x''⌝ ∧ funspec2pre' A P x'' (genv_symb_injective ge) (sig_args (ef_sig UNLOCK)) args end.
  Proof. solve_spec x. Qed.

  Lemma CEspec_release_post `{!VSTGS unit Σ, !lockGS Σ}
    (x : Jext_spec_type (concurrent_ext_spec CS ext_link) UNLOCK) (ret : option val) :
  Jext_spec_post (concurrent_ext_spec CS ext_link) UNLOCK x (genv_symb_injective ge) (sig_res (ef_sig UNLOCK)) ret ⊣⊢
  match release_spec with
  | mk_funspec _ _ A _ _ Q => ∃ x'', ⌜JMeq.JMeq x x''⌝ ∧ funspec2post' A Q x'' (genv_symb_injective ge) (sig_res (ef_sig UNLOCK)) ret end.
  Proof. solve_spec x. Qed.

  Lemma CEspec_makelock_pre `{!VSTGS unit Σ, !lockGS Σ}
    (x : Jext_spec_type (concurrent_ext_spec CS ext_link) MKLOCK) (args : list val) :
  Jext_spec_pre (concurrent_ext_spec CS ext_link) MKLOCK x (genv_symb_injective ge) (sig_args (ef_sig MKLOCK)) args ⊣⊢
  match makelock_spec CS with
  | mk_funspec _ _ A _ P _ => ∃ x'', ⌜JMeq.JMeq x x''⌝ ∧
        funspec2pre' A P x'' (genv_symb_injective ge) (sig_args (ef_sig MKLOCK)) args end.
  Proof. solve_spec x. Qed.

  Lemma CEspec_makelock_post `{!VSTGS unit Σ, !lockGS Σ}
    (x : Jext_spec_type (concurrent_ext_spec CS ext_link) MKLOCK) (ret : option val) :
    Jext_spec_post (concurrent_ext_spec CS ext_link) MKLOCK x (genv_symb_injective ge) (sig_res (ef_sig MKLOCK)) ret ⊣⊢
      match makelock_spec CS with
      | mk_funspec _ _ A _ _ Q => ∃ x'', ⌜JMeq.JMeq x x''⌝ ∧ funspec2post' A Q x'' (genv_symb_injective ge) (sig_res (ef_sig MKLOCK)) ret end.
  Proof. solve_spec x. Qed.

  Lemma CEspec_freelock_pre `{!VSTGS unit Σ, !lockGS Σ}
    (x : Jext_spec_type (concurrent_ext_spec CS ext_link) FREE_LOCK) (args : list val) :
    Jext_spec_pre (concurrent_ext_spec CS ext_link) FREE_LOCK x (genv_symb_injective ge) (sig_args (ef_sig FREE_LOCK)) args ⊣⊢
      match freelock_spec CS with
      | mk_funspec _ _ A _ P _ => ∃ x'', ⌜JMeq.JMeq x x''⌝ ∧ funspec2pre' A P x'' (genv_symb_injective ge) (sig_args (ef_sig FREE_LOCK)) args end.
  Proof. solve_spec x. Qed.

  Lemma CEspec_freelock_post `{!VSTGS unit Σ, !lockGS Σ}
    (x : Jext_spec_type (concurrent_ext_spec CS ext_link) FREE_LOCK) (ret : option val) :
    Jext_spec_post (concurrent_ext_spec CS ext_link) FREE_LOCK x (genv_symb_injective ge) (sig_res (ef_sig FREE_LOCK)) ret ⊣⊢
      match freelock_spec CS with
      | mk_funspec _ _ A _ _ Q => ∃ x'', ⌜JMeq.JMeq x x''⌝ ∧ funspec2post' A Q x'' (genv_symb_injective ge) (sig_res (ef_sig FREE_LOCK)) ret end.
  Proof. solve_spec x. Qed.

  Lemma CEspec_spawn_pre `{!VSTGS unit Σ, !lockGS Σ}
    (x : Jext_spec_type (concurrent_ext_spec CS ext_link) CREATE) (args : list val) :
    Jext_spec_pre (concurrent_ext_spec CS ext_link) CREATE x (genv_symb_injective ge) (sig_args (ef_sig CREATE)) args ⊣⊢
      match spawn_spec with | mk_funspec _ _ A _ P _ => ∃ x'',
        ⌜JMeq.JMeq x x''⌝ ∧ funspec2pre' A P x'' (genv_symb_injective ge) (sig_args (ef_sig CREATE)) args end.
  Proof. solve_spec x. Qed.

  Lemma CEspec_spawn_post `{!VSTGS unit Σ, !lockGS Σ}
    (x : Jext_spec_type (concurrent_ext_spec CS ext_link) CREATE) (ret : option val) :
    Jext_spec_post (concurrent_ext_spec CS ext_link) CREATE x (genv_symb_injective ge) (sig_res (ef_sig CREATE)) ret ⊣⊢
      match spawn_spec with | mk_funspec _ _ A _ _ Q => ∃ x'',
        ⌜JMeq.JMeq x x''⌝ ∧ funspec2post' A Q x'' (genv_symb_injective ge) (sig_res (ef_sig CREATE)) ret end.
  Proof. solve_spec x. Qed.

  (* Program Definition spr (HH : VSTGS unit Σ) (HL : lockGS Σ) :=
    semax_prog_rule (concurrent_ext_spec CS ext_link) V G prog
      (proj1_sig init_mem) 0 tt _ (all_safe HH HL) (proj2_sig init_mem).
  Next Obligation.
  Proof. intros; iIntros (??); done. Qed. *)

  Program Definition spr (HH : VSTGS unit Σ) (HL : lockGS Σ) (σ0 : rmap) :=
    semax_prog_rule_with_rmap (concurrent_ext_spec CS ext_link) V G prog
      (proj1_sig init_mem) 0 tt σ0 _ (all_safe HH HL) (proj2_sig init_mem).
  Next Obligation. Proof. intros; iIntros (??); done. Qed.
 
  Instance Sem : Semantics :=
    ClightSemanticsForMachines.ClightSem (Clight.globalenv CPROOF.(CSL_prog)).
  
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
  Definition raw_rmapUR : uora := resource_map.rmapUR share address (leibnizO resource).

  Definition raw_rmapR : cmra := ora_cmraR (uora_oraR raw_rmapUR).

  Definition rmap_authUR : uora := frac_authUR raw_rmapR.

Section conc_heap.
  Context `{HH: !VSTGS unit Σ} `{!lockGS Σ} `{rmap_inG : inG Σ rmap_authUR}.

  (* Definition rmap_authUR : ora := resource_map.rmap_authR share address (leibnizO resource).

  Definition rmap_auth `{rmap_inG : inG Σ rmap_authUR}
    (γ : gname) (σ : resource_map.rmapUR share address (leibnizO resource)) : iProp Σ :=
    @own Σ rmap_authUR rmap_inG γ (●{dfrac.DfracOwn (1%Qp)} σ).

  Definition rmap_frag `{rmap_inG : inG Σ rmap_authUR}
    (γ : gname) (σ : resource_map.rmapUR share address (leibnizO resource)) : iProp Σ :=
    @own Σ rmap_authUR rmap_inG γ (◯ σ). *)

  

  Definition rmap_auth `{rmap_inG : inG Σ rmap_authUR} (γ : gname) (σ : rmap) : iProp Σ :=
    @own Σ rmap_authUR rmap_inG γ (@frac_auth_auth raw_rmapR σ).

  Definition rmap_frag `{rmap_inG : inG Σ rmap_authUR} (γ : gname) (q : Qp) (σ : rmap) : iProp Σ :=
    @own Σ rmap_authUR rmap_inG γ (@frac_auth_frag raw_rmapR q σ).

  (* Definition thread_mem_auth `{rmap_inG : inG Σ rmap_authUR} (q : Qp) (σ : rmap) (γ : gname) : iProp Σ := rmap_frag γ q σ. *)

  Lemma resource_map_auth_combine (γ : gname) (q1 q2 : Qp) (m1 m2 : resource_map.rmapUR share address (leibnizO resource)) :
    resource_map.resource_map_auth (H1 := gen_heapGpreS_heap (gen_heapGpreS := gen_heap_inG))
      γ q1 m1 ∗
    resource_map.resource_map_auth (H1 := gen_heapGpreS_heap (gen_heapGpreS := gen_heap_inG))
      γ q2 m2 ⊢
    ⌜m1 ≡ m2⌝ ∧ resource_map.resource_map_auth (H1 := gen_heapGpreS_heap (gen_heapGpreS := gen_heap_inG)) γ (q1 + q2) m1.
  Proof.
    iIntros "(H1 & H2)".
    iDestruct (resource_map.resource_map_auth_valid_2 with "H1 H2") as %(_ & Heq).
    rewrite resource_map.resource_map_auth_unseal /resource_map.resource_map_auth_def.
    iSplit; try done.
    rewrite Heq.
    iCombine "H1 H2" as "H".
    rewrite -own_op -auth_auth_dfrac_op dfrac.dfrac_op_own; done.
  Qed.
  
  (* Lemma frag_mem_auth1_combine q1 q2 m σ1 σ2:
    frag_mem_auth m σ1 ∗ frag_mem_auth m σ2 ⊢ ⌜σ1 ≡ σ2⌝ ∧ frag_mem_auth (q1 + q2) m σ1.
  Proof.
    rewrite /frag_mem_auth.
    iIntros "((%Hm1 & H1) & (%Hm2 & H2))".
    iDestruct (resource_map_auth_combine with "[$H1 $H2]") as "(% & H)"; try done.
    iSplit; try done.
    iSplit; try done.
  Qed. *)

  Lemma rmap_frag_op `{!inG Σ rmap_authUR} γ q1 q2 (σ1 σ2 : raw_rmapR) :
    rmap_frag γ (q1 + q2) (σ1 ⋅ σ2) ⊣⊢ rmap_frag γ q1 σ1 ∗ rmap_frag γ q2 σ2.
  Proof. by rewrite /rmap_frag -own_op frac_auth_frag_op. Qed.

  (* Lemma frag_mem_auth1_split q1 q2 m σ :
    frag_mem_auth (q1 + q2) m σ ⊢ frag_mem_auth q1 m σ ∗ frag_mem_auth q2 m σ.
  Proof.
    rewrite /frag_mem_auth resource_map.resource_map_auth_unseal /resource_map.resource_map_auth_def.
    iIntros "(%Hmem & Hauth)".
    rewrite -(dfrac_op_own q2 q1) auth_auth_dfrac_op own_op.
    iDestruct "Hauth" as "(Hauth1 & Hauth2)".
    iSplitL "Hauth1"; iSplit; try done.
  Qed. *)
    
  (* Lemma thread_mem_auth_combine `{!inG Σ rmap_authUR} q1 q2 (σ1 σ2 : raw_rmapR) γ :
    thread_mem_auth q1 σ1 γ ∗ thread_mem_auth q2 σ2 γ ⊣⊢
      thread_mem_auth (q1 + q2) (σ1 ⋅ σ2) γ.
  Proof.
    by rewrite /thread_mem_auth rmap_frag_op.
  Qed. *)

  (*
    Definition thread_state_interp γ q m σ z : iProp Σ :=
  ∃ τ : rmap,
    (⌜coherent m τ ∧
       mem_equiv.access_map_equiv
         (perm_of_rmap σ) (getCurPerm m)⌝
     ∧ resource_map.resource_map_auth
         (gen_heap_name heapGS_gen_heapGS) 1 τ) ∗
    rmap_auth γ σ ∗
    rmap_frag γ q σ ∗
    ext_auth z.

   *)

  Definition thread_state_interp `{!inG Σ rmap_authUR} γ
    (p : access_map) (q : Qp) m (σ : rmap) z : iProp Σ :=
    ∃ σ0 : rmap, ⌜mem_equiv.access_map_equiv (perm_of_rmap σ) p⌝ ∧
      frag_mem_auth m σ0 ∗ rmap_auth γ σ0 ∗ rmap_frag γ q σ ∗ ext_auth z.

  (* Definition frag_state_interp (m : mem) (σ : rmap) z : iProp Σ :=
    frag_mem_auth m σ ∗ ext_auth z. *)
  
  Lemma locks_init `{InGlock : !inG Σ (gmap_view.gmap_viewR address (later (iPropO Σ)))} (m : mem) :
    ⊢ |==> ∃ HL : lockGS Σ, ∀ heapGS0 : heapGS Σ, @lock_state Σ heapGS0 HL m (∅ : gset address).
  Proof.
    iMod (own_alloc (A := gmap_view.gmap_viewR address (laterO (iPropO Σ)))
            (gmap_view.gmap_view_auth (dfrac.DfracOwn 1)
               (∅ : gmap address (laterO (iPropO Σ))))) as (γ) "Hauth".
    { apply gmap_view.gmap_view_auth_valid. }
    iModIntro.
    iExists (LockGS Σ InGlock γ).
    iIntros (heapGS0).
    unfold lock_state, semax_conc_pred.lock_state.
    iExists (∅ : gmap address mpred).
    rewrite fmap_empty big_sepM_empty /=.
    iFrame.
    iPureIntro; split; auto.
    rewrite /lock_addresses_disjoint; set_solver.
  Qed.

  Definition gen_heap_meta_auth (HG : gen_heapGS share address resource Σ) : iProp Σ :=
    @ghost_map.ghost_map_auth Σ address gname _ _
      (@gen_heapGpreS_meta share address resource Σ _ _ _
         (@gen_heap_inG share address resource Σ _ _ _ HG))
      (@gen_meta_name share address resource Σ _ _ _ HG)
      1 (∅ : gmap address gname).

  Lemma init_conc_VST_frag : forall Z `{VSTGpreS0 : !VSTGpreS Z Σ} (z : Z),
      ⊢ |==> ∀ Hinv : invGS_gen HasNoLc Σ,
        ∃ (HG : gen_heapGS share address resource Σ) (FS : funspecGS Σ) (ES : externalGS Z Σ) (HL : lockGS Σ) (γ : gname) (σ : rmap),
          @state_interp Σ Z HG ES Mem.empty σ z ∗
            rmap_auth γ σ ∗ rmap_frag γ 1 σ ∗
            @funspec_auth Σ FS (∅ : gmap address funspecO') ∗
            @has_ext Z Σ ES z ∗
            @lock_state Σ
            ({| heapGS_invGS := Hinv;
               heapGS_gen_heapGS := HG;
               heapGS_funspecGS := FS |} : heapGS Σ) HL Mem.empty (∅ : gset address) ∗
            gen_heap_meta_auth HG.
  Proof.
    intros; iIntros.
    iMod gen_heap_init_names_empty as (γh γmeta) "(Hheap & Hmeta)".
    iMod (own_alloc (A := gmap_view.gmap_viewR address (@funspecO' Σ))
            (gmap_view.gmap_view_auth (dfrac.DfracOwn 1) ∅)) as (γf) "Hfunspec".
    { apply gmap_view.gmap_view_auth_valid. }
    iMod (ext_alloc z) as (ES) "(Hextauth & Hhasext)".
    iMod (locks_init Mem.empty) as (HL) "Hlocks".
    iMod (own_alloc (A := rmap_authUR) ((@frac_auth_auth raw_rmapR (∅ : rmap)) ⋅
            (@frac_auth_frag raw_rmapR 1%Qp (∅ : rmap)))) as (γ) "Hrmap".
    { apply frac_auth_valid. done. }
    iModIntro.
    iIntros (Hinv).
    pose (HG := {| gen_heap_inG := VSTGpreS_heap; gen_heap_name := γh; gen_meta_name := γmeta |}).
    pose (FS := FunspecG _ _ γf).
    pose (HGS := ({| heapGS_invGS := Hinv; heapGS_gen_heapGS := HG; heapGS_funspecGS := FS |} : heapGS Σ)).
    iSpecialize ("Hlocks" $! HGS).
    iExists HG, FS, ES, HL, γ, (∅ : rmap).
    rewrite /gen_heap_meta_auth /=.
    rewrite /rmap_auth /rmap_frag.
    rewrite own_op.
    iDestruct "Hrmap" as "(Hauth & Hfrag)".
    iFrame.
    iPureIntro.
    pose proof (empty_coherent Mem.empty).
    split; auto.
  Qed.

  Lemma frag_mem_auth_corestep_other (q : Qp) (m m' : mem) (p : access_map) (σ : rmap)
    (Hp : permMapLt p (getMaxPerm m)) (Hσ : permMapLt (perm_of_rmap σ) (getMaxPerm m))
    (Hσ' : permMapLt (perm_of_rmap σ) (getMaxPerm m')):
    mem_step (restrPermMap Hp) m' -> permMapsDisjoint p (perm_of_rmap σ) ->
    frag_mem_auth (restrPermMap Hσ) σ -∗ frag_mem_auth (restrPermMap Hσ') σ.
  Proof.
    intros Hstep Hdisj.
    rewrite /frag_mem_auth.
    iIntros "(%Hlt & %Hcoh & Hfrag)".
    have Hrestr_old : restrPermMap Hlt = restrPermMap Hσ.
    { etransitivity.
      - apply restrPermMap_idem.
      - apply restr_proof_irr; reflexivity.
    }
    have Hcoh_old : coherent (restrPermMap Hσ) σ.
    { by rewrite <- Hrestr_old. }
    have Hcoh_new : coherent (restrPermMap Hσ') σ.
    { eapply coherent_mem_step_other_aux; eauto. }
    have Hlt0 : permMapLt (perm_of_rmap σ) (getMaxPerm (restrPermMap Hσ')).
    { by rewrite restr_Max_eq. }
    iExists Hlt0.
    iSplit; iFrame.
    rewrite (restrPermMap_idem Hlt0).
    replace (permMapLt_restr Hlt0) with Hσ'
      by apply ProofIrrelevance.proof_irrelevance.
    done.
  Qed.

  Lemma coherent_perm_of_rmap m σ :
    coherent m σ -> permMapLt (perm_of_rmap σ) (getCurPerm m).
  Proof.
    intros Hcoh b ofs.
    specialize (Hcoh (b, ofs)).
    rewrite /coherent_loc /access_cohere in Hcoh.
    destruct Hcoh as (_ & _ & ?).
    rewrite /access_at /= in H.
    rewrite perm_of_rmap_lookup /getCurPerm PMap.gmap // H.
    apply po_refl.
  Qed.

  Lemma coherent_perm_of_rmap_max m σ :
    coherent m σ -> permMapLt (perm_of_rmap σ) (getMaxPerm m).
  Proof.
    intros Hcoh.
    assert (Hcur: permMapLt (perm_of_rmap σ) (getCurPerm m)).
    { by apply coherent_perm_of_rmap. }
    etransitivity; eauto.
    apply mem_cur_lt_max.
  Qed.

  Definition rmap_included (σi σ : rmap) : Prop :=
    ((σi : resource_map.rmapUR share address (leibnizO resource)) ≼
       (σ : resource_map.rmapUR share address (leibnizO resource))).

  Definition rmap_local_update (σ σi σ' σi' : rmap) : Prop :=
    @local_update (resource_map.rmapUR share address (leibnizO resource)) (σ, σi) (σ', σi').

  (** jsafe_frag_pre **)
  (* Program Definition jsafe_frag_pre (γ : gname) q (jsafe : coPset -d> unit -d> CC_core -d> iPropO Σ) :
    coPset -d> unit -d> CC_core -d> iPropO Σ := λ E z c,
     |={E}=>
    ∀ (m : mem) (σ : rmap),
      thread_state_interp γ q m σ z -∗
      (* Hlt is derived from the current fragment state. *)
       ∃ (Hlt : permMapLt (perm_of_rmap σ) (getMaxPerm m)),
      (∃ i, ⌜halted (cl_core_sem ge) c i⌝ ∧ (*frag_state_interp_1 q m σ z ∗ *)
        Jext_spec_exit (concurrent_ext_spec CS ext_link) (Some (Vint i))) ∨
      
      (|={E}=> ∃ c' m' σ',
          ⌜corestep (cl_core_sem ge) c (restrPermMap Hlt) c' m'⌝ ∧
            thread_state_interp γ q m' σ' z ∗ ▷ jsafe E z c') ∨
      
      (∃ e args x σ1, ⌜at_external (cl_core_sem ge) c (restrPermMap Hlt) = Some (e, args)⌝ ∧
                        thread_state_interp γ q m σ1 z ∗
          Jext_spec_pre (concurrent_ext_spec CS ext_link) e x
          (genv_symb_injective ge) (sig_args (ef_sig e)) args ∗
        ▷ (∀ ret m' σ' z' (*(Hlt' : permMapLt (perm_of_rmap σ') (getMaxPerm m')) *),
            ⌜Val.has_type_list args (sig_args (ef_sig e)) ∧ Builtins0.val_opt_has_rettype ret (sig_res (ef_sig e))⌝ →
            |={E}=> thread_state_interp γ q m' σ' z' -∗
            Jext_spec_post (concurrent_ext_spec CS ext_link) e x (genv_symb_injective ge)
              (sig_res (ef_sig e)) ret -∗
            ∃ c' σ2, ⌜after_external (cl_core_sem ge) ret c m' = Some c'⌝ ∧
                       thread_state_interp γ q m' σ2 z' ∗ jsafe E z' c')). *)

  Program Definition jsafe_frag_pre (γ : gname) q (jsafe : coPset -d> unit -d> CC_core -d> iPropO Σ) :
    coPset -d> unit -d> CC_core -d> iPropO Σ := λ E z c,
     |={E}=>
      ∀ (m : mem) (σ : rmap) (p : access_map),
      thread_state_interp γ p q m σ z -∗
      (* Hlt is derived from the current fragment state. *)
       ∃ (Hlt : permMapLt (perm_of_rmap σ) (getMaxPerm m)),
      (∃ i, ⌜halted (cl_core_sem ge) c i⌝ ∧ (*frag_state_interp_1 q m σ z ∗ *)
        Jext_spec_exit (concurrent_ext_spec CS ext_link) (Some (Vint i))) ∨
      
      (|={E}=> ∃ c' m' σ',
          ⌜corestep (cl_core_sem ge) c (restrPermMap Hlt) c' m'⌝ ∧
            thread_state_interp γ (getCurPerm m') q m' σ' z ∗ ▷ jsafe E z c') ∨
      
      (∃ e args x, ⌜at_external (cl_core_sem ge) c (restrPermMap Hlt) = Some (e, args)⌝ ∧
                        thread_state_interp γ p q m σ z ∗
          Jext_spec_pre (concurrent_ext_spec CS ext_link) e x
          (genv_symb_injective ge) (sig_args (ef_sig e)) args ∗
        ▷ (∀ ret m' σ' z' (*(Hlt' : permMapLt (perm_of_rmap σ') (getMaxPerm m')) *),
            ⌜Val.has_type_list args (sig_args (ef_sig e)) ∧ Builtins0.val_opt_has_rettype ret (sig_res (ef_sig e))⌝ →
            |={E}=> thread_state_interp γ (getCurPerm m') q m' σ' z' -∗
            Jext_spec_post (concurrent_ext_spec CS ext_link) e x (genv_symb_injective ge)
              (sig_res (ef_sig e)) ret -∗
            ∃ c', ⌜after_external (cl_core_sem ge) ret c m' = Some c'⌝ ∧
                    thread_state_interp γ (getCurPerm m') q m' σ' z' ∗ jsafe E z' c')).

  (*
  Program Definition jsafe_frag_pre (γ : gname) q (jsafe : coPset -d> unit -d> CC_core -d> iPropO Σ) :
    coPset -d> unit -d> CC_core -d> iPropO Σ := λ E z c,
     |={E}=>
    ∀ (m : mem) (σ : rmap),
      thread_state_interp γ q m σ z -∗
      (* Hlt is derived from the current fragment state. *)
       ∃ (Hlt : permMapLt (perm_of_rmap σ) (getMaxPerm m)),
      (∃ i, ⌜halted (cl_core_sem ge) c i⌝ ∧ (*frag_state_interp_1 q m σ z ∗ *)
        Jext_spec_exit (concurrent_ext_spec CS ext_link) (Some (Vint i))) ∨
      
      (|={E}=> ∃ c' m' σ',
          ⌜corestep (cl_core_sem ge) c (restrPermMap Hlt) c' m'⌝ ∧
            thread_state_interp γ q m' σ' z ∗ ▷ jsafe E z c') ∨
      
        (∃ e args x, ⌜at_external (cl_core_sem ge) c (restrPermMap Hlt) = Some (e, args)⌝ ∧
                          thread_state_interp γ q m σ z ∗
          Jext_spec_pre (concurrent_ext_spec CS ext_link) e x
          (genv_symb_injective ge) (sig_args (ef_sig e)) args ∗
        ▷ (∀ ret m' σ' z' (*(Hlt' : permMapLt (perm_of_rmap σ') (getMaxPerm m')) *),
            ⌜Val.has_type_list args (sig_args (ef_sig e)) ∧ Builtins0.val_opt_has_rettype ret (sig_res (ef_sig e))⌝ →
            |={E}=> thread_state_interp γ q m' σ' z' -∗
            Jext_spec_post (concurrent_ext_spec CS ext_link) e x (genv_symb_injective ge)
              (sig_res (ef_sig e)) ret -∗
            ∃ c' σ2, ⌜after_external (cl_core_sem ge) ret c m' = Some c'⌝ ∧
                       thread_state_interp γ q m' σ2 z' ∗ jsafe E z' c')).



  Program Definition jsafe_frag_pre (γ : gname) q (jsafe : coPset -d> unit -d> CC_core -d> iPropO Σ) :
    coPset -d> unit -d> CC_core -d> iPropO Σ := λ E z c,
     |={E}=>
    ∀ (m : mem) (σ : rmap),
      thread_state_interp γ q m σ z -∗
      (* Hlt is derived from the current fragment state. *)
       ∃ (Hlt : permMapLt (perm_of_rmap σ) (getMaxPerm m)),
      (∃ i, ⌜halted (cl_core_sem ge) c i⌝ ∧ (*frag_state_interp_1 q m σ z ∗ *)
        Jext_spec_exit (concurrent_ext_spec CS ext_link) (Some (Vint i))) ∨
      
      (|={E}=> ∃ c' m' σ',
          ⌜corestep (cl_core_sem ge) c (restrPermMap Hlt) c' m'⌝ ∧
            thread_state_interp γ q m' σ' z ∗ ▷ jsafe E z c') ∨
      
        (∃ e args x, ⌜at_external (cl_core_sem ge) c (restrPermMap Hlt) = Some (e, args)⌝ ∧
          Jext_spec_pre (concurrent_ext_spec CS ext_link) e x
          (genv_symb_injective ge) (sig_args (ef_sig e)) args ∗
          ▷ (∀ ret m' (*σ' *) z' (*(Hlt' : permMapLt (perm_of_rmap σ') (getMaxPerm m')) *),
            ⌜Val.has_type_list args (sig_args (ef_sig e)) ∧ Builtins0.val_opt_has_rettype ret (sig_res (ef_sig e))⌝ →
            |={E}=> (*thread_state_interp γ q m' σ' z' -∗ *)
            Jext_spec_post (concurrent_ext_spec CS ext_link) e x (genv_symb_injective ge)
              (sig_res (ef_sig e)) ret -∗
            ∃ c' σ2, ⌜after_external (cl_core_sem ge) ret c m' = Some c'⌝ ∧
                       thread_state_interp γ q m' σ2 z' ∗ jsafe E z' c')). *)

  

  Local Instance jsafe_frag_pre_contractive γ q : Contractive (jsafe_frag_pre γ q).
  Proof.
    rewrite /jsafe_frag_pre => n jsafe jsafe' Hsafe E z c.
    repeat first [f_contractive | f_equiv]; try apply Hsafe.
  Qed.

  Local Definition jsafe_frag_def (γ : gname) (q : Qp): coPset -> unit -> CC_core -> iProp Σ :=
    fixpoint (jsafe_frag_pre γ q).
  Local Definition jsafe_frag_aux γ q: seal (jsafe_frag_def γ q). Proof. by eexists. Qed.
  Definition jsafe_frag (γ : gname) (q : Qp) := (jsafe_frag_aux γ q).(unseal).
  Local Lemma jsafe_frag_unseal γ q : jsafe_frag γ q = jsafe_frag_def γ q .
  Proof. rewrite -(jsafe_frag_aux γ q).(seal_eq) //. Qed.

  Lemma jsafe_frag_unfold γ q E z c :
    jsafe_frag γ q E z c ⊣⊢ jsafe_frag_pre γ q (jsafe_frag γ q) E z c.
  Proof.
    rewrite jsafe_frag_unseal.
    apply (fixpoint_unfold (jsafe_frag_pre γ q)).
  Qed.

  Lemma rmap_auth_frag_agree `{!inG Σ rmap_authUR} γ (σ0 σ : raw_rmapR) :
    rmap_auth γ σ0 ∗ rmap_frag γ 1 σ ⊢ ⌜σ0 ≡ σ⌝.
  Proof.
    iIntros "(Hauth & Hfrag)".
    rewrite /rmap_auth /rmap_frag.
    iCombine "Hauth Hfrag" as "Hboth".
    rewrite -own_op.
    iPoseProof (own_valid with "Hboth") as "Hvalid".
    iDestruct (frac_auth_agree_fullI σ0 σ with "Hvalid") as "%"; try done.
  Qed.

  Lemma resource_map_auth_equiv (γh : gname) (q : Qp) (σ1 σ2 : rmap) :
    σ1 ≡ σ2 ->
    resource_map.resource_map_auth (S := share) (K := address) (V := resource) (Σ := Σ)
      (H1 := gen_heapGpreS_heap (gen_heapGpreS := gen_heap_inG)) γh q σ1 ⊣⊢
    resource_map.resource_map_auth (S := share) (K := address) (V := resource) (Σ := Σ)
      (H1 := gen_heapGpreS_heap (gen_heapGpreS := gen_heap_inG)) γh q σ2.
  Proof.
    intros Heq.
    rewrite /resource_map.resource_map_auth (seal_eq resource_map.resource_map_auth_aux).
    apply own_proper.
    by f_equiv.
  Qed.

  Lemma perm_of_rmap_equiv1 σ1 σ2 :
    ✓ (σ1 : resource_map.rmapUR share address (leibnizO resource)) →
    σ1 ≡ σ2 → (perm_of_rmap σ1) = (perm_of_rmap σ2).
  Proof.
    intros Hvalid Hσ.
    assert (Hdom : dom σ1 = dom σ2).
    { apply leibniz_equiv; rewrite dom_proper; done. }
    assert (Hrow : ∀ b, perm_row_of_rmap σ1 b = perm_row_of_rmap σ2 b).
    { intro b.
      apply functional_extensionality; intro ofs.
      unfold perm_row_of_rmap, resource_at.
      erewrite resR_to_resource_eq; done. }
    unfold perm_of_rmap.
    assert (Hfold :
             forall (f : address -> access_map -> access_map) (m1 m2 : rmap),
               dom m1 = dom m2 ->
               foldr (fun '(loc, _) (p : access_map) => f loc p)
                 (PMap.init (fun _ : Z => None)) (map_to_list m1) =
                 foldr (fun '(loc, _) (p : access_map) => f loc p)
                   (PMap.init (fun _ : Z => None)) (map_to_list m2)).
    { intros f m1 m2 Hdom0.
      revert m2 Hdom0.
      induction m1 as [|k v m1 Hnotin Hfirst IH] using map_first_key_ind; intros m2 Hdom0.
      - rewrite dom_empty_L in Hdom0.
        symmetry in Hdom0; apply dom_empty_inv_L in Hdom0 as ->.
        rewrite !map_to_list_empty; reflexivity.
      - assert (k ∈ dom m2) as (v2 & Hk2)%elem_of_dom.
        { rewrite <- Hdom0.
          rewrite dom_insert_L. clear -Hdom0 Hdom. set_solver. }
        assert (HnotinDom : k ∉ dom m1).
        { apply not_elem_of_dom_2; exact Hnotin. }

        assert (Hdom1 : dom m1 = dom (delete k m2)).
        { rewrite dom_delete_L -Hdom0 dom_insert_L. clear -HnotinDom. set_solver. }
        assert (Hfirst2 : map_first_key m2 k).
        { apply (proj1 (map_first_key_dom_L _ _ _ Hdom0)). done. }
        rewrite (map_to_list_insert_first_key m1 k v Hnotin Hfirst).
        rewrite (map_to_list_delete_first_key m2 k v2 Hk2 Hfirst2).
        simpl.
        f_equal.
        apply IH; done. }
    assert (Hf :
             ((fun '(loc, _) (p : access_map) =>
                 PMap.set loc.1 (perm_row_of_rmap σ1 loc.1) p)
               : (address * shared.shared (leibnizO resource)) ->
                 access_map -> access_map) =
               ((fun '(loc, _) (p : access_map) =>
                   PMap.set loc.1 (perm_row_of_rmap σ2 loc.1) p)
                 : (address * shared.shared (leibnizO resource)) ->
                   access_map -> access_map)).
    { apply functional_extensionality; intro x.
      destruct x as [loc v].
      apply functional_extensionality; intro p.
      by rewrite (Hrow loc.1). }
    rewrite Hf.
    by apply Hfold.
  Qed.

  (* Lemma thread_state_interp_1_to_state_interp γ p m σ z:
    thread_state_interp γ p 1 m σ z ⊢ state_interp m σ z ∗ rmap_frag γ 1 σ.
  Proof.
    iIntros "H".    
    iDestruct "H" as (σ0) "(%Hp & Hmem & Hauth & Hfrag & Hext)".
    iDestruct "Hmem" as (Hlt) "(%Hcoh & Hmem)".
    iDestruct (rmap_auth_frag_agree γ σ0 σ with "[$Hauth $Hfrag]") as "%Heq".
    iDestruct (resource_map.resource_map_auth_valid with "Hmem") as %(_ & Hvalid).
    assert (Hperm : perm_of_rmap σ0 = perm_of_rmap σ).
    { eapply perm_of_rmap_equiv1; eauto. }
    assert (Hlt' : permMapLt (perm_of_rmap σ) (getMaxPerm m)).
    { by rewrite <- Hperm. }
    assert (Hrestr : restrPermMap Hlt = restrPermMap Hlt').
    { by apply restrPermMap_irr'. }
    assert (Hcoh' : coherent (restrPermMap Hlt') σ).
    { rewrite <- Hrestr.
      by apply (coherent_equiv (restrPermMap Hlt) σ0 σ Hvalid Heq). }
    iSplitR "Hfrag".
    - rewrite /state_interp /mem_rmap_auth.
      iFrame "Hext".
      
      
    unfold mem_rmap_auth.
      iExists Hlt'.

    
      exact Hperm.
    }
      exact Hlt.
    }

    
    }
    iFrame.

    
    assert (Hcoh' : coherent (restrPermMap Hlt') σ).
    {
      rewrite <- Hrestr.
      apply
        (proj1
           (coherent_equiv
              (restrPermMap Hlt) σ0 σ Hvalid Heq)).
      exact Hcoh.
    }
    unfold frag_mem_auth.
    iDestruct "Hmem" as (Hlt) "(%Hcoh & Hmem)".
    iDestruct (rmap_auth_frag_agree γ σ0 σ with "[$Hauth $Hfrag]") as "%Heq".
    iDestruct (resource_map.resource_map_auth_valid with "Hmem") as %(_ & Hvalid).
    iFrame.
    unfold mem_rmap_auth.
    Search coherent.
    assert (Hcoh' : coherent m σ).
    { by apply (proj1 (coherent_equiv m σ0 σ Hvalid Heq)). }
    iSplitR "Hfrag"; iFrame.
    rewrite /state_interp /mem_rmap_auth.
    iSplit; auto.
    rewrite resource_map_auth_equiv; auto.
  Qed. 

  Lemma state_interp_with_rmap_to_thread γ m z σ :
    state_interp_with_rmap m z σ ∗ rmap_auth γ σ ∗ rmap_frag γ 1 σ ⊢
      thread_state_interp γ (getCurPerm m) 1 m σ z.
  Proof.
    rewrite /state_interp_with_rmap /thread_state_interp.
    iIntros "((Hmem & Hext) & Hauth & Hfrag)".
    iDestruct "Hmem" as "((%Hcoh & %Hperm) & Hmem)".
    iExists σ.
    iSplit; auto.
    iFrame.
    iSplit; auto.
  Qed. *)

  Lemma getCurPerm_access_at (m : mem) (b : positive) (ofs : Z) :
    (getCurPerm m) # b ofs = (Mem.mem_access m) # b ofs Cur.
  Proof. rewrite /getCurPerm /= PMap.gmap //=. Qed.

  Lemma access_at_Cur_of_mem_equiv (m1 m2 : mem) (loc : address) :
    mem_equiv.mem_equiv m1 m2 -> access_at m1 loc Cur = access_at m2 loc Cur.
  Proof.
    intros Heqv.
    destruct Heqv as [Hcur Hmax Hcnt Hnb].
    rewrite /mem_equiv.Cur_equiv /mem_equiv.access_map_equiv in Hcur.
    rewrite /access_at - !getCurPerm_access_at.
    specialize (Hcur loc.1).
    rewrite Hcur //.
  Qed.

  Lemma access_at_cur_getCurPerm m b ofs :
    access_at m (b, ofs) Cur = (getCurPerm m) # b ofs.
  Proof. rewrite /access_at /getCurPerm /= PMap.gmap //. Qed.

  Lemma access_at_restrPermMap_perm_res m s
    (Hlt : permMapLt (perm_of_rmap s) (getMaxPerm m)) b ofs :
    access_at (restrPermMap Hlt) (b, ofs) Cur = perm_of_res (s @ (b, ofs)).
  Proof.
    rewrite / access_at.
    replace ((b, ofs).1) with b by auto.
    replace ((b, ofs).2) with ofs by auto.
    change ((Mem.mem_access (restrPermMap Hlt)) # b ofs Cur)
      with (permission_at (restrPermMap Hlt) b ofs Cur).
    rewrite restrPermMap_Cur perm_of_rmap_lookup //.
  Qed.

  Lemma coherent_restrPermMap m (s : rmap) (Hlt : permMapLt (perm_of_rmap s) (getMaxPerm m)) :
    coherent m s -> coherent (restrPermMap Hlt) s.
  Proof.
    unfold coherent in *.
    intros Hcoh (b & ofs).
    destruct (Hcoh (b, ofs)) as (Hnb & Hloc).
    split.
    - intros Hge; apply Hnb; auto.
    - unfold coherent_loc in *.
      destruct Hloc as (Hcontents & Haccess).
      split.
      + unfold contents_cohere in *.
        intros v Hv.
        by apply Hcontents.
      + unfold access_cohere.
        rewrite access_at_restrPermMap_perm_res //.
  Qed.

  Lemma coherent_restrPermMap_of_coherent m s:
    coherent m s ->
    exists (Hlt : permMapLt (perm_of_rmap s) (getMaxPerm m)), coherent (restrPermMap Hlt) s.
  Proof.
    intros.
    assert (Hlt : permMapLt (perm_of_rmap s) (getMaxPerm m)).
    { intros b ofs.
      unfold coherent in H.
      destruct (H (b, ofs)) as [_ Hloc].
      rewrite perm_of_rmap_lookup.
      unfold coherent_loc in Hloc.
      destruct Hloc as [_ Hperm].
      unfold access_cohere in Hperm.
      eapply juicy_mem.perm_order''_trans.
      - apply getCur_Max.
      - rewrite /access_at /= in Hperm.
        rewrite PMap.gmap Hperm; apply po_refl.
    }
    exists Hlt.
    by apply coherent_restrPermMap.
  Qed.

  Lemma coherent_of_restrPermMap_coherent m σ σ1
    (Hlt : permMapLt (perm_of_rmap σ) (getMaxPerm m)):
    coherent m σ -> coherent (restrPermMap Hlt) σ1 -> coherent m σ1.
  Proof.
    intros Hcoh_m Hcoh_restr.
    unfold coherent in *.
    intros (b & ofs).
    destruct (Hcoh_m (b, ofs)) as [Hnb [Hcontents Haccess]].
    destruct (Hcoh_restr (b, ofs)) as [Hnb1 [Hcontents1 Haccess1]].
    split.
    - intros Hb.
      apply Hnb1.
      by rewrite restrPermMap_nextblock.
    - split.
      + unfold contents_cohere in *.
        intros v Hv.
        by apply Hcontents1.
      + unfold access_cohere in *.
        rewrite -Haccess1 /access_at restrPermMap_Cur_eq perm_of_rmap_lookup //.
  Qed.

  (* Lemma frag_state_interp_1_to_state_interp_restr m σ z
    (Hlt : permMapLt (perm_of_rmap σ) (getMaxPerm m)) :
    frag_state_interp m σ z -∗ state_interp (restrPermMap Hlt) z.
  Proof.
    rewrite /frag_state_interp /frag_mem_auth /state_interp /mem_auth.
    iIntros "(((%Hcoh & %Heq) & Hauth) & Hext)".
    iFrame; iPureIntro; split; auto; apply coherent_restrPermMap; auto.
  Qed. *)

  
  Lemma resource_map_auth_increase γ s s' : ✓ s' -> s ≼ s' ->
    resource_map.resource_map_auth
      (H1 := gen_heapGpreS_heap (gen_heapGpreS := gen_heap_inG)) γ 1 s ==∗
    resource_map.resource_map_auth
      (H1 := gen_heapGpreS_heap (gen_heapGpreS := gen_heap_inG)) γ 1 s'.
  Proof.
    intros Hvalid Hinc.
    destruct Hinc as (δ & Hδ).
    iIntros "Hauth".
    rewrite resource_map.resource_map_auth_unseal.
    unfold resource_map.resource_map_auth_def.
    iMod (own_update _
            (●{dfrac.DfracOwn 1} s
              : authR (resource_map.rmapUR share address (leibnizO resource)) _)
            (●{dfrac.DfracOwn 1} s'
              : authR (resource_map.rmapUR share address (leibnizO resource)) _)
           with "[$Hauth]") as "Hauth".
    { eapply auth_update_auth with (b' := δ).
      rewrite Hδ.
      rewrite (comm op s δ).
      setoid_replace δ with (δ ⋅ ε) at 2 by (rewrite right_id; done).
      eapply op_local_update.
      intros n _.
      rewrite comm.
      rewrite -Hδ.
      by apply cmra_valid_validN. }
    iModIntro. iFrame.
  Qed.

  
  Lemma coherent_access_map_equiv (m : mem) (σ : rmap) :
    coherent m σ -> mem_equiv.access_map_equiv (perm_of_rmap σ) (getCurPerm m).
  Proof.
    intros Hcoh b; extensionality ofs.
    rewrite perm_of_rmap_lookup.
    destruct (Hcoh (b, ofs)) as [_ [_ Hacc]].
    rewrite /access_cohere access_at_cur_getCurPerm // in Hacc.
  Qed.

  

  Lemma perm_of_rmap_equiv σ1 σ2 :
    ✓ (σ1 : resource_map.rmapUR share address (leibnizO resource)) →
    σ1 ≡ σ2 → mem_equiv.access_map_equiv (perm_of_rmap σ1) (perm_of_rmap σ2).
  Proof.
    intros Hvalid Hσ b.
    apply functional_extensionality.
    intros ofs.
    rewrite !perm_of_rmap_lookup.
    rewrite /resource_at.
    pose proof (proj1 (@equiv_dist (resource_map.rmapUR share address (leibnizO resource)) σ1 σ2) Hσ) as Hσdist.
    f_equal.
    eapply resR_to_resource_eq.
    - apply (Hvalid (b, ofs)).
    - apply equiv_dist.
      intros n.
      eapply (@gmap.lookup_ne address _ _ (shared.sharedR (leibnizO resource)) (b, ofs) n).
      done.
  Qed.

  Lemma resR_to_resource_included_perm_order
    (x y : cmra.optionR (shared.sharedR (leibnizO resource))) :
    ✓ y → x ≼ y →
    Mem.perm_order'' (perm_of_res (resR_to_resource y)) (perm_of_res (resR_to_resource x)).
  Proof.
    intros Hy Hxy.
    eapply perm_of_res_mono'.
    - destruct y as [sy |].
      + rewrite resR_to_resource_fst /=.
        rewrite Some_valid in Hy.
        apply shared.shared_valid in Hy as [Hd _]; auto.
      + rewrite resR_to_resource_fst /=.
        apply ucmra_unit_valid.
    - eapply resR_le; eauto.
  Qed.

  Lemma rmap_included_permMapLt σi σ m :
    ✓ (σ : resource_map.rmapUR share address (leibnizO resource)) →
    rmap_included σi σ → permMapLt (perm_of_rmap σ) (getMaxPerm m) →
    permMapLt (perm_of_rmap σi) (getMaxPerm m).
  Proof.
    intros.
    etransitivity; last exact H1.
    intros b ofs.
    rewrite !perm_of_rmap_lookup.
    eapply resR_to_resource_included_perm_order; eauto.
    rewrite /rmap_included in H0.
    apply ((proj1 (@gmap.lookup_included address _ _ (shared.sharedR (leibnizO resource)) σi σ) H0) (b, ofs)).
   Qed.

  Lemma rmap_auth_frag_agreeI `{!inG Σ rmap_authUR} γ (σ0 σ : raw_rmapR) :
    rmap_auth γ σ0 ∗ rmap_frag γ 1 σ ⊢ ⌜σ0 ≡ σ⌝.
  Proof.
    iIntros "(Hauth & Hfrag)".
    rewrite /rmap_auth /rmap_frag.
    iCombine "Hauth Hfrag" as "Hboth".
    rewrite -own_op.
    iDestruct (own_valid_r with "Hboth") as "[Hboth Hvalid]".
    by iDestruct (frac_auth_agree_fullI with "Hvalid") as "%Heq".
  Qed.

  Lemma rmap_auth_frag_set_q `{!inG Σ rmap_authUR} γ (q : Qp) (σ0 σ σ1 : raw_rmapR) :
    ✓ σ1 → rmap_auth γ σ0 ∗ rmap_frag γ q σ ==∗ rmap_auth γ σ1 ∗ rmap_frag γ q σ1.
  Proof.
    intros Hvalid.
    rewrite /rmap_auth /rmap_frag.
    iIntros "(Hauth & Hfrag)".
    iMod (own_update_2 with "Hauth Hfrag") as "[$ $]".
    { apply frac_auth_update.
      Search local_update.
      eapply exclusive_local_update; eauto. }
    done.
    
      
  Abort.

  Lemma rmap_auth_frag_set `{!inG Σ rmap_authUR} γ (σ0 σ σ1 : raw_rmapR) (Hv : ✓ σ1) :
    rmap_auth γ σ0 ∗ rmap_frag γ 1 σ ==∗ rmap_auth γ σ1 ∗ rmap_frag γ 1 σ1.
  Proof.
    rewrite /rmap_auth /rmap_frag -!own_op.
    iIntros "H".
    iApply (own_update with "H").
    by apply frac_auth_update_1.
  Qed.

  Lemma mem_rmap_auth_equiv (m : mem) (σ1 σ2 : rmap)
    (Hv : ✓ (σ1 : resource_map.rmapUR share address (leibnizO resource))) (Heq : σ1 ≡ σ2) :
    mem_rmap_auth m σ1 ⊣⊢ mem_rmap_auth m σ2.
  Proof.
    rewrite /mem_rmap_auth.
    iSplit; iIntros "(%Hcoh & Hauth)"; iSplit; try iPureIntro;
      try by apply (coherent_equiv m σ1 σ2 Hv Heq).
    - by rewrite (resource_map_auth_equiv (gen_heap_name heapGS_gen_heapGS) 1%Qp σ1 σ2 Heq).
    - by rewrite (resource_map_auth_equiv (gen_heap_name heapGS_gen_heapGS) 1%Qp σ1 σ2 Heq).
  Qed.

  (* Lemma thread_state_interp_open γ p m σ z :
    thread_state_interp γ p 1 m σ z ⊢
      (mem_rmap_auth m σ ∗ ext_auth z) ∗
      ((mem_rmap_auth m σ ∗ ext_auth z) -∗ thread_state_interp γ p 1 m σ z).
  Proof.
    iIntros "H".
    iDestruct "H" as (σ0) "(%Hp & Hmem & Hauth & Hfrag & Hext)".
    iDestruct "Hmem" as "((%Hcoh & %Hacc) & Hrm)".
    iDestruct (resource_map.resource_map_auth_valid with "[$Hrm]") as %(_ & Hvσ1).
    iDestruct (rmap_auth_frag_agreeI _ σ0 σ with "[$Hauth $Hfrag]") as "%Heq".
    iAssert (mem_rmap_auth m σ) with "[Hrm]" as "Hstate".
    { rewrite /mem_rmap_auth.
      iSplit; try by rewrite -(coherent_equiv m σ0 σ).
      by rewrite (resource_map_auth_equiv _ 1 σ0 σ). }
    iFrame "Hstate Hext".
    iIntros "(Hstate & Hext)".
    iAssert (mem_rmap_auth m σ0) with "[Hstate]" as "Hstate".
    { rewrite -(mem_rmap_auth_equiv m σ0 σ); auto. }
    iDestruct "Hstate" as "(_ & Hrm)".
    iExists σ0.
    iFrame.
    iSplit; auto.
  Qed. *)

  Lemma coherent_of_restrPermMap_access_equiv m σ (Hlt : permMapLt (perm_of_rmap σ) (getMaxPerm m)) :
    coherent (restrPermMap Hlt) σ -> mem_equiv.access_map_equiv (perm_of_rmap σ) (getCurPerm m) ->
    coherent m σ.
  Proof.
    intros Hcoh Hacc (b & ofs).
    specialize (Hcoh (b, ofs)).
    destruct Hcoh as (Hnb & Hcontents & Haccess).
    split.
    - intros Hb.
      apply Hnb.
      by rewrite restrPermMap_nextblock.
    - split.
      + intros v Hv.
        specialize (Hcontents v Hv).
        by rewrite <- (restrPermMap_contents Hlt).
      + unfold access_cohere.
        rewrite access_at_cur_getCurPerm.
        rewrite <- perm_of_rmap_lookup.
        rewrite /mem_equiv.access_map_equiv in Hacc.
        specialize (Hacc b).
        by rewrite Hacc.
  Qed.

  Lemma rmap_auth_equiv_local γ (σ1 σ2 : rmap) :
    σ1 ≡ σ2 ->
    rmap_auth γ σ1 ⊣⊢ rmap_auth γ σ2.
  Proof.
    intros Heq.
    rewrite /rmap_auth.
    apply own_proper.
    f_equiv.
    exact Heq.
  Qed.
    
  Lemma jsafe_jsafe_frag (γ : gname): forall E z c,
      jsafe (genv_symb := genv_symb_injective) (cl_core_sem ge) (concurrent_ext_spec CS ext_link) ge E z c
        ⊢ jsafe_frag γ 1 E z c.
  Proof.
    intros.
    iLöb as "IH" forall (z c).
    rewrite jsafe_unfold jsafe_frag_unfold /jsafe_pre /jsafe_frag_pre.
    iIntros ">H !>" (m σ p) "S".
    rewrite /thread_state_interp.
    iDestruct "S" as (σ0) "(%Hp & Hmem & Hauth & Hfrag & Hext)".
    iDestruct (rmap_auth_frag_agree γ σ0 σ with "[$Hauth $Hfrag]") as "%Heq".
    unfold frag_mem_auth.
    iDestruct "Hmem" as (Hlt0) "(%Hcoh & Hmem)".
    iPoseProof (resource_map.resource_map_auth_valid with "Hmem") as "%Hv".
    destruct Hv as (_ & Hvσ0).
    assert (perm_of_rmap σ0 = perm_of_rmap σ) as Hperm_eq.
    { apply perm_of_rmap_equiv1; done. }
    assert (Hlt : permMapLt (perm_of_rmap σ) (getMaxPerm m)).
    { by rewrite <- Hperm_eq. }
    assert (Hr : restrPermMap Hlt = restrPermMap Hlt0).
    { by apply restrPermMap_irr'. }
    iExists Hlt.
    iDestruct ("H" $! (restrPermMap Hlt0) σ0 with "[$Hmem $Hext]")
      as "[Hhalt | [Hstep | Hextcase]]".
    { iSplit; auto. }
    - iLeft; iDestruct "Hhalt" as (i) "($ & _ & $)".
    - iRight; iLeft.
      iMod "Hstep" as (c' m' σ') "(%Hstep & Hstate & Hsafe)".
      iDestruct "Hstate" as "((%Hcoh1 & Hmem1) & Hext1)".
      iDestruct (resource_map.resource_map_auth_valid with "[$Hmem1]") as %(_ & Hvσ').
      iMod (rmap_auth_frag_set γ σ0 σ σ' Hvσ' with "[$Hauth $Hfrag]") as "(Hauth & Hfrag)".
      pose proof Hcoh1 as Hacc1.
      apply coherent_access_map_equiv in Hacc1.
      pose proof Hcoh1 as Hcoh1_restr.
      apply coherent_restrPermMap_of_coherent in Hcoh1_restr.
      destruct Hcoh1_restr as (Hlt1 & Hcoh1_restr).
      iModIntro.
      iExists c', m', σ'.
      iSplit; try rewrite Hr //.
      iSplitL "Hmem1 Hauth Hfrag Hext1"; last first.
      iApply ("IH" $! z c' with "Hsafe").
      iExists σ'; iFrame; iSplit; auto.
    - iRight; iRight.
      iDestruct "Hextcase" as (e args x) "(%Hat & Hstate & Hpre & Hk)".
      iDestruct "Hstate" as "((%Hcoh_cur & Hmem_cur) & Hext_cur)".
      iExists e, args, x.
      iSplit; first done.
      iSplitL "Hmem_cur Hauth Hfrag Hext_cur".
      { iExists σ0.
        iSplit; auto.
        iFrame.
        iExists Hlt0.
        iSplit; auto. }
      iSplitL "Hpre"; auto.
      iNext.
      iIntros (ret m' σ' z') "%Htypes".
      iSpecialize ("Hk" $! ret m' σ' z' with "[%]"); auto.
      iMod "Hk" as "Hk".
      iIntros "!> S Hpost".
      iDestruct "S" as (σ1) "(%Hacc & Hfragmem & Hauth1 & Hfrag1 & Hext1)".
      iDestruct "Hfragmem" as (Hlt1) "(%Hcoh1 & Hmem1)".
      iDestruct (rmap_auth_frag_agree γ σ1 σ' with "[$Hauth1 $Hfrag1]") as "%Heq1".
      iDestruct (resource_map.resource_map_auth_valid with "[$Hmem1]") as %(_ & Hvσ1).
      assert (Hacc1 : mem_equiv.access_map_equiv (perm_of_rmap σ1) (getCurPerm m')).
      { erewrite perm_of_rmap_equiv1; eauto. }
      assert (Hmeq : mem_equiv.mem_equiv (restrPermMap Hlt1) m').
      { by eapply mem_equiv.cur_equiv_restr_mem_equiv. }
      assert (Hcoh_full' : coherent m' σ').
      { apply (proj1 (coherent_equiv m' σ1 σ' Hvσ1 Heq1)).
        eapply coherent_of_restrPermMap_access_equiv; eauto. }
      rewrite (resource_map_auth_equiv _ _ σ1 σ' Heq1).
      iDestruct ("Hk" with "[$Hmem1 $Hext1] Hpost") as (c') "(%Hafter & Hstate & Hsafe)"; eauto.
      iDestruct "Hstate" as "((%Hcoh2 & Hmem2) & Hext2)".
      iAssert (rmap_auth γ σ') with "[Hauth1]" as "Hauth2".
      { by rewrite <- (rmap_auth_equiv_local γ σ1 σ' Heq1). }
      assert (Hlt2 : permMapLt (perm_of_rmap σ') (getMaxPerm m')).
      { by apply coherent_perm_of_rmap_max. }
      assert (Hcoh2_restr : coherent (restrPermMap Hlt2) σ').
      { by apply coherent_restrPermMap. }
      iExists c'.
      iSplit; first done.
      iFrame.
      iSplit; last first; try by iApply "IH".
      iPureIntro.
      split; auto.
      exists Hlt2; try done.
  Qed.
  
  Existing Instance mem_equiv.access_map_equiv_Equivalence.

  Lemma permMapLt_cur: forall p m (Hlt : permMapLt (getCurPerm p) (getCurPerm m)),
      permMapLt (getCurPerm p) (getMaxPerm m).
  Proof.
    intros.
    etrans; first apply Hlt.
    apply cur_lt_max.
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

  

  Definition access_at_nonempty (m : mem) (loc : address) : Prop :=
    access_at m loc Cur = Some Nonempty /\ access_at m loc Max = Some Nonempty.

  Definition access_at_1 (m : Mem.mem) (l : address) : forall k : perm_kind, option permission :=
    fun k => let '(b, ofs) := l in (Mem.mem_access m) # b ofs k.

  Definition nonEmptyRangeCur (m : Mem.mem) (l: Values.block * Z) : Prop :=
    forall (i : Z), (0 <= i < Z.of_nat (size_chunk_nat Mptr))%Z ->
                    (Mem.mem_access m) # (l.1) (l.2 + i)%Z Cur = Some Nonempty.

  Definition locks_coherent (tp : dtp) (m : mem) (ls : gset address) :=
    forall l,
      (l ∈ ls ->
       lockRes tp l <> None /\
         ((Mem_load_unchecked Mptr m l.1 l.2 = (Vptrofs Ptrofs.zero) /\
            lockRes tp l = Some empty_map) \/
            (Mem_load_unchecked Mptr m l.1 l.2 = (Vptrofs Ptrofs.one))) /\
      (forall i  (cnti : containsThread tp i) (Hp : permMapLt (getThreadR cnti) (getMaxPerm m)),
          nonEmptyRangeCur (restrPermMap Hp) l)).

  Lemma storebytes_contents_eq : forall m m' b ofs bytes b0,
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

  Lemma setPermBlock_sets_range (b : Values.block) (ofs : Z) (pmap0 : access_map) (n : nat) :
    forall i : Z,
      (0 <= i < Z.of_nat n)%Z ->
      (setPermBlock (Some Nonempty) b ofs pmap0 n) # b (ofs + i)%Z = Some Nonempty.
  Proof.
    induction n as [|n IH]; intros i Hi.
    - simpl in Hi; lia.
    - simpl setPermBlock.
      unfold setPerm.
      rewrite Maps.PMap.gss.
      destruct (compcert.lib.Coqlib.zeq (ofs + Z.of_nat n) (ofs + i)) as [Heq|Hneq]; try done.
      apply IH. lia.
  Qed.

  Lemma free_preserves_cur_nonempty :
    forall m m1 b lo hi (l: address),
      Mem.free m b lo hi = Some m1 -> (Mem.mem_access m) # (l.1) l.2 Cur = Some Nonempty ->
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
    forall m m', mem_step m m' ->
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
      mem_step m m' -> nonEmptyRangeCur m l ->
      Mem.getN (size_chunk_nat Mptr) l.2 ((Mem.mem_contents m)  # (l.1)) =
        Mem.getN (size_chunk_nat Mptr) l.2 ((Mem.mem_contents m') # (l.1)).
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
      pose proof H as Hfl.
      apply free_list_contents in Hfl.
      by rewrite Hfl.
  Qed.

  Lemma Mem_unchecked_restrPermMap :
    forall (m: Mem.mem) (p: access_map) (Hlt : permMapLt p (getMaxPerm m)) l,
    Mem_load_unchecked Mptr (restrPermMap Hlt) l.1 l.2 = Mem_load_unchecked Mptr m l.1 l.2.
  Proof. intros m p Hlt [b ofs]; by unfold Mem_load_unchecked. Qed.

  Lemma lock_state_empty_change m1 m2 :
    lock_state m1 ∅ ⊢ lock_state m2 ∅.
  Proof.
    iIntros "H".
    iDestruct "H" as (I) "((%Hdom & %Hdisjoint) & Hauth & HI)".
    apply dom_empty_inv_L in Hdom.
    subst I.
    iExists ∅.
    iFrame.
    iSplit; auto.
  Qed.

  Lemma lock_state_mem_change
    (m m' : mem) (ls : gset address)
    (Hload :
      forall l,
        l ∈ ls ->
        semax_conc_pred.Mem_load_unchecked Mptr m l.1 l.2 =
          semax_conc_pred.Mem_load_unchecked Mptr m' l.1 l.2) :
    lock_state m ls ⊢ lock_state m' ls.
  Proof.
    rewrite /lock_state /semax_conc_pred.lock_state.
    iIntros "Hlocks".
    iDestruct "Hlocks" as (I) "((%Hdom & %Hdisjoint) & Hauth & HRs)".
    iExists I.
    iSplit.
    { iPureIntro; split; done. }
    iFrame "Hauth".
    iApply (big_sepM_mono with "HRs").
    iIntros (l R Hl) "HR".
    assert (Hl_ls : l ∈ ls).
    { rewrite -Hdom; eapply elem_of_dom_2; eauto. }
    specialize (Hload l Hl_ls).
    iDestruct "HR" as "[[%Hone HR] | %Hzero]".
    - iLeft.
      iSplit; last iExact "HR".
      iPureIntro.
      rewrite -Hload //.
    - iRight.
      iPureIntro.
      rewrite -Hload //.
  Qed.

  Lemma coherent_perm_of_rmap_eq (m : mem) (σ1 σ2 : rmap)
    (Hcoh1 : coherent m σ1) (Hcoh2 : coherent m σ2) :
    mem_equiv.access_map_equiv (perm_of_rmap σ1) (perm_of_rmap σ2).
  Proof.
    intros b; extensionality ofs.
    destruct (Hcoh1 (b, ofs)) as (_ & _ & H1).
    destruct (Hcoh2 (b, ofs)) as (_ & _ & H2).
    unfold access_cohere in H1, H2.
    rewrite H1 in H2.
    rewrite !perm_of_rmap_lookup //.
  Qed.

  (* Lemma lock_inv_in_lock_state m ls sh l R :
    lock_state m ls -∗ lock_inv sh l R -∗ ⌜∃ l_addr, val2adr l l_addr ∧ l_addr ∈ ls⌝.
  Proof.
    iIntros "Hstate Hlock".
    iDestruct "Hstate" as (I) "((%Hdom & %Hldisj) & Hauth & _)".
    iDestruct "Hlock" as (l1) "(%Hval & _ & Hfrag)".
    iDestruct (own_valid_2 (A := gmap_view.gmap_viewR address _) with "Hauth Hfrag") as "#Hvalid".
    iDestruct (algebra.gmap_view_both_validI with "[$Hvalid]") as "(%Hvalid & #Hlookup)".
    destruct (I !! l1) as [RI |] eqn:HI.
    - iPureIntro.
      exists l1; split; auto; rewrite -Hdom elem_of_dom; by eexists.
    - rewrite lookup_fmap HI.
      iDestruct (option_equivI with "Hlookup") as "[]".
  Qed. *)

  (*
    Lemma lock_inv_acquire (q : Qp) (m : mem) (ls : gset address) (σ0 : rmap)
    (Hlt : permMapLt (perm_of_rmap σ0) (getMaxPerm m)) sh b (o : ptrofs) (R : mpred) :
  Mem_load_unchecked Mptr m b (Ptrofs.unsigned o) = Vptrofs Ptrofs.one →
  frag_mem_auth q (restrPermMap Hlt) σ0 -∗ lock_state m ls -∗ lock_inv sh (Vptr b o) R ==∗
  let m' := Mem_store_unchecked Mptr m b (Ptrofs.unsigned o) (Vptrofs Ptrofs.zero) in
  ∃ σ1 : rmap,
    (* σ1 is the rmap extracted from the lock entry. *)
    ⌜✓ (σ0 ⋅ σ1) ∧ (▷ R) σ1⌝ ∗
    ∃ Hlt' : permMapLt (perm_of_rmap (σ0 ⋅ σ1)) (getMaxPerm m'),
      frag_mem_auth q (restrPermMap Hlt') (σ0 ⋅ σ1) ∗
      lock_state m' ls ∗ lock_inv sh (Vptr b o) R ∗ ▷ R.
   *)

  
  Goal Op (resource_map.rmapUR share address (leibnizO resource)).
  Proof. apply _. Qed.
  
  Goal Valid (resource_map.rmapUR share address (leibnizO resource)).
  Proof. apply _. Qed.

  Goal ∀ σ0 σ1 : resource_map.rmapUR share address (leibnizO resource),
      ✓ (σ0 ⋅ σ1) → True.
  Proof.
    intros; exact I.
  Qed.

  Lemma rmap_frag_lock_transfer `{!inG Σ rmap_authUR} (γ : gname) (q qL : Qp) (σ σlock : raw_rmapR) :
    rmap_frag γ q σ ∗ rmap_frag γ qL σlock ⊣⊢
      rmap_frag γ q (σ ⋅ σlock) ∗ rmap_frag γ qL (∅ : raw_rmapR).
  Proof.
    rewrite /rmap_frag -!own_op.
    apply own_proper.
    rewrite -!frac_auth_frag_op.
    by rewrite right_id.
  Qed.

 (* Lemma resource_map_auth_acquire γ q1 q2 s1 s2 :
    resource_map.resource_map_auth
      (H1 := gen_heapGpreS_heap (gen_heapGpreS := gen_heap_inG))
      γ q1 s1 ∗
      resource_map.resource_map_auth
      (H1 := gen_heapGpreS_heap (gen_heapGpreS := gen_heap_inG))
      γ q2 s2
      ⊣⊢
      resource_map.resource_map_auth
      (H1 := gen_heapGpreS_heap (gen_heapGpreS := gen_heap_inG))
      γ (q1 + q2) (s1 ⋅ s2).
  Proof.
    rewrite resource_map.resource_map_auth_unseal.
    unfold resource_map.resource_map_auth_def.
    repeat rewrite -own_op.
  Admitted. *)
 
  Parameter lock_rmap_holds : mpred -> rmap -> Prop.
  Print frag_mem_auth.
  
  (* Lemma lock_inv_acquire (q : Qp) (m : mem) (ls : gset address)
    (σ0 : resource_map.rmapUR share address (leibnizO resource))
    (Hlt : permMapLt (perm_of_rmap σ0) (getMaxPerm m)) sh b (o : ptrofs) (R : mpred) :
    Mem_load_unchecked Mptr m b (Ptrofs.unsigned o) = Vptrofs Ptrofs.one →
    frag_mem_auth (restrPermMap Hlt) σ0 -∗
    lock_state m ls -∗ lock_inv sh (Vptr b o) R ==∗
    let m' := Mem_store_unchecked Mptr m b (Ptrofs.unsigned o) (Vptrofs Ptrofs.zero) in
    ∃ (σ1: (resource_map.rmapUR share address (leibnizO resource))),
      (* σ1 is the rmap extracted from the lock entry. *)
      <affine> ⌜✓(σ0 ⋅ σ1) ∧ lock_rmap_holds R σ1⌝ ∧
                         ∃ Hlt' :
                           permMapLt (perm_of_rmap (σ0 ⋅ σ1)) (getMaxPerm m'),
                           frag_mem_auth (restrPermMap Hlt') (σ0 ⋅ σ1) ∗
                             lock_state m' ls ∗
                             lock_inv sh (Vptr b o) R ∗
                             ▷ R.
  Admitted. *)

  Definition rmapAuthT : ora := resource_map.rmap_authR share address (leibnizO resource).

  Definition rmapOwnInG : inG Σ rmapAuthT := @resource_map.resource_map_inG Σ share _ address _ _ resource (gen_heapGpreS_heap (gen_heapGpreS := gen_heap_inG)).

  (*
    frag_mem_auth q m σ contains fractional authoritative ownership: resource_map_auth γ q σ.

A lock should only record the lock's resource σ.
It shouldn't own another thread authoritative fraction q.
Otherwise acquire still faces the same problem of updating fractional authority
from σ0 to σ0 ⋅ σlock.
So, use lock_state to store the lock's σ; keep frag_mem_auth for thread state.

   *)

  Definition rmap_has_lock_info (m : mem) (p : lock_info) (σ : rmap) : mpred :=
    (∃ Hp : permMapLt p (getMaxPerm m),
        ⌜mem_equiv.access_map_equiv (perm_of_rmap σ) p /\ coherent (restrPermMap Hp) σ⌝)%I.
(*
  Definition rmap_has_lock_info (p : lock_info)
    (σ : resource_map.rmapUR share address (leibnizO resource)): mpred :=
        ⌜mem_equiv.access_map_equiv (perm_of_rmap σ) p⌝ ∧
        @own Σ rmapAuthT rmapOwnInG
          (gen_heap_name heapGS_gen_heapGS)
          (◯ σ))%I. *)

  Definition lock_payload (m : mem) (p : lock_info) (σ : rmap) (R : mpred) : mpred :=
    (rmap_has_lock_info m p σ ∗ ▷ R)%I.

(*
  Definition lock_state (tp : t) (m : mem) (ls : gset address) : mpred :=
    (∃ I : gmap address mpred, (<affine> ⌜dom I = ls ∧ lock_addresses_disjoint ls⌝) ∗
          own lockGS_gname (gmap_view_auth (DfracOwn 1) (invariant_unfold <$> I)) ∗
          [∗ map] l ↦ R ∈ I,
       (* Available lock *)
       ((∃ (p : lock_info) (σ : rmap),
            (<affine> ⌜lockRes tp l = Some p ∧
               Mem_load_unchecked Mptr m l.1 l.2 = Vptrofs Ptrofs.one⌝) ∗ lock_payload m p σ R)
        ∨ (* Held lock *)
          (<affine> ⌜lockRes tp l = Some empty_map ∧ Mem_load_unchecked Mptr m l.1 l.2 = Vptrofs Ptrofs.zero⌝)))%I.

  *)



  Lemma locks_coherent_acquire_update (tp : dtp) (m m' : mem) (ls : gset address) (i : nat)
    (cnti : containsThread tp i) (c : CC_core) (newThreadPerm : access_map)
    (l : address) (Hl : l ∈ ls) (Hlocks : locks_coherent tp m ls)
    (* The store changes the acquired lock to zero. *)
    (Hload_same : Mem_load_unchecked Mptr m' l.1 l.2 = Vptrofs Ptrofs.zero)
    (* The store does not change any other lock. *)
    (Hload_other : forall l', l' ∈ ls -> l' <> l -> Mem_load_unchecked Mptr m' l'.1 l'.2 =
                                              Mem_load_unchecked Mptr m l'.1 l'.2)
    (* All threads in the resulting pool retain Nonempty on lock addresses. *)
    (Hnonempty : forall (l' : address), l' ∈ ls -> forall (j : nat)
           (cntj : containsThread (updLockSet (updThread cnti (Kresume c Vundef)newThreadPerm) l
                   empty_map) j)
           (Hp : permMapLt (getThreadR cntj) (getMaxPerm m')),
         nonEmptyRangeCur (restrPermMap Hp) l') :
    locks_coherent (updLockSet (updThread cnti (Kresume c Vundef) newThreadPerm) l empty_map) m' ls.
  Proof.
    rewrite /locks_coherent in Hlocks |- *.
    intros l' Hl'.
    destruct (decide (l' = l)) as [Heq | Hneq]; subst.
    - split; try rewrite gssLockRes //.
      split. left.
      split; auto.
      intros j cntj Hp.
      eapply Hnonempty; auto.
    - pose proof (Hlocks l' Hl') as Hlocks'.
      destruct Hlocks' as (HlockRes' & HlockState' & Hrange').
      assert (HlockRes_eq : lockRes (updLockSet (updThread cnti (Kresume c Vundef) newThreadPerm)
                                       l empty_map) l' = lockRes tp l').
      { rewrite gsoLockRes //. }
      split; try rewrite HlockRes_eq //.
      split; last first.
      intros j cntj Hp.
      eapply Hnonempty; auto.
      rewrite Hload_other //.
  Qed.

  Lemma Mem_load_unchecked_store_unchecked_same (m : mem) (b : Values.block) (ofs : Z) :
    Mem_load_unchecked Mptr (Mem_store_unchecked Mptr m b ofs (Vptrofs Ptrofs.zero)) b ofs =
      Vptrofs Ptrofs.zero.
  Proof.
    rewrite /Mem_load_unchecked /Mem_store_unchecked /Mem_store_unchecked_contents /=.
    rewrite PMap.gss /=.
    rewrite <- (encode_val_length Mptr (Vptrofs Ptrofs.zero)).
    rewrite Mem.getN_setN_same.
    pose proof (decode_encode_val_general (Vptrofs Ptrofs.zero) Mptr Mptr) as Hdecode.
    unfold Mptr, Vptrofs, decode_encode_val in Hdecode |- *.
    destruct Archi.ptr64; simpl in *; auto.
 Qed.

  Lemma restrPermMap_twice_eq p1 p2 m (H1 : permMapLt p1 (getMaxPerm m))
    (H2 : permMapLt p2 (getMaxPerm (restrPermMap H1))) (H2g : permMapLt p2 (getMaxPerm m)):
    restrPermMap H2 = restrPermMap H2g.
  Proof. etransitivity; try apply (restrPermMap_idem H2); apply restr_proof_irr. Qed.

  Lemma coherent_restrPermMap_store_unchecked_nonempty m (σ : rmap) p b ofs v
    (Hσ : permMapLt (perm_of_rmap σ) (getMaxPerm m)) (Hp : permMapLt p (getMaxPerm m))
    (Hσ' : permMapLt (perm_of_rmap σ) (getMaxPerm (Mem_store_unchecked Mptr m b ofs v)))
    (Heq : mem_equiv.access_map_equiv (perm_of_rmap σ) p)
    (Hnonempty : nonEmptyRangeCur (restrPermMap Hp) (b, ofs)) :
    coherent (restrPermMap Hσ) σ -> coherent (restrPermMap Hσ') σ.
  Proof.
    intros Hcoh (b' & ofs').
    destruct (Hcoh (b', ofs')) as (Hnext & Hcontents & Haccess).
    split.
    - intros Hge; apply Hnext; rewrite !restrPermMap_nextblock // in Hge |- *.
    - split.
      + intros mv Hval.
        rewrite restrPermMap_contents in Hcontents |- *.
        destruct (adr_range_dec (b, ofs) (size_chunk Mptr) (b', ofs')) as [Hin | Hout].
        * (* The changed location is in the Nonempty range. *)
          destruct Hin as (Hb & Hlo & Hhi).
          simpl in *.
          subst b'.
          assert (Hne : (perm_of_rmap σ) # b ofs' = Some Nonempty).
          { unfold nonEmptyRangeCur in Hnonempty.
            specialize (Hnonempty (ofs' - ofs)%Z).
            spec Hnonempty.
            { rewrite <- size_chunk_conv; lia. }
            replace ((b, ofs).2) with ofs in Hnonempty by auto.
            replace (ofs + (ofs' - ofs))%Z with ofs' in Hnonempty by lia.
            rewrite restrPermMap_Cur_eq in Hnonempty.
            specialize (Heq b).
            rewrite Heq //.
          }
          exfalso.
          unfold resource_at, resR_to_resource in Hval.
          destruct (σ !! (b, ofs')) as [s |] eqn:Hlookup; simpl in Hval; try discriminate.
          destruct s as [dq rsh av | sh nrsh]; simpl in Hval; try discriminate.
          assert (Hread : Mem.perm_order'' ((perm_of_rmap σ) # b ofs') (Some Readable)).
          { eapply (readable_dfrac_perm_order m (perm_of_rmap σ) dq mv av (b, ofs') Hσ rsh).
            - rewrite Hlookup in Hval.
              inv Hval; rewrite H0 /=; f_equal; done.
            - rewrite /access_cohere /resource_at Hlookup /= in Haccess.
              rewrite Haccess; apply po_refl.
          }
          rewrite Hne in Hread. inv Hread. rewrite Hlookup in Hval.
          inv Hval. rewrite Hlookup in Hval. done.
        * (* Outside the stored range, contents are unchanged. *)
          rewrite -(Hcontents mv Hval) /juicy_mem.contents_at /Mem_store_unchecked /= /Mem_store_unchecked_contents.
          destruct (Pos.eq_dec b' b) as [-> | Hb].
          ** rewrite Maps.PMap.gss Mem.setN_other; auto.
             intros r Hr Heqr.
             subst r.
             apply Hout.
             split; auto.
             rewrite encode_val_length in Hr.
             by rewrite size_chunk_conv.
          ** rewrite Maps.PMap.gso //.
    + (* Mem_store_unchecked does not change current permissions. *)
      unfold access_cohere in Haccess |- *.
      rewrite !access_at_restrPermMap_Cur // in Haccess |- *.
  Qed.
  
  Lemma perm_of_sh_writable0_not_top sh (Hw : shares.writable0_share sh) (Htop : sh <> Share.top) : perm_of_sh sh = Some Writable.
  Proof. unfold perm_of_sh; repeat if_tac; done. Qed.

  Lemma perm_of_sh_readable_not_writable0 sh (Hr : shares.readable_share sh)
    (Hnw : ~ shares.writable0_share sh) :
    perm_of_sh sh = Some Readable.
  Proof. unfold perm_of_sh; repeat if_tac; done. Qed.

  Lemma perm_of_sh_unreadable_nonbot sh
    (Hnr : ~ shares.readable_share sh) (Hnb : sh <> Share.bot) :
    perm_of_sh sh = Some Nonempty.
  Proof.
    unfold perm_of_sh.
    repeat if_tac; try done.
    - exfalso; apply Hnr, shares.writable0_readable; auto.
    - exfalso; apply Hnr, shares.writable0_readable; auto.
  Qed.

  Lemma join_permjoin_sh (sh1 sh2 sh : share) :
    sepalg.join sh1 sh2 sh ->
    permjoin_def.permjoin (perm_of_sh sh1) (perm_of_sh sh2) (perm_of_sh sh).
  Proof.
    intro Hjoin.
    unfold perm_of_sh.
    destruct (writable0_share_dec sh1) as [Hw1 | Hnw1] eqn:Ew1.
    - destruct (eq_dec sh1 Share.top) as [Ht1 | Hnt1] eqn:Et1.
      + subst sh1.
        assert (Hbot2 : sh2 = Share.bot).
        { apply join_top_l in Hjoin; auto. }
        subst sh2.
        assert (Htop : sh = Share.top).
        { apply join_top in Hjoin; auto. }
        subst sh.
        repeat if_tac; try constructor; try contradiction.
        pose proof (Share.nontrivial). done.
        exfalso.
        apply bot_unreadable.
        apply writable0_readable; auto.
        exfalso.
        apply (bot_unreadable H1).
      + destruct (writable0_share_dec sh2) as [Hw2 | Hnw2] eqn:Ew2.
        * exfalso.
          eapply join_writable0_readable; eauto.
        * destruct (readable_share_dec sh2) as [Hr2 | Hnr2] eqn:Er2.
          ++ exfalso.
             eapply join_writable0_readable; eauto.
          ++ destruct (eq_dec sh2 Share.bot) as [Hb2 | Hnb2] eqn:Eb2.
             ** subst.
                apply join_with_bot_r in Hjoin.
                subst.
                rewrite Ew1.
                rewrite Et1.
                if_tac; constructor.
             ** assert (Hr : readable_share sh).
                { eapply join_readable1; eauto. }
                repeat if_tac; try constructor; try contradiction.
                apply join_writable01 in Hjoin; auto. done.
    - destruct (readable_share_dec sh1) as [Hr1 | Hnr1] eqn:Er1.
      + destruct (writable0_share_dec sh2) as [Hw2 | Hnw2] eqn:Ew2.
        * exfalso.
          eapply join_writable0_readable; try apply (sepalg.join_comm Hjoin); auto.
        * destruct (readable_share_dec sh2) as [Hr2 | Hnr2] eqn:Er2.
          ++ repeat if_tac; subst; try constructor.
             ** apply join_to_bot_r in Hjoin; subst.
                pose proof (bot_unreadable); done.
             ** apply join_readable1 in Hjoin; done.
          ++ destruct (eq_dec sh2 Share.bot) as [Hb2 | Hnb2] eqn:Eb2.
             ** subst.
                apply join_with_bot_r in Hjoin; subst.
                rewrite Ew1 Er1.
                if_tac; constructor.
             ** assert (Hr : readable_share sh).
                { eapply join_readable1; eauto. }
                assert (Hnw : ~ writable0_share sh).
                { eapply join_readable_unreadable; eauto. }
                repeat if_tac; try constructor; try contradiction.
      + destruct (eq_dec sh1 Share.bot) as [Hb1 | Hnb1] eqn:Eb1.
        * subst.
          apply join_with_bot_l in Hjoin; subst.
          repeat if_tac; try constructor; try contradiction.
        * destruct (writable0_share_dec sh2) as [Hw2 | Hnw2] eqn:Ew2.
          ** assert (Hw : writable0_share sh).
             { apply sepalg.join_comm in Hjoin.
               apply join_writable01 in Hjoin; auto. }
             repeat if_tac; subst; try constructor; try contradiction.
             apply join_top_r in Hjoin. done.
             apply join_top_r in Hjoin. done.
          ** destruct (readable_share_dec sh2) as [Hr2 | Hnr2] eqn:Er2.
          ++ assert (Hr : readable_share sh).
             { eapply join_readable2; eauto. }
             assert (Hnw : ~ writable0_share sh).
             { eapply join_readable_unreadable; try apply sepalg.join_comm; eauto. }
             repeat if_tac; subst; try constructor; try contradiction.
          ++ destruct (eq_dec sh2 Share.bot) as [Hb2 | Hnb2] eqn:Eb2.
             *** subst sh2.
                 apply join_with_bot_r in Hjoin; subst.
                 repeat if_tac; subst; try constructor; try contradiction.
             *** assert (Hnr : ~ readable_share sh).
                 { eapply join_unreadable_shares; eauto. }
                 destruct (writable0_share_dec sh) as [Hw | Hnw] eqn:Ew.
                 +++ pose proof Hw as Hw1.
                     apply writable0_readable in Hw1. done.
                 +++ repeat if_tac; subst; try constructor; try contradiction.
                     apply join_to_bot_r in Hjoin; subst; done.
  Qed.

  Lemma readable_share'_perm_of_sh'_iff (s : shareO) :
  shared.readable_share' s <-> Mem.perm_order' (perm_of_sh' s) Readable.
  Proof.
    destruct s as [sh |]; split; simpl; intros; rewrite /perm_of_sh; try done.
    - rewrite /perm_of_sh.
      repeat if_tac; subst; try constructor; try contradiction.
    - rewrite /perm_of_sh in H.
      repeat if_tac in H; subst; auto; inv H.
  Qed.


  Lemma perm_of_sh_clamped_readable (s : share) : ~ writable0_share s ->
    (if Mem.perm_order'_dec (perm_of_sh s) Readable
     then perm_of_sh s
     else Some Readable) = Some Readable.
  Proof.
    intros Hnw.
    destruct (Mem.perm_order'_dec (perm_of_sh s) Readable) as [Hread | Hnread]; auto.
    unfold perm_of_sh in *; repeat if_tac; simpl in *;
      try contradiction; try auto; try inv Hread.
  Qed.

  Lemma permjoin_RNR_unreadable_op (s1 s2 : shareO)
    (Hnr1 : ¬ shared.readable_share' s1) (Hnr2 : ¬ shared.readable_share' s2) :
    permjoin_def.permjoin (Some Readable) (Some Nonempty)
      (if Mem.perm_order'_dec (perm_of_sh' (s1 ⋅ s2)) Readable
       then perm_of_sh' (s1 ⋅ s2) else Some Readable).
  Proof.
    destruct (Mem.perm_order'_dec (perm_of_sh' (s1 ⋅ s2)) Readable) as [Hr | Hnr].
    - exfalso.
      apply (shared.op_unreadable_shares s1 s2 Hnr1 Hnr2).
      apply (proj2 (readable_share'_perm_of_sh'_iff (s1 ⋅ s2))); auto.
    - constructor.
  Qed.

  Lemma perm_of_sh_readable_iff (sh : share) :
    Mem.perm_order' (perm_of_sh sh) Readable <-> readable_share sh.
  Proof.
    unfold perm_of_sh.
    split.
    - repeat if_tac; intros; try inv H2; auto.
    - repeat if_tac; intros; try constructor; try contradiction.
  Qed.

  Local Notation sresR := (@shared.sharedR share share_instance(leibnizO resource)).

  Lemma permjoin_resR_NO_YES_from_valid (dq0 : dshare.dfrac) (rdq0 : readable_dfrac dq0)
    (v0 : agree (leibnizO resource)) (shL : shareO) (rshL : ¬ shared.readable_share' shL)
    (Hv : ✓ Some ((shared.YES dq0 rdq0 v0 : sresR) ⋅ (shared.NO shL rshL : sresR))) :
    permjoin_def.permjoin (perm_of_res (resR_to_resource (Some (shared.NO shL rshL))))
    (perm_of_res (resR_to_resource (Some (shared.YES dq0 rdq0 v0))))
    (perm_of_res (resR_to_resource
                    (Some ((shared.YES dq0 rdq0 v0 : sresR) ⋅ (shared.NO shL rshL: sresR))))).
  Proof.
    apply permjoin_def.permjoin_comm.
    pose proof (shared.shared_op_alt _ (shared.YES dq0 rdq0 v0) (shared.NO shL rshL)) as Hop.
    simpl in Hop.
    destruct (shared.readable_dfrac_dec (dq0 ⋅ dshare.DfracOwn shL)) as [rsh | Hnread] eqn:Hdec.
    - destruct Hop as (v & Hval & Hop).
      inv Hval.
      rewrite Hop.
      cbn [resR_to_resource shared.dfrac_of shared.val_of option_map].
      destruct (resource_map.elem_of_agree v) as (x1 & Hmem) eqn:Helem.
      rewrite Helem.
      destruct x1; rewrite /perm_of_res.
      + assert (Hproj : proj1_sig (exist (fun x => x ∈ agree_car v) (VAL v0) Hmem) = VAL v0) by done.
        rewrite Hproj.
        destruct shL as [shL |].
        * destruct (eq_dec shL Share.bot) as [Hbot | Hnbot].
          ++ clear Hdec Hop Hv rsh rdq0 rshL Helem Hproj Hmem.
             subst.
             assert (Hs : forall s, s ⋅ Share Share.bot = s).
             { replace (Share Share.bot) with (ε : share_car) by done;
                 apply ucmra_unit_right_id_L. }
             destruct dq0 as [s | s]; simpl; rewrite Hs; destruct s; constructor.
          ++ destruct dq0 as [sh0 | sh0]; destruct sh0 as [sh0 |];
               cbn in rdq0, rsh |- *; try contradiction.
             assert (HpermL : perm_of_sh shL = Some Nonempty).
             { unfold perm_of_sh.
               repeat if_tac; try done; subst; exfalso; apply rshL.
               - change (readable_share Share.top).
                 apply writable0_readable; auto.
               - apply writable0_readable in H; done.
             }
             ** destruct (dshare.DfracOwn (Share sh0) ⋅ dshare.DfracOwn (Share shL)); destruct s; simpl;
                  try inv rsh.
                pose proof (shared.dfrac_of_op' _ (shared.YES (dshare.DfracOwn (Share sh0)) rdq0 v )
                              (shared.NO (Share shL) rshL)) as Hfrac.
                rewrite Hop /= in Hfrac.
                assert (Hsh1 : Share sh0 ⋅ Share shL = Share sh).
                { destruct (Share sh0 ⋅ Share shL) as [|] eqn:Hsum;
                    inv Hfrac; rewrite Hsum // in H0. }
                assert (Hjoin : sepalg.join sh0 shL sh).
                { pose proof ((proj1 (share_op_join (Share sh0) (Share shL) sh)) Hsh1) as Hop1.
                  destruct Hop1 as (x1' & y1' & Hx1' & Hy1' & Hop1).
                  inv Hx1'.
                  apply share_op_is_join; auto. }
                pose proof (join_permjoin_sh sh0 shL sh Hjoin) as Hp.
                rewrite HpermL // in Hp.
                exfalso.
                pose proof (shared.dfrac_of_op' _ (shared.YES (dshare.DfracOwn (Share sh0)) rdq0 v)
                        (shared.NO (Share shL) rshL)) as Hfrac.
                rewrite Hop /= dshare.dfrac_op_own in Hfrac.
                destruct (Share sh0 ⋅ Share shL); inv Hfrac.
             ** destruct (Mem.perm_order'_dec (perm_of_sh sh0) Readable) as [Hr0 | Hnr0].
                *** assert (Hr0' : readable_share sh0).
                    { apply (proj1 (perm_of_sh_readable_iff sh0)); auto. }
                    assert (HnrL : ~ readable_share shL).
                    { intro HrL.
                      apply rshL.
                      apply (proj2 (readable_share'_perm_of_sh'_iff (Share shL))).
                      apply (proj2 (perm_of_sh_readable_iff shL)); auto.
                    }
                    destruct (Share sh0 ⋅ Share shL) as [sh1 |] eqn:Hsh.
                    +++ assert (Hjoin : sepalg.join sh0 shL sh1).
                        { pose proof ((proj1 (share_op_join (Share sh0) (Share shL) sh1)) Hsh)
                            as Hj.
                          destruct Hj as (? & ? & Hsx & Hsy & ?).
                          inv Hsx.
                          apply share_op_is_join; auto.
                        }
                        assert (Hr1 : readable_share sh1).
                        { eapply shares.join_readable1; eauto. }
                        assert (Hp1 : Mem.perm_order' (perm_of_sh sh1) Readable).
                        { apply (proj2 (perm_of_sh_readable_iff sh1)); auto. }
                        destruct (Mem.perm_order'_dec (perm_of_sh sh1) Readable) as [Hp1' | Hnp1].
                        2 :{ contradiction. }
                        unfold perm_of_sh.
                        repeat if_tac; subst; try contradiction.
                        --- exfalso.
                            apply Hnbot.
                            apply join_top_l in Hjoin; auto.
                        --- assert (Hw1 : writable0_share sh1).
                            { eapply join_writable01; eauto. }
                            simpl.
                            rewrite Hsh; simpl.
                            if_tac; try contradiction.
                            unfold perm_of_sh.
                            if_tac; try contradiction.
                            if_tac; try constructor.
                        --- assert (Hnw1 : ~ writable0_share sh1).
                            { eapply join_readable_unreadable; eauto. }
                            simpl.
                            rewrite Hsh.
                            simpl.
                            if_tac; try contradiction.
                            unfold perm_of_sh.
                            if_tac; try contradiction.
                            if_tac; try constructor.
                            if_tac; try contradiction.
                    +++ exfalso.
                        unfold readable_dfrac in rsh.
                        simpl in rsh.
                        pose proof rsh as rsh'.
                        rewrite Hsh // in rsh'.
                *** apply permjoin_RNR_unreadable_op; auto.
                    intro Hread0.
                    apply Hnr0.
                    pose proof (proj1 (readable_share'_perm_of_sh'_iff (Share sh0)) Hread0) as Hp.
                    simpl in Hp. done.
        * simpl in *.
          exfalso.
          rewrite Hop in Hv.
          rewrite Some_valid in Hv.
          destruct dq0 as [s | s].
          +++ destruct s as [sh |]; simpl in Hv; contradiction.
          +++ destruct s as [sh |]; simpl in Hv; contradiction.
      + simpl in *.
        destruct dq0 as [s0 | s0]; simpl.
        * destruct s0 as [sh0 |]; simpl.
          ** destruct shL as [shL |]; try contradiction.
             destruct (eq_dec sh0 Share.bot) as [Hbot0 | Hnbot0].
             { subst sh0; exfalso; apply (bot_unreadable rdq0). }
             destruct (eq_dec shL Share.bot) as [HbotL | HnbotL]; simpl.
             *** destruct (Share sh0 ⋅ Share shL) as [sh1 |] eqn:Hprod.
                 if_tac; subst; try constructor.
                 simpl in rsh.
                 pose proof rsh as rsh'.
                 rewrite Hprod in rsh'. done.
                 simpl in rsh.
                 pose proof rsh as rsh'.
                 rewrite Hprod // in rsh'.
             *** destruct (Share sh0 ⋅ Share shL) as [sh1 |] eqn:Hprod.
                 if_tac; subst; try constructor.
                 simpl in rsh.
                 pose proof rsh as rsh'.
                 rewrite Hprod in rsh'.
                 pose proof (bot_unreadable). done.
                 simpl in rsh.
                 pose proof rsh as rsh'.
                 rewrite Hprod // in rsh'.
          ** destruct shL as [shL |]; try contradiction.
        * destruct shL as [shL |]; try contradiction.
          if_tac; try constructor. constructor.
      + simpl in *.
        destruct dq0 as [s0 | s0]; simpl.
        * destruct s0 as [sh0 |]; simpl.
          ** destruct shL as [shL |]; try contradiction.
             destruct (eq_dec sh0 Share.bot) as [Hbot0 | Hnbot0].
             { subst sh0; exfalso; apply (bot_unreadable rdq0). }
             destruct (eq_dec shL Share.bot) as [HbotL | HnbotL]; simpl.
             *** destruct (Share sh0 ⋅ Share shL) as [sh1 |] eqn:Hprod.
                 if_tac; try constructor; subst.
                 simpl in rsh.
                 pose proof rsh as rsh'.
                 rewrite Hprod // in rsh'.
                 simpl in rsh.
                 pose proof rsh as rsh'.
                 rewrite Hprod // in rsh'.
             *** destruct (Share sh0 ⋅ Share shL) as [sh1 |] eqn:Hprod.
                 if_tac; try constructor; subst.
                 simpl in rsh.
                 pose proof rsh as rsh'.
                 rewrite Hprod in rsh'.
                 pose proof (bot_unreadable). done.
                 simpl in rsh.
                 pose proof rsh as rsh'.
                 rewrite Hprod // in rsh'.
          ** destruct shL as [shL |]; try contradiction.
        * destruct shL as [shL |]; try contradiction.
          if_tac; try constructor. constructor.
    - destruct (shared.dfrac_error (dq0 ⋅ dshare.DfracOwn shL)) eqn:Herr.
      + exfalso; rewrite Some_valid Hop // in Hv.
      + exfalso; rewrite Some_valid in Hv; destruct Hop as (? & ? & ? & ? & ? & ? & ? & ?); done.
  Qed.
  
  Lemma perm_of_rmap_op_permMapJoin (σ0R σlock : resource_map.rmapUR share address (leibnizO resource)) (Hvalid : ✓ (σ0R ⋅ σlock)) :
    permMapJoin (perm_of_rmap σlock) (perm_of_rmap σ0R) (perm_of_rmap (σ0R ⋅ σlock)).
  Proof.
    intros b ofs.
    rewrite !perm_of_rmap_lookup /resource_at gmap.lookup_op.
    pose proof Hvalid as Hv.
    specialize (Hv (b, ofs)).
    rewrite gmap.lookup_op in Hv.
    assert (Hnone : perm_of_res (ε, None) = (@None permission)).
    { rewrite /perm_of_res /=.
      if_tac; auto. contradiction. }
    destruct (σ0R !! (b, ofs)) as [x1 |] eqn:Hx;
      destruct (σlock !! (b, ofs)) as [y1 |] eqn:Hy;
      rewrite Hx Hy in Hv |- *;
      try rewrite op_None_right_id;
      try rewrite op_None_left_id;
      try rewrite Hnone;
      try constructor.
    rewrite - Some_op in Hv |- *.
    clear Hx Hy.
    destruct x1 as [dq0 rdq0 v0 | sh0 rsh0]; destruct y1 as [dqL rdqL vL | shL rshL].
    - (* YES / YES *)
      rewrite shared.YES_op' in Hv |- *.
      destruct (shared.readable_dfrac_dec (dq0 ⋅ dqL)) as [rdq | Hnread] eqn:Hdec.
      + cbn [resR_to_resource
               shared.dfrac_of
               shared.val_of] in Hv |- *.
        destruct Hv as [Hdq Hvagree].
        assert (Hval0L :
                 proj1_sig (resource_map.elem_of_agree (A := leibnizO resource) v0) =
                   proj1_sig (resource_map.elem_of_agree (A := leibnizO resource) vL)).
        { eapply (elem_of_agree_ne' 0).
          - apply cmra_valid_validN.
            eapply cmra_valid_op_l; eauto.
          - apply equiv_dist.
            apply agree_op_inv in Hvagree; done.
        }
        assert (Hval0P :
                 proj1_sig (resource_map.elem_of_agree (A := leibnizO resource) (v0 ⋅ vL)) =
                   proj1_sig (resource_map.elem_of_agree (A := leibnizO resource) v0)).
        { eapply (elem_of_agree_ne' 0).
          - apply cmra_valid_validN; auto.
          - apply equiv_dist.
            apply agree_op_inv in Hvagree.
            rewrite - Hvagree.
            apply agree_idemp.
        }
        cbn [option_map].
        rewrite -Hval0L Hval0P.
        destruct `(resource_map.elem_of_agree v0);
          rewrite /perm_of_res.
        destruct dq0 as [sh0 |]; destruct dqL as [shL |];
          cbn in rdq0, rdqL, rdq, Hdq |- *;
          try contradiction.
        * destruct sh0; destruct shL; try contradiction.
          clear Hdec.
          rewrite dshare.dfrac_op_own in rdq |- *.
          destruct (Share sh ⋅ Share sh0) as [sh1 |] eqn:Hsum; try contradiction.
          assert (Hjoin : sepalg.join sh sh0 sh1).
          { pose proof ((proj1 (share_op_join (Share sh) (Share sh0) sh1)) Hsum) as Hop.
            destruct Hop as (sx & sy & Hsx & Hsy & Hop).
            inv Hsx.
            apply share_op_is_join; auto.
          }
          assert (Hsh : sh <> Share.bot).
          { intro Heq; subst sh; apply (bot_unreadable rdq0). }
          assert (Hsh0 : sh0 <> Share.bot).
          { intro Heq; subst sh0; apply (bot_unreadable rdqL). }
          assert (Hsh1 : sh1 <> Share.bot).
          { intro Heq; subst sh1; simpl in rdq; apply (bot_unreadable rdq). }
          destruct x; try rewrite !if_false; try assumption; try constructor.
          apply permjoin_def.permjoin_comm.
          simpl. apply join_permjoin_sh; auto.
        * simpl in *.
          destruct sh0; destruct s; try contradiction.
          clear Hdec.
          destruct (Share sh ⋅ Share sh0) as [sh1 |] eqn:Hsum; try contradiction.
          assert (Hsh : sh <> Share.bot).
          { intro Heq; subst sh; apply (bot_unreadable rdq0). }
          destruct x; simpl.
          ** pose proof Hdq as Hdq1.
             change (✓ dshare.DfracBoth (Share sh ⋅ Share sh0)) in Hdq1.
             rewrite Hsum in Hdq1.
             destruct Hdq1 as (sh' & Hsh' & Hnw1).
             inversion Hsh'; subst sh'; clear Hsh'.
             assert (Hdq0 : ✓ dshare.DfracBoth (Share sh0)).
             { eapply cmra_valid_op_r; exact Hdq. }
             destruct Hdq0 as (sh' & Hsh' & Hnw0).
             inversion Hsh'; subst sh'; clear Hsh'.
             pose proof Hdq as Hsh_nw.
             rewrite ora_comm in Hsh_nw.
             apply dfrac_valid_own_readable in Hsh_nw; auto.
             destruct Hsh_nw as (sh' & Hsh1 & Hnw).
             symmetry in Hsh1.
             inv Hsh1.
             assert (Hp : perm_of_sh sh = Some Readable).
             { unfold perm_of_sh.
               repeat if_tac; try contradiction; try done.
             }
             assert (Hp0 : (if Mem.perm_order'_dec (perm_of_sh sh0) Readable then perm_of_sh sh0
                            else Some Readable) = Some Readable).
             { rewrite /perm_of_sh.
               repeat if_tac; simpl in *; try contradiction; try reflexivity; inversion H.
             }
             assert (Hp1 : (if Mem.perm_order'_dec (perm_of_sh sh1) Readable then perm_of_sh sh1
                            else Some Readable) = Some Readable).
             { rewrite /perm_of_sh; repeat if_tac; simpl in *;
                 try contradiction; try reflexivity; inversion H.
             }
             rewrite Hp Hp0 Hp1; constructor.
          ** rewrite if_false; auto. constructor.
          ** rewrite if_false; auto. constructor.
        * simpl in *.
          destruct s; destruct shL; try contradiction.
          clear Hdec.
          destruct (Share sh ⋅ Share sh0) as [sh1 |] eqn:Hsum; try contradiction.
          assert (Hsh : sh0 <> Share.bot).
          { apply readable_not_bot; auto. }
          destruct x; simpl.
          ** pose proof Hdq as Hdq1.
             change (✓ dshare.DfracBoth (Share sh ⋅ Share sh0)) in Hdq1.
             rewrite Hsum in Hdq1.
             destruct Hdq1 as (sh' & Hsh' & Hnw1).
             inversion Hsh'; subst sh'; clear Hsh'.
             assert (Hdq_sh : ✓ dshare.DfracBoth (Share sh)).
             { eapply cmra_valid_op_l; eauto. }
             destruct Hdq_sh as (sh' & Hsh' & Hnw).
             inversion Hsh'; subst sh'; clear Hsh'.
             pose proof Hdq as Hsh0_nw.
             apply dfrac_valid_own_readable in Hsh0_nw; auto.
             destruct Hsh0_nw as (sh' & Hsh' & Hnw0).
             symmetry in Hsh'.
             inversion Hsh'; subst sh'; clear Hsh'.
             assert (Hp0 : perm_of_sh sh0 = Some Readable).
             { rewrite /perm_of_sh.
               repeat if_tac; simpl in *; try contradiction; try auto.
             }
             rewrite Hp0.
             rewrite !perm_of_sh_clamped_readable; try constructor.
             change (~ writable0_share sh1) in Hnw1. done.
             change (~ writable0_share sh) in Hnw. done.
          ** rewrite if_false; auto. constructor.
          ** rewrite if_false; auto. constructor.
        * simpl in *.
          destruct s; destruct s0; try contradiction.
          clear Hdec.
          destruct (Share sh ⋅ Share sh0) as [sh1 |] eqn:Hsum; try contradiction.
          destruct x; simpl; try constructor.
          pose proof Hdq as Hdq1.
          change (✓ dshare.DfracBoth (Share sh ⋅ Share sh0)) in Hdq1.
          rewrite Hsum in Hdq1.
          destruct Hdq1 as (sh' & Hsh' & Hnw1).
          inversion Hsh'; subst sh'; clear Hsh'.
          change (~ writable0_share sh1) in Hnw1.
          assert (Hdq0 : ✓ dshare.DfracBoth (Share sh0)).
          { eapply cmra_valid_op_r; eauto. }
          destruct Hdq0 as (sh' & Hsh' & Hnw0).
          inversion Hsh'; subst sh'; clear Hsh'.
          change (~ writable0_share sh0) in Hnw0.
          assert (Hdq_sh : ✓ dshare.DfracBoth (Share sh)).
          { eapply cmra_valid_op_l; eauto. }
          destruct Hdq_sh as (sh' & Hsh' & Hnw).
          inversion Hsh'; subst sh'; clear Hsh'.
          change (~ writable0_share sh) in Hnw.
          rewrite !perm_of_sh_clamped_readable; try constructor; auto.
      + exfalso.
        rewrite Some_valid in Hv.
        inv Hv.
    - (* YES / NO *)
      apply permjoin_resR_NO_YES_from_valid; auto.
    - (* NO / YES *)
      apply permjoin_def.permjoin_comm.
      apply permjoin_resR_NO_YES_from_valid.
      rewrite comm in Hv. done.
    - (* NO / NO *)
      rewrite Some_valid in Hv.
      apply shared.shared_valid in Hv as [Hdq _].
      change (✓ (sh0 ⋅ shL)) in Hdq.
      pose proof Hdq as Hdq1.
      apply share_valid2_joins in Hdq.
      destruct Hdq as (x & y & z & Hsh0 & Hsh1 & Hsh2 & Hshop).
      subst.
      repeat if_tac; subst; simpl.
      rewrite Hsh2.
      repeat if_tac; try constructor; subst.
      + rewrite left_id in Hsh2; inv Hsh2.
      + rewrite right_id in Hsh2; inv Hsh2.
      + rewrite left_id in Hsh2; inv Hsh2.
      + cbn in Hshop.
        destruct (eq_dec (Share.glb x y) Share.bot) as [Hglb | Hglb];
          simpl in Hshop; try discriminate.
        inversion Hshop; subst.
        apply lub_bot_e in H2.
        destruct H2; done.
  Qed.

(*
  Definition lock_state `{!lockGS Σ}
    (lr : address → option access_map) (m : mem) (ls : gset address) : mpred :=
  ∃ I : gmap address mpred,
    <affine> ⌜dom I = ls ∧ lock_addresses_disjoint ls⌝ ∗
    own lockGS_gname (gmap_view.gmap_view_auth
         (DfracOwn 1) (invariant_unfold <$> I)) ∗
    [∗ map] l ↦ R ∈ I, ∃ (q : Qp) (σlock : rmap) (Hlt : permMapLt (perm_of_rmap σlock) (getMaxPerm m)), frag_mem_auth q (restrPermMap Hlt) σlock ∗ (
          (* Available lock *)
          ( <affine> ⌜Mem_load_unchecked Mptr m l.1 l.2 = Vptrofs Ptrofs.one ∧ lr l = Some (perm_of_rmap σlock)⌝ ∗ ▷ R )
          ∨
          ( <affine> ⌜Mem_load_unchecked Mptr m l.1 l.2 = Vptrofs Ptrofs.zero ∧ σlock = ε
                ∧ lr l = Some empty_map⌝ ) ).
*)

  Definition thread_safe (tp : dtp) i (γ : gname) (q : Qp) :=
    ∃ (cnti : containsThread tp i),
      match getThreadC cnti with
      | Krun c | Kblocked c => jsafe_frag γ q ⊤ tt c
      | Kresume c v =>
          ∀ c',
            (* [v] is not used here. The problem is probably coming from
           the definition of JuicyMachine.resume_thread'. *)
            ⌜cl_after_external None c = Some c'⌝ →
            jsafe_frag γ q ⊤ tt c'
      | Kinit v1 v2 =>
          ∃ q_new,
    ⌜cl_initial_core ge v1 (v2 :: nil) = Some q_new⌝ ∧
      jsafe_frag γ q ⊤ tt q_new
  end%I.

 (* Definition threads_safe (tp : dtp) (qs : gmap nat Qp) (m : mem) : iProp Σ :=
    [∗ list] _ ↦ i ∈ seq 0 (pos.n (OrdinalPool.num_threads tp)),
      ∃ q (σ : rmap) (cnti : containsThread tp i)
        (Hlt : permMapLt (perm_of_rmap σ) (getMaxPerm m)),
        ⌜qs !! i = Some q ∧ permMapLt (perm_of_rmap σ) (getThreadR cnti).1⌝ ∗
            thread_safe tp i q ∗ frag_mem_auth q (restrPermMap Hlt) σ. *)

  Definition threads_safe `{rmap_inG : inG Σ rmap_authUR}
    (tp : dtp) (* (m : mem) *) (γ : gname): iProp Σ :=
    [∗ list] _ ↦ i ∈ seq 0 (pos.n (OrdinalPool.num_threads tp)),
      ∃ (q : Qp) (σ : rmap) (cnti : containsThread tp i),
        <affine>⌜mem_equiv.access_map_equiv (perm_of_rmap σ) (getThreadR cnti)⌝ ∗
                  thread_safe tp i γ q ∗ rmap_frag γ q σ.

  
  (* Definition threads_safe `{rmap_inG : inG Σ rmap_authUR}
    (tp : dtp) (m : mem) (σ0 : rmap) (γ : gname) : iProp Σ :=
    [∗ list] _ ↦ i ∈ seq 0 (pos.n (OrdinalPool.num_threads tp)),
      ∃ (q : Qp) (σ : rmap) (cnti : containsThread tp i),
        <affine>⌜mem_equiv.access_map_equiv (perm_of_rmap σ) (getThreadR cnti)⌝ ∗
                  thread_safe tp i γ q ∗
                  frag_mem_auth q m σ0 ∗
                  rmap_frag γ q σ. *)

  Definition threads_wellformed (tp : dtp) :=
    forall i (cnti : containsThread(ThreadPool := OrdinalPool.OrdinalThreadPool) tp i),
    match getThreadC cnti with
    | Krun q => Logic.True
    | Kblocked q => cl_at_external q <> None
    | Kresume q v => cl_at_external q <> None /\ v = Vundef
    | Kinit _ _ => Logic.True
    end.

  Definition other_threads_safe (γ : gname) (tp : dtp) (i : nat) :=
    ∀ (Ψ : nat → nat → iPropI Σ),
      □ (∀ (k y : nat),
            ⌜seq 0 (pos.n (OrdinalPool.num_threads tp)) !! k = Some y⌝ → ⌜k ≠ i⌝ →
       (∃ (q0 : Qp) (σ0 : rmap) (cnti0 : containsThread tp y),
           <affine>⌜mem_equiv.access_map_equiv (perm_of_rmap σ0) (getThreadR cnti0)⌝ ∗
                     thread_safe tp y γ q0 ∗ rmap_frag γ q0 σ0) -∗ Ψ k y) -∗
               Ψ i i -∗ [∗ list] k↦y ∈ seq 0 (pos.n (OrdinalPool.num_threads tp)), Ψ k y.

  
  
  Definition post_safe (γ : gname) (q : Qp)
    (x : Jext_spec_type (concurrent_ext_spec CS ext_link) LOCK)
    (argsty : typelist) (retty : type) (cc : calling_convention) (args : list val) (k : cont) :=
    ∀ (ret : option val) (m' : mem) (σ' : rmap) (z' : unit),
      ⌜Val.has_type_list args (sig_args (ef_sig LOCK)) ∧
        Builtins0.val_opt_has_rettype ret (sig_res (ef_sig LOCK))⌝ →
      |={⊤}=> thread_state_interp γ (getCurPerm m') q m' σ' z' -∗
              Jext_spec_post (concurrent_ext_spec CS ext_link) LOCK x (genv_symb_injective ge)
              (sig_res (ef_sig LOCK)) ret -∗
          ∃ (c' : CC_core), ⌜after_external (cl_core_sem ge) ret (Callstate (Ctypes.External LOCK argsty retty cc) args k) m' = Some c'⌝ ∧
                thread_state_interp γ (getCurPerm m') q m' σ' z' ∗ jsafe_frag γ q ⊤ z' c'.

  Lemma rmap_add_local_update (σcur σ1 σlock : raw_rmapR) :
    ✓ (σcur ⋅ σlock) → (σcur, σ1) ~l~> (σcur ⋅ σlock, σ1 ⋅ σlock).
  Proof.
    intros Hvalid.
    apply local_update_unital.
    intros n ρ _ Heq.
    split.
    - by apply cmra_valid_validN.
    - rewrite Heq.
      rewrite - !assoc.
      by rewrite (comm _ ρ).
  Qed.

  Lemma rmap_auth_frag_acquire_update `{!inG Σ rmap_authUR} (γ : gname) (q : Qp) (σcur σ1 σlock : raw_rmapR) :
    ✓ (σcur ⋅ σlock) →
    rmap_auth γ σcur ∗ rmap_frag γ q σ1
    ==∗
        rmap_auth γ (σcur ⋅ σlock) ∗
        rmap_frag γ q (σ1 ⋅ σlock).
  Proof.
    intros Hvalid.
    rewrite /rmap_auth /rmap_frag.
    iIntros "(Hauth & Hfrag)".
    iMod (own_update_2 with "Hauth Hfrag") as "(Hauth & Hfrag)".
    { apply frac_auth_update.
      by apply rmap_add_local_update. }
    iFrame. done.
  Qed.

  Locate gmap_view_auth.
  Check lock_state.

  

  Print lock_state.

  Lemma rmap_frag_valid `{!inG Σ rmap_authUR} (γ : gname) (q : Qp) (σ : raw_rmapR) :
    rmap_frag γ q σ ⊢ ⌜✓ σ⌝.
  Proof.
    rewrite /rmap_frag.
    iIntros "Hfrag".
    iDestruct (own_valid with "Hfrag") as "Hv".
  Admitted.


  Definition lock_state1 `{!lockGS Σ} `{!inG Σ rmap_authUR} (γ : gname) (m : mem) (ls : gset address) (IR : address -> option access_map) : mpred :=
    ∃ I : gmap address mpred,
      <affine> ⌜dom I = ls ∧ lock_addresses_disjoint ls⌝ ∗
      own lockGS_gname (gmap_view_auth (DfracOwn 1) (invariant_unfold <$> I)) ∗
      [∗ map] a ↦ R ∈ I,
    (* unlocked *)
    (∃ (qL : Qp) (σlock : rmap) (l0 : access_map),
         rmap_frag γ qL σlock ∗
         <affine>⌜IR a = Some l0 ∧ mem_equiv.access_map_equiv l0 (perm_of_rmap σlock) ∧
                                          Mem_load_unchecked Mptr m a.1 a.2 = Vptrofs Ptrofs.one⌝ ∗ ▷ R) ∨
      (* locked *)
      (∃ qL : Qp, rmap_frag γ qL (∅ : raw_rmapR) ∗
                  <affine>⌜IR a = Some empty_map ∧ Mem_load_unchecked Mptr m a.1 a.2 = Vptrofs Ptrofs.zero⌝).
  
  Lemma lock_inv_in_lock_state γ m ls (IR : address -> option access_map) sh l R :
    lock_state1 γ m ls IR -∗ lock_inv sh l R -∗ ⌜∃ l_addr, val2adr l l_addr ∧ l_addr ∈ ls⌝.
  Proof.
    iIntros "Hstate Hlock".
    iDestruct "Hstate" as (I) "((%Hdom & %Hldisj) & Hauth & _)".
    iDestruct "Hlock" as (l1) "(%Hval & _ & Hfrag)".
    iDestruct (own_valid_2 (A := gmap_view.gmap_viewR address _) with "Hauth Hfrag") as "#Hvalid".
    iDestruct (algebra.gmap_view_both_validI with "[$Hvalid]") as "(%Hvalid & #Hlookup)".
    destruct (I !! l1) as [RI |] eqn:HI.
    - iPureIntro.
      exists l1; split; auto; rewrite -Hdom elem_of_dom; by eexists.
    - rewrite lookup_fmap HI.
      iDestruct (option_equivI with "Hlookup") as "[]".
  Qed.
  
  (* Lemma lock_acquire_rmap_update `{!VSTGS () Σ} `{!lockGS Σ} `{!inG Σ rmap_authUR}
    (γ : gname) (q qL : Qp) (m : mem) (ls : gset address) (l : val) (l1 : address) (sh : share)
    (R : oFunctor_car (dependent_type_functor_rec Mpred) (iProp Σ) (iProp Σ))
    (σcur σ1 : rmap) (Hval : val2adr l l1)
    (Hload : Mem_load_unchecked Mptr m l1.1 l1.2 = Vptrofs Ptrofs.one)
    (Hofs : Ptrofs.Z_mod_modulus l1.2 = l1.2) :
    let σ1R := (σ1 : resource_map.rmapUR share address (leibnizO resource)) in
    let m_global' := Mem_store_unchecked Mptr m l1.1 (Ptrofs.intval (Ptrofs.repr l1.2)) (Vptrofs Ptrofs.zero) in
    lock_inv sh l R -∗ lock_state1 γ m ls -∗
    resource_map.resource_map_auth (H1 := gen_heapGpreS_heap (gen_heapGpreS := gen_heap_inG))
      (gen_heap_name heapGS_gen_heapGS) 1 σcur -∗
    rmap_auth γ σcur -∗
    rmap_frag γ q σ1 -∗
    (* resource currently owned by the unlocked lock *)
    (∃ σlock : rmap, ⌜lock_rmap_holds R σlock⌝ ∧ rmap_frag γ qL σlock) ==∗
    ∃ σlock σnew : rmap,
      ⌜✓ (σ1R ⋅ σlock) ∧ lock_rmap_holds R σlock⌝ ∧
      ∃ Hlt_store : permMapLt (perm_of_rmap (σ1R ⋅ σlock)) (getMaxPerm m_global'),
        frag_mem_auth (restrPermMap Hlt_store) σnew ∗
        rmap_auth γ σnew ∗
        (* thread now owns σlock *)
        rmap_frag γ q (σ1R ⋅ σlock) ∗
        (* lock keeps its fraction, but carries no resource *)
        rmap_frag γ qL (∅ : raw_rmapR) ∗
        lock_state1 γ m_global' ls ∗
        lock_inv sh l R ∗
        ▷ R.
   Proof.
     intros σ1R m_global'.
     iIntros "Hl Hls Hrs Hauth Hfrag Hlock".
     iDestruct "Hlock" as (σlock) "(%Hlr & Hlockfrag)".
     iCombine "Hfrag Hlockfrag" as "Hfrags".
     rewrite rmap_frag_lock_transfer.
     iDestruct "Hfrags" as "(Hfrag & Hlockfrag)".
     iExists σlock, σcur.
     rewrite /frag_mem_auth.
     Search resource_map.resource_map_auth.
     iFrame "Hauth Hfrag Hl".
     iFrame.
     Search rmap_frag. *)

  

  Lemma perm_of_rmap_included (σ σ0 : raw_rmapR) :
    ✓ σ0 -> σ ≼ σ0 -> permMapLt (perm_of_rmap σ) (perm_of_rmap σ0).
  Proof.
    intros Hv Hinc b ofs.
    rewrite !perm_of_rmap_lookup.
    destruct Hinc as (δ & Hδ).
    assert (Hloc : σ !! (b, ofs) ≼ σ0 !! (b, ofs)).
    { exists (δ !! (b, ofs)).
      specialize (Hδ (b, ofs)).
      by rewrite lookup_op in Hδ.
    }
    specialize (Hv (b, ofs)).
    pose proof (resR_le (σ !! (b, ofs)) (σ0 !! (b, ofs)) Hv Hloc) as Hle.
    eapply perm_of_res_mono'; last exact Hle.
    rewrite resR_to_resource_fst.
    destruct (σ0 !! (b, ofs)) as [s|] eqn:Hs; simpl in *.
    - rewrite Hs /=.
      rewrite Hs /= in Hv.
      apply shared.shared_valid in Hv as (Hd & _); auto.
    - rewrite Hs. done.
  Qed.


  Lemma rmap_auth_frag_permMapLt_valid `{!inG Σ rmap_authUR} γ (q : Qp) (σcur σ : raw_rmapR) :
    ✓ σcur -> rmap_auth γ σcur ∗ rmap_frag γ q σ ⊢
               ⌜✓ σ ∧ permMapLt (perm_of_rmap σ) (perm_of_rmap σcur)⌝.
  Proof.
    intros Hvcur.
    rewrite /rmap_auth /rmap_frag.
    iIntros "(Ha & Hf)".
    iPoseProof (own_valid_2 with "Ha Hf") as "Hvalid".
    iPoseProof (frac_auth_agreeI (A := raw_rmapR) q σcur σ with "Hvalid") as "Hrel".
    destruct (decide (q = 1%Qp)) as [Hq | Hq].
    - iDestruct "Hrel" as "%Heq".
      assert (Hinc : σ ≼ σcur).
      { exists (∅ : raw_rmapR). by rewrite right_id. }
      assert (Hperm : permMapLt (perm_of_rmap σ) (perm_of_rmap σcur)).
      { eapply perm_of_rmap_included; eauto. }
      iPureIntro. split; try eapply cmra_valid_included; eauto.
    - iDestruct "Hrel" as (c) "%Heq".
      assert (Hinc : σ ≼ σcur).
      { by exists c. }
      assert (Hperm : permMapLt (perm_of_rmap σ) (perm_of_rmap σcur)).
      { eapply perm_of_rmap_included; eauto. }
      iPureIntro. split; try eapply cmra_valid_included; eauto.
  Qed.

  Ltac get_lk n dq rsh Hvalid Hincl Hlk :=
    let Hseq := fresh "Hseq" in
    assert (Hseq : seq 0%nat (Z.to_nat LKSIZE) !! n = Some n) by
      (vm_compute; reflexivity);
    iDestruct (big_sepL_lookup_acc with "HLK") as "[HLKi Hclose]";
    first exact Hseq;
    iDestruct (mapsto_lookup with "Hm HLKi")
      as %(dq & rsh & Hvalid & Hincl & Hlk);
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

  Lemma frag_mem_auth_store_unchecked_lock_zero_restr `{!VSTGS () Σ} (m : mem) (σ : rmap)
    (Hlt : permMapLt (perm_of_rmap σ) (getMaxPerm m)) sh (b : Values.block) (o : Z) (v : val) :
    frag_mem_auth (restrPermMap Hlt) σ -∗ LKspec LKSIZE sh (b, o) ==∗
    ∃ Hlt' : permMapLt (perm_of_rmap σ) (getMaxPerm (Mem_store_unchecked Mptr (restrPermMap Hlt) b o v)), frag_mem_auth (restrPermMap Hlt') σ ∗ LKspec LKSIZE sh (b, o).
  Proof.
    iIntros "Hmem HLK".
    rewrite /frag_mem_auth.
    iDestruct "Hmem" as (Hlt0) "(%Hcoh & Hm)".
    assert (Heq_restr : restrPermMap Hlt0 = restrPermMap Hlt).
    { rewrite (restrPermMap_idem Hlt0); apply restr_proof_irr. }
    rewrite Heq_restr in Hcoh.
    iDestruct (resource_map.resource_map_auth_valid with "Hm") as %(_ & Hvalid).
    rewrite /LKspec /=.
    get_lk 0%nat dq0 rsh0 Hvalid0 Hincl0 Hlk0.
    get_lk 1%nat dq1 rsh1 Hvalid1 Hincl1 Hlk1.
    get_lk 2%nat dq2 rsh2 Hvalid2 Hincl2 Hlk2.
    get_lk 3%nat dq3 rsh3 Hvalid3 Hincl3 Hlk3.
    get_lk 4%nat dq4 rsh4 Hvalid4 Hincl4 Hlk4.
    get_lk 5%nat dq5 rsh5 Hvalid5 Hincl5 Hlk5.
    get_lk 6%nat dq6 rsh6 Hvalid6 Hincl6 Hlk6.
    get_lk 7%nat dq7 rsh7 Hvalid7 Hincl7 Hlk7.
    assert (Hcoh_store : coherent (Mem_store_unchecked Mptr (restrPermMap Hlt) b o v) σ).
    { unfold coherent, resource_at in *.
      intro loc.
      destruct (Hcoh loc) as (Hnext & Hcontents & Haccess).
      split3; try done.
      unfold contents_cohere, contents_at in *.
      intros mv Hval.
      destruct (adr_range_dec (b, o) (size_chunk Mptr) loc) as [Hin | Hout].
      - destruct loc as [bb ofs].
        destruct Hin as (Hb & Hlo & Hhi); simpl in *.
        subst bb.
        change (size_chunk Mptr) with 8%Z in Hhi.
        assert (ofs = o \/ ofs = o + 1 \/ ofs = o + 2 \/ ofs = o + 3 \/
                  ofs = o + 4 \/ ofs = o + 5 \/ ofs = o + 6 \/ ofs = o + 7)%Z as Hor by lia.
        exfalso.
        repeat destruct Hor as [-> | Hor];
          repeat solve_LK_VAL_contra.
        + replace (adr_add (b, o) 0%nat) with (b, o) in Hlk0; last first.
          { rewrite /adr_add //=. f_equal. lia. }
          erewrite resR_to_resource_eq in Hval; eauto.
          rewrite /= elem_of_to_agree in Hval.
          inversion Hval.
        + subst ofs.
          erewrite resR_to_resource_eq in Hval; eauto.
          rewrite /= elem_of_to_agree in Hval.
          inv Hval.
      - rewrite <- (Hcontents mv Hval).
        rewrite /juicy_mem.contents_at /Mem_store_unchecked /= /Mem_store_unchecked_contents.
        destruct loc as (b' & ofs); simpl in *.
        destruct (Pos.eq_dec b' b) as [Hb | Hb].
        + subst b'.
          rewrite Maps.PMap.gss Mem.setN_other; auto.
          intros r Hr.
          intro Heq.
          subst r.
          apply Hout.
          split; auto.
          rewrite encode_val_length in Hr. done.
        + rewrite Maps.PMap.gso; auto.
    }
    assert (Hlt_store : permMapLt (perm_of_rmap σ) (getMaxPerm (Mem_store_unchecked Mptr (restrPermMap Hlt) b o v))).
    { by apply coherent_perm_of_rmap_max. }
    assert (Hlt_inner : permMapLt (perm_of_rmap σ) (getMaxPerm (restrPermMap Hlt_store))).
    { eapply mem_equiv.useful_permMapLt_trans; done. }
    assert (Hcoh_restr : coherent (restrPermMap Hlt_store) σ).
    { eapply coherent_restrPermMap; done. }
    assert (Hcoh_inner : coherent (restrPermMap Hlt_inner) σ).
    { eapply coherent_restrPermMap; done. }
    iModIntro.
    iExists Hlt_store.
    iSplitL "Hm".
    - rewrite /frag_mem_auth.
      iExists Hlt_inner.
      iFrame "Hm".
      by iPureIntro.
    - rewrite /LKspec /=.
      iExact "HLK".
  Qed.
    
  Lemma lock_acquire_rmap_update `{!VSTGS () Σ} `{!lockGS Σ} `{!inG Σ rmap_authUR}
    (γ : gname) (q : Qp) (m : mem) (ls : gset address) (IR : address -> option access_map)
    (l : val) (l1 : address) (sh : share)
    (R : oFunctor_car (dependent_type_functor_rec Mpred) (iProp Σ) (iProp Σ))
    (σcur σ1 : rmap) (Hval : val2adr l l1)
    (Hload : Mem_load_unchecked Mptr m l1.1 l1.2 = Vptrofs Ptrofs.one)
    (Hofs : Ptrofs.Z_mod_modulus l1.2 = l1.2)
    (Hltσcur : permMapLt (perm_of_rmap σcur) (getMaxPerm m))
    (Hσcur : coherent (restrPermMap Hltσcur) σcur) :
    let σ1R :=
      (σ1 : resource_map.rmapUR share address (leibnizO resource)) in
    let m_global' :=
      Mem_store_unchecked Mptr m l1.1 (Ptrofs.intval (Ptrofs.repr l1.2)) (Vptrofs Ptrofs.zero) in
    let IR' : address -> option access_map :=
      fun a =>
        if decide (a = l1)
        then Some empty_map
        else IR a in
    lock_inv sh l R -∗ lock_state1 γ m ls IR  -∗
    resource_map.resource_map_auth (H1 := gen_heapGpreS_heap (gen_heapGpreS := gen_heap_inG)) (gen_heap_name heapGS_gen_heapGS) 1 σcur -∗ rmap_auth γ σcur -∗ rmap_frag γ q σ1 ==∗
    ∃ σlock σnew : rmap, ⌜✓ (σ1R ⋅ σlock) ∧
                           exists l0 : access_map, IR l1 = Some l0 ∧ mem_equiv.access_map_equiv l0 (perm_of_rmap σlock)⌝ ∧
    ∃ Hlt_store : permMapLt (perm_of_rmap (σ1R ⋅ σlock)) (getMaxPerm m_global'),
      frag_mem_auth (restrPermMap Hlt_store) σnew ∗ rmap_auth γ σnew ∗ rmap_frag γ q (σ1R ⋅ σlock)
      ∗ lock_state1 γ m_global' ls IR' ∗ lock_inv sh l R ∗ ▷ R.
  Proof.
    intros σ1R m_global' IR'.
    iIntros "Hl Hls Hrs Hauth Hfrag".
    iDestruct "Hls" as (I) "((%Hdom & %Hldisj) & HI & HRs)".
    iDestruct "Hl" as (a) "(%Hva & Hlk & Hi)".
    assert (Ha : a = l1).
    { unfold val2adr in Hva, Hval.
      destruct l; try contradiction; congruence.
    }
    subst a.
    iPoseProof (own_valid_2 (A := gmap_view.gmap_viewR address (laterO (iPropO Σ))) with "HI Hi")
      as "#Heq".
    iDestruct (own_valid_2 (A := gmap_view.gmap_viewR address _) with "HI Hi") as "#Heq1".
    rewrite gmap_view_both_validI bi.and_elim_r lookup_fmap option_equivI.
    destruct (invariant_unfold <$> I !! l1) as [Q |] eqn: HIQ; simpl.
    2: { by rewrite /invariant_unfold HIQ. }
    rewrite HIQ later_equivI.
    apply fmap_Some in HIQ as (R0 & HIR0 & HQ).
    rewrite (big_sepM_delete _ _ l1); eauto.
    iDestruct "HRs" as "[Hhere Hrest]".
    iDestruct "Hhere" as "[Hhere | Hhere]".
    - iDestruct "Hhere" as (qL σlock l0) "(Hlockfrag & (%HIRl1 & %Heq_lock & %Hload0) & HR)".
      subst Q.
      simpl.
      iAssert (▷ R)%I with "[Heq HR]" as "HR".
      { iNext. by iRewrite "Heq" in "HR". }
      iCombine "Hfrag Hlockfrag" as "Hfrags".
      rewrite rmap_frag_lock_transfer.
      iDestruct "Hfrags" as "[Hfrag Hempty]".
      iAssert (lock_state1 γ m_global' ls IR')%I with "[HI Hrest Hempty]" as "Hls".
      { rewrite /lock_state1.
        iExists I.
        iFrame "HI".
        iSplit.
        { iPureIntro. split; auto. }
        rewrite {1} (big_sepM_delete _ _ l1 R0 HIR0).
        iSplitL "Hempty".
        + iRight.
          iExists qL. iFrame.
          iPureIntro.
          split.
          * unfold IR'.
            destruct (decide (l1 = l1)) as [_ | Hneq]; auto. contradiction.
          * rewrite /m_global' /semax_conc_pred.Mem_load_unchecked /Mem_store_unchecked /= /Mem_store_unchecked_contents.
          rewrite Hofs.
          by rewrite Maps.PMap.gss -(encode_val_length Mptr (Vptrofs Ptrofs.zero))
                                      Mem.getN_setN_same.
        + iApply (big_sepM_mono with "Hrest").
          iIntros ((b1 & o1) y Hky) "Hk".
          rewrite lookup_delete_Some in Hky.
          destruct Hky as [Hneq HkI].
          assert (Hin1 : (b1, o1) ∈ ls).
          { rewrite <- Hdom. eapply elem_of_dom_2; eauto. }
          assert (Hin2 : l1 ∈ ls).
          { rewrite <- Hdom. eapply elem_of_dom_2; eauto. }
          assert (HIR_same: IR' (b1, o1) = IR (b1, o1)).
          { unfold IR'.
            destruct (decide ((b1, o1) = l1)) as [Heqbl | Hnebl].
            - subst. contradiction.
            - rewrite if_false; auto. }
          assert (Hsame : Mem_load_unchecked Mptr m_global' b1 o1 = Mem_load_unchecked Mptr m b1 o1).
          {
            unfold m_global'.
            destruct l1 as [b o]; simpl in *.
            rewrite Hofs.
            assert (Hneq' : (b1, o1) <> (b, o)) by congruence.
            assert (Hrepr : Ptrofs.unsigned (Ptrofs.repr o) = o).
            { rewrite Ptrofs.unsigned_repr. done. rewrite -Hofs.
              pose proof (Ptrofs.Z_mod_modulus_range o) as Hr.
              unfold Ptrofs.max_unsigned. lia. }
            rewrite <- Hrepr.
            eapply Mem_load_unchecked_store_unchecked_lock_addresses_disjoint; eauto.
            * rewrite Hrepr. done.
            * rewrite Hrepr. done. }
          iDestruct "Hk" as "[Hk | Hk]".
          - iDestruct "Hk" as (qL0 σlock0 l00) "(Hf & (%HIR0_lock & %Heq0 & %Hone) & Hy)".
            iLeft.
            iExists qL0, σlock0, l00.
            iFrame.
            iPureIntro.
            repeat split; auto.
            { by rewrite HIR_same. }
            by rewrite Hsame.
          - iDestruct "Hk" as (qL0) "(Hf & (%HIR0_empty & %Hzero))".
            iRight.
            iExists qL0.
            iFrame.
            iPureIntro.
            split. by rewrite HIR_same.
            by rewrite Hsame.
      }
      iAssert (lock_inv sh l R)%I with "[Hlk Hi]" as "Hl".
      { rewrite /lock_inv. iExists l1. by iFrame. }
      iDestruct (resource_map.resource_map_auth_valid with "Hrs") as %(_ & Hvcur).
      iDestruct (rmap_auth_frag_permMapLt_valid γ q σcur (σ1 ⋅ σlock) Hvcur
          with "[$Hauth $Hfrag]")
        as %(Hv1 & Hlt1).
      assert (Hlt_store : permMapLt (perm_of_rmap (σ1R ⋅ σlock)) (getMaxPerm m_global')).
      { unfold σ1R.
        etransitivity; try apply Hlt1.
        rewrite /m_global' /getMaxPerm /Mem_store_unchecked //. }
      rewrite /lock_inv.
      iDestruct "Hl" as (laddr) "(%Hval0 & HLK & Hown)".
      assert (Hl0 : laddr = l1).
      { unfold val2adr in Hval0, Hval.
        destruct l; simpl in *; try contradiction. congruence. }
      subst laddr.
      pose proof (mem_equiv.useful_permMapLt_trans Hltσcur Hltσcur) as Hlt_pre.
      assert (Hcoh_pre : coherent (restrPermMap Hlt_pre) σcur).
      { rewrite (restrPermMap_idem Hlt_pre).
        replace (restrPermMap (permMapLt_restr Hlt_pre)) with (restrPermMap Hltσcur); try done.
        apply restr_proof_irr.
      }
      iAssert (frag_mem_auth (restrPermMap Hltσcur) σcur) with "[Hrs]" as "Hmem_pre".
      { rewrite /frag_mem_auth.
        iExists Hlt_pre.
        iFrame "Hrs".
        by iPureIntro.
      }
      (* Store 0 into the lock and preserve frag_mem_auth. *)
      iMod (frag_mem_auth_store_unchecked_lock_zero_restr m σcur Hltσcur sh l1.1 l1.2 (Vptrofs Ptrofs.zero) with "Hmem_pre HLK") as (Hlt_post_local) "[Hmem_post_local HLK]".
      (* Extract post-store coherence from that frag_mem_auth. *)
      rewrite /frag_mem_auth.
      iDestruct "Hmem_post_local" as (Hlt_inner) "(%Hcoh_inner & Hrs)".
      assert (Hcoh_local : coherent (restrPermMap Hlt_post_local) σcur).
      { rewrite (restrPermMap_idem Hlt_inner) in Hcoh_inner.
        replace (restrPermMap (permMapLt_restr Hlt_inner)) with (restrPermMap Hlt_post_local) in Hcoh_inner; try done.
        apply restr_proof_irr.
      }
      (* σcur is also below the max permission of the global post-store memory. *)
      assert (Hltσcur' : permMapLt (perm_of_rmap σcur) (getMaxPerm m_global')).
      { unfold m_global'.
        rewrite /m_global' /getMaxPerm /Mem_store_unchecked //. }
      assert (Hofs' : Ptrofs.intval (Ptrofs.repr l1.2) = l1.2).
      { by change (Ptrofs.Z_mod_modulus l1.2 = l1.2). }
      assert (Hcontents_post : Mem.mem_contents (Mem_store_unchecked Mptr (restrPermMap Hltσcur) l1.1 l1.2 (Vptrofs Ptrofs.zero)) = Mem.mem_contents m_global').
      { rewrite /m_global' Hofs' /Mem_store_unchecked /= /Mem_store_unchecked_contents mem_contents_restrPermMap //. }

      assert (Hnext_post : Mem.nextblock (Mem_store_unchecked Mptr (restrPermMap Hltσcur) l1.1 l1.2 (Vptrofs Ptrofs.zero)) = Mem.nextblock m_global').
      { by rewrite /m_global' Hofs' /Mem_store_unchecked /=. }
      assert (Hmax_post : getMaxPerm (Mem_store_unchecked Mptr (restrPermMap Hltσcur) l1.1 l1.2 (Vptrofs Ptrofs.zero)) = getMaxPerm m_global').
      { rewrite /m_global' /getMaxPerm /Mem_store_unchecked /=.
        exact (@restr_Max_eq (perm_of_rmap σcur) m Hltσcur).
      }
      pose proof (mem_equiv.useful_permMapLt_trans Hlt_store Hltσcur') as Hlt_cur.
      assert (Hcoh_cur : coherent (restrPermMap Hlt_cur) σcur).
      { unfold coherent in Hcoh_local |- *.
        intro loc.
        destruct (Hcoh_local loc) as [Hnb [Hcontents Haccess]].
        split.
        - intro Hge.
          apply Hnb.
          rewrite restrPermMap_nextblock.
          rewrite !restrPermMap_nextblock in Hge.
          rewrite Hnext_post.
          exact Hge.

        - split.
          + unfold contents_cohere, contents_at in Hcontents |- *.
            rewrite !restrPermMap_contents in Hcontents |- *.
            intros v Hv.
            specialize (Hcontents v Hv).
            unfold juicy_mem.contents_at in Hcontents |- *.
            rewrite <- Hcontents_post.
            exact Hcontents.
          + unfold access_cohere.
            destruct loc as [b ofs].
            by rewrite access_at_restrPermMap_perm_res.
      }
      (* Build exactly the frag_mem_auth required by the target. *)
      iAssert (frag_mem_auth (restrPermMap Hlt_store) σcur) with "[Hrs]" as "Hmem_final".
      {
        rewrite /frag_mem_auth.
        iExists Hlt_cur.
        iFrame "Hrs".
        by iPureIntro.
      }
      (* Finish the update. *)
      iModIntro.
      iExists σlock, σcur.
      iSplit.
      + iPureIntro.
        split; try done.
        exists l0. split; auto. 
      + iExists Hlt_store. 
        iFrame "Hmem_final Hauth Hfrag Hls HR".
        iExists l1.
        iFrame "HLK Hown".
        by iPureIntro.
  - iDestruct "Hhere" as (qL) "(Hf & (%HIRempty & %Hzero))".
    rewrite Hzero in Hload. inv Hload.
  Qed.

  Lemma frag_mem_auth_restr_to_global `{!VSTGS () Σ} (m : mem) (p : access_map)
    (Hlt : permMapLt p (getMaxPerm m)) (σ : rmap) :
    frag_mem_auth (restrPermMap Hlt) σ ⊢ frag_mem_auth m σ.
  Proof.
    rewrite /frag_mem_auth.
    iIntros "H".
    iDestruct "H" as (Hlt') "(%Hcoh & Hauth)".
    pose proof (permMapLt_restr Hlt') as Hlt_global.
    iExists Hlt_global.
    iFrame.
    iPureIntro.
    split; auto.
    replace (restrPermMap Hlt_global) with (restrPermMap (permMapLt_restr Hlt')).
    - by rewrite <- (restrPermMap_idem Hlt').
    - apply restr_proof_irr.
  Qed.

  (* Lemma invariant_acquire (tp : dtp) (i : nat) (cnti : containsThread tp i) (c : state)
    (newThreadPerm : access_map) (l : address) (l0 : lock_info) (Hinv : invariant tp)
    (Hlock : lockRes tp l = Some l0) (Hjoin : permMapJoin l0 (getThreadR cnti) newThreadPerm) :
    invariant (updLockSet (updThread cnti (Kresume c Vundef) newThreadPerm) l empty_map).
  Proof.
    destruct Hinv as [no_race_thr0 no_race_lr0 no_race0 lockRes_valid0].
    constructor.
    - intros i0 j cnti0 cntj Hneq.
      pose proof (cntUpdateL' (tp := updThread cnti (Kresume c Vundef) newThreadPerm) (j := i0) l empty_map cnti0) as cnti0_upd.
    pose proof (cntUpdateL' (tp := updThread cnti (Kresume c Vundef) newThreadPerm) (j := j) l empty_map cntj) as cntj_upd.
    rewrite (gLockSetRes l _ cnti0_upd cnti0).
    rewrite (gLockSetRes l _ cntj_upd cntj).
    destruct (Nat.eq_dec i0 i) as [Hi0 | Hi0]; destruct (Nat.eq_dec j i) as [Hj | Hj].
    + subst. contradiction.
    + subst i0.
      rewrite (gssThreadRes cnti (Kresume c Vundef) newThreadPerm cnti0_upd).
      pose proof (cntUpdate' _ _ _ cntj_upd) as cntj_old.
      rewrite gsoThreadRes; auto.
      unfold permMapsDisjoint.
      intros b ofs.
      specialize (Hjoin b ofs).

      pose proof (no_race0 i l cnti l0 Hlock) as Hil.
      pose proof (no_race0 j l cntj_old l0 Hlock) as Hjl.
      pose proof (no_race_thr0 i j cnti cntj_old Hneq) as Hij.

      specialize (Hil b ofs) as [u1 Hu1].
      specialize (Hjl b ofs) as [u2 Hu2].
      specialize (Hij b ofs) as [u3 Hu3].
      destruct (l0 # b ofs) as [pl |] eqn:Hl;
        destruct ((getThreadR cnti) # b ofs) as [pi |] eqn:Hi;
        destruct (newThreadPerm # b ofs) as [pn |] eqn:Hn;
        destruct ((getThreadR cntj_old) # b ofs) as [pj |] eqn:Hj0;
        repeat match goal with
          | p : permission |- _ => destruct p
          end;
        simpl in *;
        try discriminate;
        try (inversion Hjoin; subst; clear Hjoin);
        simpl in *;
        try discriminate;
        eexists; try auto.
        reflexivity.

      destruct (l0 # b ofs) as [pl |] eqn:El;
        destruct ((getThreadR cnti) # b ofs) as [pt |] eqn:Et;
        destruct (newThreadPerm # b ofs) as [pn |] eqn:En;
        destruct ((getThreadR cntj_old) # b ofs) as [pj |] eqn:Ej;
        simpl in *;
        try solve [inversion Hjoin].

      all:
        repeat match goal with
          | p : permission |- _ => destruct p
          end;
        simpl in *;
        try discriminate;
        try inversion Hjoin;
        subst;
        try (eexists; reflexivity).

      
      eapply Hjoin_safe.
      * apply permMapsDisjoint_comm.
        eapply no_race0; eauto.
      * eapply no_race_thr0; eauto.

    + subst j.
      pose proof (cntUpdate' _ _ _ cnti0_upd) as cnti0_old.
      rewrite gsoThreadRes; auto.
      rewrite (gssThreadRes cnti
                 (Kresume c Vundef) newThreadPerm cntj_upd).
      apply permMapsDisjoint_comm.
      eapply Hjoin_safe.
      * apply permMapsDisjoint_comm.
        eapply no_race0; eauto.
      * eapply no_race_thr0; eauto.
        intro Heq.
        apply Hi0.
        symmetry; exact Heq.

    + pose proof (cntUpdate' _ _ _ cnti0_upd) as cnti0_old.
      pose proof (cntUpdate' _ _ _ cntj_upd) as cntj_old.
      rewrite gsoThreadRes; auto.
      rewrite gsoThreadRes; auto.
      eapply no_race_thr0; eauto.

  - intros laddr1 laddr2 rmap1 rmap2 Hneq Hres1 Hres2.
    destruct (eq_dec laddr1 l) as [H1 | H1];
      destruct (eq_dec laddr2 l) as [H2 | H2].

    + subst.
      contradiction.

    + subst laddr1.
      rewrite OrdinalPool.gssLockRes in Hres1.
      inversion Hres1; subst.
      apply empty_disjoint'.

    + subst laddr2.
      rewrite OrdinalPool.gssLockRes in Hres2.
      inversion Hres2; subst.
      apply permMapsDisjoint_comm.
      apply empty_disjoint'.

    + rewrite OrdinalPool.gsoLockRes in Hres1; auto.
      rewrite OrdinalPool.gsoLockRes in Hres2; auto.
      rewrite gsoThreadLPool in Hres1.
      rewrite gsoThreadLPool in Hres2.
      eapply no_race_lr0; eauto.

  - intros i0 laddr cnti0 rmap Hres.
    pose proof
      (cntUpdateL'
         (tp := updThread cnti (Kresume c Vundef) newThreadPerm)
         (j := i0) l empty_map cnti0) as cnti0_upd.

    rewrite (gLockSetRes l empty_map cnti0_upd cnti0).

    destruct (eq_dec laddr l) as [Hladdr | Hladdr].

    + subst laddr.
      rewrite OrdinalPool.gssLockRes in Hres.
      inversion Hres; subst.
      apply permMapsDisjoint_comm.
      apply empty_disjoint'.

    + rewrite OrdinalPool.gsoLockRes in Hres; auto.
      rewrite gsoThreadLPool in Hres.

      destruct (Nat.eq_dec i0 i) as [Hi0 | Hi0].

      * subst i0.
        rewrite (gssThreadRes cnti
                   (Kresume c Vundef) newThreadPerm cnti0_upd).
        eapply Hjoin_safe.
        -- eapply no_race_lr0; eauto.
        -- eapply no_race0; eauto.

      * pose proof (cntUpdate' _ _ _ cnti0_upd) as cnti0_old.
        rewrite gsoThreadRes; auto.
        eapply no_race0; eauto.

  - eapply updLockSet_lr_valid_existing; try done.
Qed.
    
    
    (* prove separately *)
  Admitted. *)

  Lemma acquire_safe (γ : gname) (tp : dtp) (m : mem) (ls : gset address) (i : nat) (q : Qp) (σ1 : rmap) (Htp_wf : threads_wellformed tp) (Hinvariant : invariant tp) (Hcompat : mem_compatible tp m)
    (Hlocks : locks_coherent tp m ls) (cnti : containsThread tp i)
    (Hlt : permMapLt (perm_of_rmap σ1) (getMaxPerm m))
    (Heq1 : mem_equiv.access_map_equiv (perm_of_rmap σ1) (getThreadR cnti))
    (argsty : typelist) (retty : type) (cc : calling_convention) (k : cont) (args : list val)
    (Hi : getThreadC cnti = Kblocked (Callstate (Ctypes.External LOCK argsty retty cc) args k))
    (Hcoh : coherent (restrPermMap Hlt) σ1)
    (Hlt0 : permMapLt (perm_of_rmap σ1) (getMaxPerm (restrPermMap Hlt)))
    (x : Jext_spec_type (concurrent_ext_spec CS ext_link) LOCK):
  ⊢ other_threads_safe γ tp i -∗
    Jext_spec_pre (concurrent_ext_spec CS ext_link) LOCK x (genv_symb_injective ge) (sig_args (ef_sig LOCK)) args -∗
    ▷ post_safe γ q x argsty retty cc args k -∗ lock_state1 γ m ls (lockRes tp) -∗
    thread_state_interp γ (getThreadR cnti) q m σ1 () -∗
    |={⊤}[∅]▷=>
      ∃ (tp' : t) (m' : mem) (ev : Events.sync_event) (σnew : rmap),
        ⌜threads_wellformed tp' ∧ invariant tp' ∧ mem_compatible tp' m' ∧
          locks_coherent tp' m' ls ∧ syncStep true cnti Hcompat tp' m' ev⌝ ∧
   ext_auth () ∗ rmap_auth γ σnew ∗ frag_mem_auth m' σnew ∗ threads_safe tp' γ ∗
     lock_state1 γ m' ls (lockRes tp').
  Proof.
    iIntros "Hsafe Hpre Hpost Hls S".
    iDestruct "S" as (σcur) "(%Heq & Hmem & Hauth & Hfrag & Hext)".
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
    Check lock_inv_in_lock_state.
    iDestruct (lock_inv_in_lock_state γ m ls (lockRes tp) sh l R with "Hls Hl") as "%Hin".
    destruct Hin as (l1 & Hval & Hl).
    pose proof Hlocks as Hlocks'.
    specialize (Hlocks l1 Hl).
    destruct Hlocks as (HlockRes & ? & ?).
    destruct (lockRes tp l1) eqn:E; last done.
    assert (l = Vptr l1.1 (Ptrofs.repr l1.2)) as Hl1.
    { destruct l; simpl in Hval; try contradiction.
      destruct l1 as [b1 ofs1]; inv Hval; simpl.
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
    assert (HlR : lockRes tp (l1.1, Ptrofs.intval (Ptrofs.repr l1.2)) = Some l0).
    { destruct l1; simpl; by rewrite Hofs. }
    destruct H as [[Ho Hl0_empty] | Ho].
    - (* acquire fails *)
      admit.
    - (* acquire succeeds *)
      iDestruct "Hmem" as "(%Hltσcur & %Hσcur & Hrs)".
      set (ret := (None : option val)).
      set (m_global' := Mem_store_unchecked Mptr m l1.1 (Ptrofs.intval (Ptrofs.repr l1.2)) (Vptrofs Ptrofs.zero)).
      pose (σcurR := (σcur : resource_map.rmapUR share address (leibnizO resource))).
      pose (σ1R := (σ1 : resource_map.rmapUR share address (leibnizO resource))).
      (*
        local: σ1 ---- acquire σlock ----> σ1R ⋅ σlock
        global: σcur ---------------------> σnew
        and we must produce: frag_mem_auth ... σnew
        rmap_auth γ σnew
        rmap_frag γ q (σ1R ⋅ σlock)
       *)
      iMod (lock_acquire_rmap_update γ q m ls (lockRes tp) l l1 sh R σcur σ1 Hval Ho Hofs Hltσcur Hσcur
             with "Hl Hls Hrs Hauth Hfrag") as "Hacquire".

      iDestruct "Hacquire" as (σlock σnew) "(%Hσlock & Hacquire)".
      destruct Hσlock as [Hvalid_join Hlock_holds].
      (* iAssert (∃ (σlock σnew : rmap),
                  ⌜✓ (σ1R ⋅ σlock) ∧ lock_rmap_holds R σlock⌝ ∧
                    ∃ Hlt_store : permMapLt (perm_of_rmap (σ1R ⋅ σlock)) (getMaxPerm m_global'),
                      frag_mem_auth (restrPermMap Hlt_store) σnew ∗
                        rmap_auth γ σnew ∗ rmap_frag γ q (σ1R ⋅ σlock) ∗
                        lock_state m_global' ls ∗ lock_inv sh l R ∗ ▷ R)%I
        with "[-Hsafe Hpost Hext]" as "Hacquire". 
      {
        
        (*
          This is the NEW acquire-update lemma/proof.
          It consumes the current:             
          Hrs   : resource_map_auth ... 1 σcur
          Hauth : rmap_auth γ σcur
          Hfrag : rmap_frag γ q σ1

          and produces:
          σnew              global authoritative rmap
          σ1R ⋅ σlock       selected-thread post rmap
          frag_mem_auth ... σnew
          rmap_auth γ σnew
          rmap_frag γ q (σ1R ⋅ σlock)
         *)
        admit.
      }. *)
      iDestruct "Hacquire" as (Hlt_store) "(Hmem_post & Hauth_post & Hfrag_post &
                                          Hls_store & Hl & HR)".
      set (σpost := σ1R ⋅ σlock).
      set (m_thread' := restrPermMap Hlt_store).
      iAssert (thread_state_interp γ (getCurPerm m_thread') q m_thread' σpost ())
        with "[Hmem_post Hauth_post Hfrag_post Hext]" as "Hstate".
      { rewrite /thread_state_interp /m_thread' /σpost.
        iExists σnew.
        iSplit; iFrame.
        iPureIntro.
        pose proof (mem_equiv.getCur_restr (perm_of_rmap (σ1R ⋅ σlock)) m_global' Hlt_store)
          as Hcur.
        unfold mem_equiv.access_map_equiv in Hcur |- *.
        intros b.
        symmetry.
        apply Hcur.
      }
      Local Opaque lock_state.
      rewrite step_fupd_fupd.
      iApply step_fupd_intro; first done.
      iNext.
      iSpecialize ("Hpost" $! ret m_thread' σpost () with "[]").
      { iPureIntro. subst; repeat split; auto. }
      iMod "Hpost" as "Hpost".
      iAssert (∃ c' : CC_core, ⌜after_external (cl_core_sem ge) ret (Callstate (Ctypes.External LOCK argsty retty cc) [l] k) m_thread' = Some c'⌝ ∧
                thread_state_interp γ (getCurPerm m_thread') q m_thread' σpost () ∗
                jsafe_frag γ q ⊤ () c')%I with "[Hpost Hstate HR Hl]" as "HafterPost".
      {
        iApply ("Hpost" with "Hstate").
        simpl.
        iExists (l, sh, R).
        iSplit; auto.
        rewrite /PROPx /PARAMSx /GLOBALSx /LOCALx /SEPx /=.
        iSplit; auto.
        iFrame. }
      iDestruct "HafterPost" as (c') "(%Hafter & Hstate & Hjsafe)".
      iUnfold thread_state_interp in "Hstate".
      iDestruct "Hstate" as (σnew2) "(%Heq_post & Hmem_thread & Hauth_post & Hfrag_post & Hext2)".
      iAssert (frag_mem_auth m_global' σnew2) with "[Hmem_thread]" as "Hmem_global".
      { rewrite /m_thread'.
        iApply (frag_mem_auth_restr_to_global m_global' (perm_of_rmap (σ1R ⋅ σlock))
                  Hlt_store σnew2 with "Hmem_thread").
      }
      (*
 global σcur              local σ1
     |                       |
     | acquire               | + σlock
     v                       v
global σnew              σpost = σ1 ⋅ σlock
     |                       |
frag_mem_auth            rmap_frag
       *)
      assert (Hlt_post : permMapLt (perm_of_rmap σpost) (getMaxPerm m)).
      { unfold σpost. unfold m_global' in Hlt_store. simpl in Hlt_store. done. }
      set (δ := PTree.map (fun b fmax ofs =>
                             match fmax ofs with
                             | Some _ => Some ((perm_of_rmap σpost) # b ofs)
                             | None => None
                             end) (getMaxPerm m).2).
      assert (Hcompute : mem_equiv.access_map_equiv
                           (computeMap (getThreadR cnti) δ) (perm_of_rmap σpost)).
      { pose proof (Hcompat i cnti) as Hlt_old.
        unfold mem_equiv.access_map_equiv.
        intros b.
        extensionality ofs.
        assert (none_of_lt : forall pm, permMapLt pm (getMaxPerm m) -> (getMaxPerm m) # b ofs = None ->
                                   pm # b ofs = None).
        { intros pm Hpm Hmax.
          specialize (Hpm b ofs).
          rewrite Hmax in Hpm.
          destruct (pm # b ofs) as [p |] eqn:Hpm_at; done.
        }
        case_eq (Maps.PTree.get b (getMaxPerm m).2).
        - intros fmax Hb.
          case_eq (fmax ofs).
          + intros pmax Hofs1.
            eapply computeMap_1 with
              (df :=
                 fun ofs0 =>
                   match fmax ofs0 with
                   | Some _ => Some ((perm_of_rmap σpost) # b ofs0)
                   | None => None end).
            * rewrite Maps.PTree.gmap Hb //.
            * rewrite Hofs1 //.
          + intros Hofs1. transitivity ((getThreadR cnti) # b ofs).
            * eapply computeMap_2 with
                (df := fun ofs0 =>
                         match fmax ofs0 with
                         | Some _ => Some ((perm_of_rmap σpost) # b ofs0)
                         | None => None
                         end).
              ** rewrite Maps.PTree.gmap Hb //.
              ** rewrite Hofs1 //.
            * assert (Hmax_none : (getMaxPerm m) # b ofs = None).
              { rewrite /Maps.PMap.get Hb //. }
              rewrite (none_of_lt _ Hlt_old Hmax_none).
              rewrite (none_of_lt _ Hlt_post Hmax_none).
              done.
        - intros Hb.
          transitivity ((getThreadR cnti) # b ofs).
          + eapply computeMap_3.
            rewrite Maps.PTree.gmap Hb //.
          + assert (Hmax_none : (getMaxPerm m) # b ofs = None).
            {
              rewrite /Maps.PMap.get Hb.
              pose proof (Max_isCanonical m) as Hcan.
              unfold isCanonical in Hcan.
              apply (f_equal (fun f => f ofs)) in Hcan.
              simpl in *.
              done.
            }
            rewrite (none_of_lt _ Hlt_old Hmax_none).
            rewrite (none_of_lt _ Hlt_post Hmax_none).
            done. }

      set (newThreadPerm := computeMap (getThreadR cnti) δ).
      assert (Heq_acq : mem_equiv.access_map_equiv (perm_of_rmap σpost) newThreadPerm).
      {
        unfold newThreadPerm.
        unfold mem_equiv.access_map_equiv in Hcompute |- *.
        intros b.
        symmetry.
        apply (Hcompute b).
      }
      
      set (l1' := (l1.1, Ptrofs.intval (Ptrofs.repr l1.2))).
      set (tp' := updLockSet (updThread cnti (Kresume c Vundef) newThreadPerm) l1' empty_map).
      iAssert (threads_safe tp' γ) with "[Hsafe Hjsafe Hfrag_post]" as "Hthreads".
      { rewrite /threads_safe.
        assert (Hnum : pos.n (OrdinalPool.num_threads tp') = pos.n (OrdinalPool.num_threads tp)).
        { subst tp'; auto. }
        rewrite Hnum.
        iApply "Hsafe".
        - (* every non-selected thread *)
          iIntros "!>" (k0 y (-> & ?)%lookup_seq Hneq) "Hy".
          replace (0 + k0) with k0 in * by lia.
          assert (Hneq' : i <> k0) by lia.
          iDestruct "Hy" as (q0 σ0 cnty) "(%Heqy & Hsafe_y & Hfrag_y)".
          assert (cnty' : containsThread tp' k0).
          { subst tp'; auto. }
          iExists q0, σ0, cnty'.
          iSplit; try iFrame.
          { iPureIntro. subst tp'. rewrite gLockSetRes gsoThreadRes; eauto. }
          rewrite /thread_safe.
          iDestruct "Hsafe_y" as (cnty0) "Hsafe_y".
          assert (Hcnty : cnty0 = cnty) by apply proof_irrelevance.
          subst cnty0.
          iExists cnty'.
          subst tp'. rewrite gLockSetCode gsoThreadCode; auto.
        - (* selected thread i *)
          assert (cnti' : containsThread tp' i).
          { subst tp'; auto. }
          iExists q, σpost, cnti'.
          iFrame.
          iSplit.
          { iPureIntro. subst tp'. by rewrite gLockSetRes gssThreadRes. }
          rewrite /thread_safe.
          iExists cnti'.
          subst tp'.
          rewrite gLockSetCode gssThreadCode /=.
          iIntros (c'') "%Hafter''".
          change (cl_after_external None c = Some c') in Hafter.
          assert (c'' = c').
          { change (Some (Returnstate Vundef k) = Some c') in Hafter.
            rewrite Hafter in Hafter''. inv Hafter''. done. }
          rewrite H //. }
      set (ev := Events.acquire l1' (Some (build_delta_content δ m_global'))).
      iExists tp', m_global', ev, σnew2.
      rewrite /lock_state1.
      iModIntro.
      iSplit.
      2: {
        iFrame "Hext2 Hauth_post Hmem_global Hthreads".
        rewrite /lock_state1 /m_global'.
        iDestruct "Hls_store" as (x0) "(Hdom & Hown & Hmap)".
        iExists x0.
        iFrame "Hdom Hown".
        iApply (big_sepM_mono with "Hmap").
        iIntros (a R0 Hlookup) "H".
        assert (HlockRes_tp' : forall a, lockRes tp' a = if decide (a = l1) then Some empty_map
                                                    else lockRes tp a).
        {
          intro a0.
          unfold tp', l1'.
          destruct (decide (a0 = l1)) as [Heqa | Hneqa].
          - subst a0.
            assert (Hl1' : (l1.1, Ptrofs.intval (Ptrofs.repr l1.2)) = l1).
            { destruct l1 as (b & ofs); simpl in *; f_equal. done. }
            rewrite Hl1'. simpl.
            by rewrite OrdinalPool.gssLockRes.
          - assert (Hl1' : (l1.1, Ptrofs.intval (Ptrofs.repr l1.2)) = l1).
            { destruct l1 as (b & ofs); simpl in *; f_equal. done. }
            rewrite Hl1'.
            simpl.
            by rewrite OrdinalPool.gsoLockRes.
        }
        iDestruct "H" as "[Hlocked | Hunlocked]"; try by iRight.
        - (* unlocked *)
          iLeft.
          iDestruct "Hlocked" as (qL σlock0 l2) "(Hfrag & (%HIR & %Heq_lock & %Hload) & HR)".
          iExists qL, σlock0, l2.
          iFrame.
          iSplit; try iPureIntro; auto.
          repeat split; auto.
          simpl.
          change (lockRes tp' a = Some l2).
          etransitivity; eauto.
        - iRight.
          iDestruct "Hunlocked" as (qL) "(Hfrag & (%HIR & %Hload))".
          iExists qL.
          iFrame.
          iPureIntro.
          split.
          + change (lockRes tp' a = Some empty_map).
            etransitivity; eauto.
          + apply Hload.
      }
      assert (syncStep true cnti Hcompat tp' m_global' ev /\ threads_wellformed tp'
                 ∧ invariant tp'
                 ∧ mem_compatible tp' m_global'
                 ∧ locks_coherent tp' m_global' ls ) as Hstep.
      { split.
        eapply step_acquire with (pmap := l0) (b := l1.1) (ofs := Ptrofs.repr l1.2) (virtueThread := δ); try done.
        - (* δ bounded *)
          unfold δ, bounded_maps.sub_map.
          intros b fδ Hfδ.
          rewrite PTree.gmap in Hfδ.
          destruct (((getMaxPerm m).2 !! b)%maps)
            as [fmax |] eqn:Hmax; simpl in Hfδ; try discriminate.
          inv Hfδ.
          exists fmax.
          split; first done.
          intros ofs Hδ.
          destruct (fmax ofs); simpl in Hδ; try discriminate; done.
        - (* at_external *)
          rewrite Hl1 //.
        - (* load = 1 *)
          unfold unchecked_load; simpl.
          rewrite Hofs.
          f_equal. done.
        - (* new thread permission is below max *)
          intros b ofs.
          unfold mem_equiv.access_map_equiv in Hcompute.
          specialize (Hcompute b).
          rewrite Hcompute.
          apply Hlt_post.
        - (* unchecked store *)
          unfold m_global'.
          unfold unchecked_store, Mem_store_unchecked.
          f_equal.
          eapply Mem.mkmem_ext; simpl; reflexivity.
        - unfold permMapJoin.
          intros b ofs.
          destruct Hlock_holds as (l0' & Hl0' & Heq_lock).
          assert (Hl0eq : l0' = l0) by congruence.
          subst l0'.
          assert (Hlock : forall b ofs,
                     l0 # b ofs = (perm_of_rmap σlock) # b ofs).
          {
            intros b0 ofs0.
            unfold mem_equiv.access_map_equiv in Heq_lock.
            specialize (Heq_lock b0).
            exact (f_equal (fun f => f ofs0) Heq_lock).
          }
          rewrite (Hlock b ofs).
          assert (Hthread : (getThreadR cnti) # b ofs = (perm_of_rmap σ1R) # b ofs).
          { unfold σ1R.
            unfold mem_equiv.access_map_equiv in Heq1.
            specialize (Heq1 b).
            exact (f_equal (fun f => f ofs) (eq_sym Heq1)).
          }
          rewrite Hthread.
          unfold mem_equiv.access_map_equiv in Hcompute.
          specialize (Hcompute b).
          rewrite Hcompute.
          unfold σpost.
          apply ((perm_of_rmap_op_permMapJoin σ1R σlock Hvalid_join) b ofs).
        - split.
          + subst tp'.
            unfold threads_wellformed in *.
            intros j cntj'.
            rewrite gLockSetCode.
            destruct (Nat.eq_dec j i) as [-> | Hneq].
            * rewrite gssThreadCode.
              split; auto.
            * rewrite gsoThreadCode; auto.
              apply Htp_wf.
          + 

  Admitted.
      

  (*
  Lemma acquire_safe (γ : gname) (tp : dtp) (m : mem) (ls : gset address)
    (qs : gmap nat Qp) (i : nat) (q : Qp) (σ1 σ0 : rmap)
    (Htp_wf : threads_wellformed tp) (Hinvariant : invariant tp)
    (Hcompat : mem_compatible tp m) (Hlocks : locks_coherent tp m ls)
    (cnti : containsThread tp i) (Hlt : permMapLt (perm_of_rmap σ1) (getMaxPerm m))
    (Heq1 : mem_equiv.access_map_equiv (perm_of_rmap σ1) (getThreadR cnti))
    (argsty : typelist) (retty : type) (cc : calling_convention) (k : cont) (args : list val)
    (Hi : getThreadC cnti = Kblocked (Callstate (Ctypes.External LOCK argsty retty cc) args k))
    (Hcoh : coherent (restrPermMap Hlt) σ1)
    (Hlt0 : permMapLt (perm_of_rmap σ1) (getMaxPerm (restrPermMap Hlt)))
    (x : Jext_spec_type (concurrent_ext_spec CS ext_link) LOCK) :
  ⊢ other_threads_safe γ tp i -∗
    Jext_spec_pre (concurrent_ext_spec CS ext_link) LOCK x (genv_symb_injective ge) (sig_args (ef_sig LOCK)) args -∗
    ▷ post_safe γ q x argsty retty cc args k -∗ lock_state m ls -∗
               thread_state_interp γ (getThreadR cnti) q m σ1 () -∗
    |={⊤}[∅]▷=>
          ∃ (tp' : t) (m' : mem) (ev : Events.sync_event) (σnew : rmap),
        ⌜threads_wellformed tp' ∧ invariant tp' ∧ mem_compatible tp' m' ∧
          locks_coherent tp' m' ls ∧ syncStep true cnti Hcompat tp' m' ev⌝ ∧
          ext_auth () ∗ rmap_auth γ σnew ∗ frag_mem_auth m' σnew ∗
            threads_safe tp' γ ∗ lock_state m' ls.
  Proof.
    iIntros "Hsafe Hpre Hpost Hls (Hths & Hext)".
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
    iDestruct (lock_inv_in_lock_state m ls sh l R with "Hls Hl") as "%Hin".
    destruct Hin as (l1 & Hval & Hl).
    pose proof Hlocks as Hlocks'.
    specialize (Hlocks l1 Hl).
    destruct Hlocks as (HlockRes & ? & ?).
    destruct (lockRes tp l1) eqn: E; last done.
    assert (l = Vptr l1.1 (Ptrofs.repr l1.2)) as Hl1.
    { destruct l; simpl in Hval; try contradiction.
      destruct l1 as [b1 ofs1]; inv Hval; simpl.
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
    - (* acquire fails *) admit.
    - iDestruct "Hths" as "(% & Hrs)".
      set (ret := (None : option val)).
      set (m_global' := Mem_store_unchecked Mptr m l1.1 (Ptrofs.intval (Ptrofs.repr l1.2)) (Vptrofs Ptrofs.zero)).

      pose (σ0R  := (σ0 : resource_map.rmapUR share address (leibnizO resource))).
      iAssert (∃ σlock : resource_map.rmapUR share address (leibnizO resource),
            <affine>⌜✓ (σ0R ⋅ σlock) ∧ lock_rmap_holds R σlock⌝ ∗
            ∃ Hlt_store : permMapLt (perm_of_rmap (σ0R ⋅ σlock)) (getMaxPerm m_global'),
                frag_mem_auth q (restrPermMap Hlt_store) (σ0R ⋅ σlock) ∗
                  lock_state m_global' ls ∗ lock_inv sh l R ∗ ▷ R)%I
        with "[-Hsafe Hpost Hext]" as "Hacquire".
      {
        unfold frag_mem_auth.
        admit.
      }
      iDestruct "Hacquire" as (σlock) "[Hσlock Hacquire]".
      iDestruct "Hσlock" as %Hσlock.
      destruct Hσlock as [Hvalid_join Hlock_holds].
      iDestruct "Hacquire" as (Hlt_store) "(Hfrag_store & Hls_store & Hl & HR)".
      set (m_thread' := restrPermMap Hlt_store).
      set (σ' := σ0R ⋅ σlock).
      iAssert (frag_state_interp q m_thread' σ' ()) with "[Hfrag_store Hext]" as "Hstate".
      {
        rewrite /frag_state_interp /m_thread' /σ'.
        iFrame.
      }
      iDestruct "Hstate" as "(((%Hcoh_in & %Hacc_in) & Hauth_in) & Hext_in)".
      iAssert (frag_state_interp q m_thread' σ' ())
        with "[Hauth_in Hext_in]" as "Hstate".
      {
        rewrite /frag_state_interp /frag_mem_auth.
        iFrame.
        iSplit; auto.
      }
      (* iApply step_fupd_intro; first done. *)
      Local Opaque lock_state.
      rewrite step_fupd_fupd.
      iApply step_fupd_intro; first done.
      iNext.
      iSpecialize ("Hpost" $! ret m_thread' σ' () with "[]").
      { iPureIntro; subst; repeat split; auto. }
      iMod "Hpost" as "Hpost".
      iAssert (∃ (c' : CC_core) (σ2 : rmap),
            ⌜after_external (cl_core_sem ge) ret (Callstate (Ctypes.External LOCK argsty retty cc) [l] k) m_thread' = Some c'⌝ ∧ frag_state_interp q m_thread' σ2 () ∗ jsafe_frag q ⊤ () c')%I
        with "[Hpost Hstate HR Hl]" as "HafterPost".
      {
        iApply ("Hpost" with "Hstate").
        simpl.
        iExists (l, sh, R).
        iSplit; auto.
        rewrite /PROPx /PARAMSx /GLOBALSx /LOCALx /SEPx /=.
        iSplit; auto.
        iFrame.
      }
      iDestruct "HafterPost" as (c' σ2) "(%Hafter & Hfrag & Hjsafe)".
      iDestruct "Hfrag" as "(((%Hcoh2 & %Hacc2) & Hauth2) & Hext2)".
      assert (mem_equiv.access_map_equiv (perm_of_rmap σ2) (perm_of_rmap σ')) as Hperm_eq.
      { eapply coherent_perm_of_rmap_eq; eauto. }
      rewrite /frag_state_interp /frag_mem_auth.
      set (l1' := (l1.1, Ptrofs.intval (Ptrofs.repr l1.2))).
      (*
      set (tp' := updLockSet (updThread cnti (Kresume c Vundef) (perm_of_rmap σ', (getThreadR cnti))) l1' (empty_map, empty_map)).
      pose proof Hcoh2 as Hcoh2'.
      apply coherent_restrPermMap_of_coherent in Hcoh2'.
      destruct Hcoh2' as (Hlt2 & Hcoh2').
      iAssert (frag_mem_auth q (restrPermMap Hlt2) σ2) with "[Hauth2]" as "Hfrag2".
      { rewrite /frag_mem_auth.
        iFrame.
        iPureIntro.
        do 2 split; auto.
        unfold mem_equiv.access_map_equiv.
        intros. 
        admit.
      }
      assert (cnti' : containsThread tp' i).
      { subst tp'; auto. }
      iAssert (thread_safe tp' i q) with "[Hjsafe]" as "HcurSafe".
      { rewrite /thread_safe.
        subst tp'.
        simpl.
        iExists cnti'.
        assert (Hcnt : cnti' = cnti) by apply proof_irrelevance.
        rewrite Hcnt.
        rewrite eqtype.eq_refl.
        iIntros (c'0) "%Hafter0".
        change (cl_after_external None c = Some c') in Hafter.
        assert (c'0 = c') by congruence.
        subst c'0.
        iFrame.
      }
 
      set (Ψ := fun (_ y : nat) => (∃ (q0 : Qp) (σ : rmap) (cnty : containsThread tp' y)
           (Hlt0 : permMapLt (perm_of_rmap σ) (getMaxPerm m_global')),
           ⌜qs !! y = Some q0 ∧ mem_equiv.access_map_equiv (perm_of_rmap σ) (getThreadR cnty).1⌝
            ∗ thread_safe tp' y q0 ∗ frag_mem_auth q0 (restrPermMap Hlt0) σ)%I).
      iAssert (∃ Hlt2g : permMapLt (perm_of_rmap σ2) (getMaxPerm m_global'),
            frag_mem_auth q (restrPermMap Hlt2g) σ2)%I with "[Hfrag2]" as "Hfrag2g".
      {
        assert (Hlt2g : permMapLt (perm_of_rmap σ2) (getMaxPerm m_global')).
        { erewrite <- restr_Max_eq; eauto. }
        iExists Hlt2g.
        rewrite restrPermMap_twice_eq //.
      }
      iDestruct "Hfrag2g" as (Hlt2g) "Hfrag2g".
      iAssert (Ψ i i) with "[HcurSafe Hfrag2g]" as "Hii".
      { rewrite /Ψ.
        iExists q, σ2, cnti', Hlt2g.
        iFrame.
        iPureIntro.
        split.
        - exact Hq.
        - subst tp'.
          assert (Hcnt : cnti' = cnti) by apply proof_irrelevance.
          rewrite Hcnt /= eqtype.eq_refl //. }
      iSpecialize ("Hsafe" $! Ψ).
      iAssert ([∗ list] k0 ↦ y ∈ seq 0 (pos.n (OrdinalPool.num_threads tp)), Ψ k0 y)%I
        with "[Hsafe Hii]" as "HallSafe".
      { iApply ("Hsafe" with "[] Hii").
        iModIntro.
        iIntros (k0 y Hlookup Hneq) "Hy".
        iDestruct "Hy" as (q0 σ cnty Hlt1) "((%Hqy & %Heqy) & HsafeY & HfragY)".
        apply lookup_seq in Hlookup as [Hy _].
        simpl in Hy.
        subst k0.
        iAssert (∃ Hlt1g : permMapLt (perm_of_rmap σ) (getMaxPerm m_global'),
              frag_mem_auth q0 (restrPermMap Hlt1g) σ)%I with "[HfragY]" as "HfragYg".
        { iDestruct "HfragY" as "((% & %) & H)".
          rewrite /m_global' /Mem_store_unchecked /getMaxPerm /=.
          iExists Hlt1.
          iSplit; iFrame.
          iPureIntro.
          split; auto.
          assert (Hty : permMapLt (getThreadR cnty).1 (getMaxPerm m)).
          { intros b0 ofs0.
            pose proof Hlt1 as Hlt1'.
            specialize (Hlt1' b0 ofs0).
            unfold mem_equiv.access_map_equiv in Heqy.
            specialize (Heqy b0).
            rewrite - Heqy //.
          }
          assert (Hnonempty : nonEmptyRangeCur (restrPermMap Hty) (l1.1, Ptrofs.Z_mod_modulus l1.2)).
          { rewrite Hofs; apply (H0 y cnty Hty). }
          eapply (coherent_restrPermMap_store_unchecked_nonempty m σ ((getThreadR cnty).1)
                    l1.1 _ _ Hlt1 Hty Hlt1); eauto.
        }
        iDestruct "HfragYg" as (Hlt1g) "HfragYg".
        assert (cnty' : containsThread tp' y).
        { subst tp'; done. }
        assert (HC : getThreadC cnty' = getThreadC cnty).
        { subst tp'.
          simpl.
          destruct (eqtype.eq_op _ _) eqn: Heq.
          - exfalso.
            apply Hneq.
            rewrite /eqtype.eq_op /= in Heq.
            destruct (@eqtype.eqP ssrnat.nat_eqType y i) as [Hyi | Hnyi]; auto.
            inv Heq.
          - unfold OrdinalPool.getThreadC.
            do 2 f_equal.
            apply proof_irrelevance.
        }
        assert (HR0 : getThreadR cnty' = getThreadR cnty).
        { subst tp'.
          simpl.
          destruct (eqtype.eq_op _ _) eqn: Heq.
          - exfalso.
            apply Hneq.
            rewrite /eqtype.eq_op /= in Heq.
            destruct (@eqtype.eqP ssrnat.nat_eqType y i) as [Hyi | Hnyi]; auto.
            inv Heq.
          - unfold OrdinalPool.getThreadR.
            do 2 f_equal.
            apply proof_irrelevance.
        }
        rewrite /Ψ.
        iExists q0, σ, cnty', Hlt1g.
        iSplit.
        - iPureIntro.
          split; auto.
          rewrite HR0 //.
        - iSplitL "HsafeY".
          + iDestruct "HsafeY" as (cnty0) "HsafeY".
            assert (Hcnty0 : cnty0 = cnty) by apply proof_irrelevance.
            subst cnty0.
            iExists cnty'.
            rewrite HC //.
          + done.
      }
      iAssert (threads_safe tp' qs m_global') with "[HallSafe]" as "Hthreads".
      { rewrite /threads_safe.
        assert (Hnum : pos.n (OrdinalPool.num_threads tp') = pos.n (OrdinalPool.num_threads tp)).
        { unfold tp'; auto. }
        rewrite Hnum //.
      }
      iExists tp', m_global', _.
      iFrame.

      assert (Hdelta1 :
               exists δ1 : delta_map,
                 permMapJoin
                   l0.1
                   (getThreadR cnti).1
                   (computeMap (getThreadR cnti).1 δ1)).
      {
        assert (Hlock :
                 forall b ofs,
                   l0.1 # b ofs =
                     (perm_of_rmap σlock) # b ofs).
        { admit. }

        assert (Hthread :
                 forall b ofs,
                   (getThreadR cnti).1 # b ofs =
                     (perm_of_rmap σ0R) # b ofs).
        { admit. }

        assert (Hnew :
                 exists δ1 : delta_map,
                 forall b ofs,
                   (computeMap (getThreadR cnti).1 δ1) # b ofs =
                     (perm_of_rmap (σ0R ⋅ σlock)) # b ofs).
        { admit. }

        destruct Hnew as [δ1 Hnew].
        exists δ1.
        assert (Hvalid : ✓ (σ0R ⋅ σlock)). admit.
        unfold permMapJoin.
        intros b ofs.
        rewrite (Hlock b ofs) (Hthread b ofs) (Hnew b ofs).
        exact
          ((perm_of_rmap_op_permMapJoin σ0R σlock Hvalid) b ofs).
     }

     assert (Hdelta_exists :
               (exists (δ1 δ2 : delta_map),
                   bounded_maps.sub_map δ1 (getMaxPerm m).2 /\
                   bounded_maps.sub_map δ2 (getMaxPerm m).2 /\
                   computeMap (getThreadR cnti).1 δ1 = perm_of_rmap σ' /\
                   computeMap (getThreadR cnti).2 δ2 = (getThreadR cnti).2 /\
                   permMapJoin l0.1 (getThreadR cnti).1 (computeMap (getThreadR cnti).1 δ1) /\
                   permMapJoin l0.2 (getThreadR cnti).2 (computeMap (getThreadR cnti).2 δ2))%type).
      { set (δ1 := PTree.map (fun b fmax ofs =>
                                match fmax ofs with
                                | Some _ => Some ((perm_of_rmap σ') # b ofs)
                                | None => None
                                end) (getMaxPerm m).2).
        set (δ2 := PTree.empty (Z -> option (option permission))).
        assert (Hδ1eq : mem_equiv.access_map_equiv
                          (computeMap (getThreadR cnti).1 δ1) (perm_of_rmap σ')).
        { pose proof (proj1 (Hcompat i cnti)) as Hlt_old.
          pose proof Hlt2g as Hlt_new.
          rewrite Hperm_eq in Hlt_new.
          change (permMapLt (perm_of_rmap σ') (getMaxPerm m)) in Hlt_new.
          unfold mem_equiv.access_map_equiv.
          intros b; extensionality ofs.
          assert (none_of_lt :
                   forall pm, permMapLt pm (getMaxPerm m) -> (getMaxPerm m) # b ofs = None ->
                     pm # b ofs = None).
          { intros pm Hpm Hmax.
            specialize (Hpm b ofs).
            rewrite Hmax in Hpm.
            destruct (pm # b ofs) as [p |] eqn:Hpm_at; done.
          }
          case_eq (Maps.PTree.get b (getMaxPerm m).2).
          - intros fmax Hb.
            case_eq (fmax ofs).
            + intros pmax Hofs1.
              eapply computeMap_1 with
                (df := fun ofs0 => match fmax ofs0 with
                                | Some _ => Some ((perm_of_rmap σ') # b ofs0)
                                | None => None
                                end).
              * rewrite Maps.PTree.gmap Hb //.
              * rewrite Hofs1 //.
           + intros Hofs1.
             transitivity ((getThreadR cnti).1 # b ofs).
             * eapply computeMap_2 with
                 (df := fun ofs0 => match fmax ofs0 with
                                 | Some _ => Some ((perm_of_rmap σ') # b ofs0)
                                 | None => None end).
               ** rewrite Maps.PTree.gmap Hb //.
               ** rewrite Hofs1 //.
             * assert (Hmax_none : (getMaxPerm m) # b ofs = None).
               { rewrite / Maps.PMap.get Hb //. }
               rewrite (none_of_lt _ Hlt_old Hmax_none).
               rewrite (none_of_lt _ Hlt_new Hmax_none) //.
          - intros Hb.
            transitivity ((getThreadR cnti).1 # b ofs).
            + eapply computeMap_3.
              rewrite Maps.PTree.gmap Hb //.
            + assert (Hmax_none : (getMaxPerm m) # b ofs = None).
              { rewrite /Maps.PMap.get Hb.
                pose proof (Max_isCanonical m) as Hcan.
                unfold isCanonical in Hcan.
                apply (f_equal (fun f => f ofs)) in Hcan.
                simpl in *. done.
              }
              rewrite (none_of_lt _ Hlt_old Hmax_none).
              rewrite (none_of_lt _ Hlt_new Hmax_none) //.
        } 
        assert (Hδ1bound : bounded_maps.sub_map δ1 (getMaxPerm m).2).
        { subst δ1.
          unfold bounded_maps.sub_map.
          intros b fδ Hfδ.
          rewrite PTree.gmap in Hfδ.
          destruct (((getMaxPerm m).2 !! b)%maps) as [fmax |] eqn:Hmax; simpl in Hfδ;
            try discriminate.
          inv Hfδ.
          exists fmax.
          split; auto.
          intros ofs Hδ.
          destruct (fmax ofs); simpl in Hδ; try discriminate; auto.
        }
        Check l0.1.
        exists δ1, δ2.
        repeat split; try done.
        - admit.
        - admit.
        - admit.
        - admit.
      }
      destruct Hdelta_exists as (δ1 & δ2 & Hsub1 & Hsub2 & Hcompute1 & Hcompute2 & Hjoin1 & Hjoin2).
      Search l0.
      (* lock_state
         gmap addr lock_info
lock_info
         Some  => exists sigma, resource σ = p
         None 

       *) *)
      
      Admitted.
  (*
      set (l1' :=
             (l1.1, Ptrofs.intval (Ptrofs.repr l1.2))).
      
      Check  step_acquire.
      (*
      iPoseProof (lock_inv_acquire _
                    (restrPermMap Hlt) ls σ0 sh l1.1 (Ptrofs.repr l1.2) R
                   with "[Hths] [Hls] [Hl]") as "Hauth"; auto. *)
      assert (exists tp' m' ev,
                 syncStep true cnti Hcompat tp' m' ev /\ locks_coherent tp' m' ls /\
                    threads_wellformed tp' /\ invariant tp' /\ mem_compatible tp' m') as Hstep.
      {
        eexists _, _, _.
        split.
        eapply step_acquire with
          (tp' := tp') (pmap := l0)
          ; try done.
        - admit.
        - simpl. admit.
        - simpl.
          rewrite Hofs //.
        - simpl. admit.
        - pose proof (compat_lp _ _ Hcompat _ _ E) as (Hl0_1_lt & Hl0_2_lt).
          pose proof (compat_th _ _ Hcompat cnti) as (Hth_1_lt & Hth_2_lt).
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
              by specialize (perm_order_antisym None (l0.1.1 ofs0) Hl0_1_lt Hperm1). }
          eapply acquire_delta_permMapJoin_new; try apply permMapsDisjoint_comm; auto.
        - simpl.
          pose proof (compat_lp _ _ Hcompat _ _ E) as (Hl0_1_lt & Hl0_2_lt).
          pose proof (compat_th _ _ Hcompat cnti) as (Hth_1_lt & Hth_2_lt).
          pose proof (no_race _ Hinvariant i l1 cnti l0 E) as Hnr.
          unfold permMapsDisjoint2 in Hnr.
          destruct Hnr as (Hdisj1 & Hdisj2).
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
              by specialize (perm_order_antisym None (l0.2.1 ofs0) Hl0_2_lt Hperm1). }
          eapply acquire_delta_permMapJoin_new; try apply permMapsDisjoint_comm; auto.
        - split.
          eapply locks_coherent_acquire_update; eauto.
          rewrite /= Hofs. set_solver.
          rewrite /= Hofs.
          apply Mem_load_unchecked_store_unchecked_same.
          + intros l' Hl' Hneq.
            Search Mem_load_unchecked .
            eapply
              Mem_load_unchecked_store_unchecked_lock_addresses_disjoint;
              eauto. admit. admit. admit.
          + admit.
          +  admit.
      }
      destruct Hstep as (tp' & m' & ev' & Hsyn).
      iApply step_fupd_intro; first set_solver.
      iNext.
      iExists tp', m', ev'.
      iSplit; auto. admit.
      iFrame.
      Print lock_state.
      Print frag_mem_auth.
      Check R _.
      Print threads_safe.
      set (Ψ :=
             fun (_ y : nat) =>
               (∃ (q0 : Qp) (σ : rmap)
                  (cnty : containsThread tp' y)
                  (Hlt' : permMapLt (perm_of_rmap σ) (getMaxPerm m')),
                   ⌜qs !! y = Some q0 ∧
                     mem_equiv.access_map_equiv
                       (perm_of_rmap σ) (getThreadR cnty).1⌝ ∗
                       thread_safe tp' y q0 ∗
                       frag_mem_auth q0 (restrPermMap Hlt') σ)%I).


 *)
        *)

  
  
  Lemma rmap_auth_init_frag 
    (γ : gname) (σ : resource_map.rmapUR share address (leibnizO resource)) :
    ✓ σ → rmap_auth γ (∅ : rmap) ∗ rmap_frag γ 1 (∅ : rmap) ==∗ rmap_auth γ σ ∗ rmap_frag γ 1 σ.
  Proof.
    iIntros (Hvalid) "[Hauth Hfrag]".
    rewrite /rmap_auth /rmap_frag.
    iMod (own_update_2 with "Hauth Hfrag") as "[Hauth Hfrag]"; try by apply frac_auth_update_1.
    iModIntro. iFrame.
  Qed.
  
End conc_heap.

Existing Instance HybridMachine.DryHybridMachine.DryHybridMachineSig.

Theorem dry_safety `{!VSTGpreS unit Σ} `{!inG Σ (gmap_view.gmap_viewR address unitR)}
  `{!inG Σ (gmap_view.gmap_viewR address (laterO (iPropO Σ)))} `{!inG Σ rmap_authUR} sch n :
  exists b c_init, Genv.find_symbol (globalenv prog) (Ctypes.prog_main prog) = Some b /\
                cl_initial_core (globalenv prog) (Vptr b Ptrofs.zero) [] = Some c_init /\
     HybridMachineSig.HybridCoarseMachine.csafe
       (ThreadPool:= threadPool.OrdinalPool.OrdinalThreadPool(Sem:=ClightSem ge))
     (sch, [],
      DryHybridMachine.initial_machine(Sem := Sem) (getCurPerm (proj1_sig init_mem))
        c_init) (proj1_sig init_mem) n.
Proof.
  eapply ouPred.pure_soundness, (step_fupdN_soundness_no_lc' _ (S n) O); [apply _..|].
  simpl; intros; iIntros "_".
  pose proof (empty_coherent Mem.empty) as Hcoh_empty.
  iMod (init_conc_VST_frag () tt) as "H".
  iSpecialize ("H" $! Hinv).
  iDestruct "H" as (HG FS ES HL γ σ) "(Hstate & Hauth & Hfrag & Hfunspec & Hext & locks & _)".
  set (HHfrag := Build_VSTGS _ _
             ({| heapGS_invGS := Hinv;
                heapGS_gen_heapGS := HG;
                heapGS_funspecGS := FS |} : heapGS Σ) ES).
  destruct (spr HHfrag HL σ) as (b & q & (? & ? & Hinit) & Hsafe); [| done..].
  iMod (Hsafe with "[$Hstate $Hfunspec $Hext]") as (?) "(S & Heq & Hsafe)".
  iDestruct "Heq" as "%Heq".
  iUnfold state_interp_with_rmap, frag_mem_auth in "S".
  iDestruct "S" as "((%Hlt & %Hcoh& Hmem) & Hext)".
  (*iPoseProof (state_interp_with_rmap_to_frag with "S") as "S".
  rewrite /frag_state_interp.
  iDestruct "S" as "([(%Hcoh & %Haceq) Hmem] & Hext)". *)
  iDestruct (resource_map.resource_map_auth_valid with "Hmem") as "%Hvalid".
  destruct Hvalid as (_ & Hvalid).
  iMod (rmap_auth_frag_set γ σ σ σ0 Hvalid with "[$Hauth $Hfrag]") as "(Hauth & Hfrag)".
  iAssert (|={⊤}[∅]▷=>^n ⌜HybridMachineSig.HybridCoarseMachine.csafe
               (ThreadPool:= threadPool.OrdinalPool.OrdinalThreadPool(Sem:=ClightSem ge))
               (sch, [],
                 DryHybridMachine.initial_machine(Sem := Sem) (getCurPerm (proj1_sig init_mem))
                   q) (proj1_sig init_mem) n⌝) with "[Hmem Hext Hsafe locks Hauth Hfrag]" as "Hdry".
  2: { iApply step_fupd_intro; first done.
       iNext; iApply (step_fupdN_mono with "Hdry").
       iPureIntro. intros.
       eexists. eexists. split; first done; split; first apply Hinit; done. }
  clear Hinit Hsafe.
  rewrite bi.and_elim_l.
  set (tp := initial_machine _ _).
  assert (invariant tp) as Hinvariant by apply ThreadPoolWF.initial_invariant0.
  assert (HybridMachineSig.mem_compatible tp (`init_mem)) as Hcompat
        by apply ThreadPoolWF.initial_mem_compatible.
  assert (threads_wellformed tp) as Htp_wf by done.
  iAssert (threads_safe tp γ) with "[Hsafe Hfrag]" as "Hsafe".
  { subst tp.
    rewrite /threads_safe /thread_safe /frag_mem_auth /=.
    iSplit; auto.
    iExists 1%Qp, σ0.
    unshelve iExists _; first done.
    iSplit; auto.
    iFrame.
    unshelve iExists _; first done.
    iApply (jsafe_jsafe_frag with "Hsafe").
  }
  assert (locks_coherent tp (`init_mem) ∅) as Hlocks by done.
  clear Hcoh_empty.
  iAssert (lock_state (`init_mem) ∅) with "[locks]" as "locks".
  { iApply (lock_state_empty_change with "locks"). }
  forget (proj1_sig init_mem) as m.
  forget (@nil Events.machine_event) as tr.
  clearbody tp.
  set (ls := ∅) in Hlocks |- *.
  iAssert (frag_mem_auth m σ0) with "[Hmem]" as "Hmem".
  { iExists Hlt; iSplit; first done. done. }
  clearbody ls.
  clear dependent b x q.
  clear σ.
  rename σ0 into σ.
  clear Heq Hlt Hcoh Hvalid.
  iLöb as "IH" forall (sch tr tp m n ls σ Htp_wf Hinvariant Hcompat Hlocks).
  destruct n as [|n].
  { iPureIntro. constructor. }
  destruct sch as [|i sch].
  { iApply step_fupdN_intro; first done; iPureIntro. constructor; done. }
  simpl; destruct (lt_dec i (pos.n (OrdinalPool.num_threads tp))) as [Hlt_thrd |Hge_thrd].
  2 : {
    Local Opaque lock_state.
    iApply step_fupd_intro; try done.
    iNext.
    iAssert (|={⊤}[∅]▷=>^n ∀ U'',
             ⌜HybridMachineSig.HybridCoarseMachine.csafe (U'', tr, tp) m n⌝) with "[-]" as "H".
    { rewrite step_fupdN_plain_forall //.
      iIntros (U'').
      iApply ("IH" $! U'' tr tp m n ls with "[] [] [] [] Hext Hauth Hsafe locks"); try done. }
    iApply (step_fupdN_mono with "H"); iPureIntro.
    intros Hsafe.
    eapply HybridMachineSig.HybridCoarseMachine.AngelSafe
        with (tr := []); simpl; rewrite seq.cats0; last apply Hsafe.
    eapply HybridMachineSig.schedfail; eauto.
    rewrite /containsThread /= /OrdinalPool.containsThread.
    intros ?.
    pose proof (@ssrnat.leP (S i) (pos.n (OrdinalPool.num_threads tp))) as Hle; inv Hle;
        [lia | congruence]. }
  rewrite {2}/threads_safe.
  iPoseProof (big_sepL_lookup_acc_impl i i with "[$Hsafe]") as "Hsafe".
  apply lookup_seq; eauto.
  iDestruct "Hsafe" as "[Hi Hsafe]".
  iDestruct "Hi" as (q σ1 ?) "(%Heq1 & Hsafei & Hfragi)".
  iDestruct "Hsafei" as (?) "Hsafei".
  replace cnti0 with cnti by apply ProofIrrelevance.proof_irrelevance.
  clear cnti0.
  destruct (getThreadC cnti) eqn: Hi.
  - (* Krun *)
    destruct (cl_halted s) eqn: Hhalt; [|destruct (cl_at_external s) eqn: Hat_ext].
    + (* halted *)
      assert (HybridMachineSig.halted_thread cnti Int.zero) as Hhalt'.
      { econstructor; eauto. hnf; rewrite Hhalt //. }
      iApply step_fupd_intro; first done; iNext.
      iAssert (threads_safe tp γ) with "[Hsafei Hfragi Hsafe]" as "Hsafe".
      { iApply "Hsafe".
        + iIntros "!>" (????) "H"; iApply "H".
        + iExists q, σ1, cnti.
          iSplit; auto; iFrame.
          rewrite /thread_safe.
          iExists cnti; rewrite Hi //. }
      iAssert (|={⊤}[∅]▷=>^n ∀ U'',
            ⌜HybridMachineSig.HybridCoarseMachine.csafe (U'', tr, tp) m n⌝) with "[-]" as "H".
      { rewrite step_fupdN_plain_forall //.
        iIntros (x).
        iApply ("IH" $! _ _ _ _ _ _ with "[] [] [] [] Hext Hauth Hsafe locks"); try done.
      }
      iApply (step_fupdN_mono with "H"); iPureIntro.
      intros Hsafe.
      eapply HybridMachineSig.HybridCoarseMachine.AngelSafe with (tr := []); simpl;
        rewrite seq.cats0; last apply Hsafe.
      eapply HybridMachineSig.halted_step; eauto.
    + (* HybridMachineSig.suspend_step *)
      assert (HybridMachineSig.suspend_thread m cnti (updThreadC cnti (Kblocked s))) as Hsuspend.
      { eapply (HybridMachineSig.SuspendThread _ _ _ _ _ _ _ _ Hcompat); done. }
      iApply step_fupd_intro; first done; iNext.
      iAssert (|={⊤}[∅]▷=>^n ∀ U'', ⌜HybridMachineSig.HybridCoarseMachine.csafe (U'', tr, (updThreadC cnti (Kblocked s))) m n⌝) with "[-]" as "H".
      { rewrite step_fupdN_plain_forall //.
        iIntros.
        iApply ("IH" $! x tr (updThreadC cnti (Kblocked s)) m n ls
                 with "[%] [%] [%] [%] Hext Hauth [Hsafe Hfragi Hsafei] locks"); try done.
        - intros j cntj.
          destruct (eq_dec j i) as [-> | Hneq].
          + rewrite (gssThreadCC cnti (Kblocked s) cntj) /= Hat_ext //.
          + pose proof (cntUpdateC' (Kblocked s) cnti cntj) as cntj0.
            rewrite -gsoThreadCC //; by apply Htp_wf.
        - by apply ThreadPoolWF.updThreadC_invariant.
        - by apply StepLemmas.updThreadC_compatible.
        - iApply "Hsafe".
          + iIntros "!>" (k y (-> & ?)%lookup_seq Hneq) "Hy".
            iDestruct "Hy" as (q0 σ0 cnty) "(%Hperm & Hsafe_y & Hfrag_y)".
            iExists q0, σ0, (cntUpdateC _ _ cnty).
            iSplit.
            * iPureIntro; auto; rewrite gThreadCR //.
            * iFrame.
              replace (0 + k) with k by lia.
              assert (Hneq' : i <> k) by lia.
              iDestruct "Hsafe_y" as (cntyk) "Hsafe_y".
              iExists (cntUpdateC (Kblocked s) cnti cntyk).
              rewrite -(gsoThreadCC Hneq') //.
          + iExists q, σ1, (cntUpdateC (Kblocked s) cnti cnti).
            iSplit; auto.
            * rewrite (gThreadCR cnti cnti (Kblocked s) (cntUpdateC (Kblocked s) cnti cnti)) //.
            * iFrame; iExists (cntUpdateC (Kblocked s) cnti cnti); rewrite gssThreadCC //.
      }
      iApply (step_fupdN_mono with "H"); iPureIntro; intros Hsafe.
      eapply HybridMachineSig.HybridCoarseMachine.AngelSafe
          with (tr := []); simpl; rewrite seq.cats0; last apply Hsafe.
      eapply HybridMachineSig.suspend_step; eauto.
    + (* corestep: HybridMachineSig.thread_step *)
      rewrite jsafe_frag_unfold /jsafe_frag_pre.
      (* iAssert (⌜coherent (restrPermMap Hlt) σ1⌝) with "[Hfragi]" as "%Hcoh".
      { by iDestruct "Hfragi" as "((? & ?) & ?)". } *)
      iMod "Hsafei" as "Hsafei".
      iDestruct ("Hsafei" $! m σ1 (getThreadR cnti) with "[$Hmem $Hauth $Hfragi $Hext]") as (Hlt) "[Hhalt | [Hstep | Hext]]".
      { iSplit; auto. }
      (* contradiction *)
      { iDestruct "Hhalt" as (i0 Hhalt') "_". done. }
      2 : { iDestruct "Hext" as (??? Hext) "?". simpl in Hext; congruence. }
      unfold frag_mem_auth .
      (* HStep *)
      iMod "Hstep" as (c' m' σ') "(%Hstep & S & Hsafei)".
      assert (Hmem_restr : restrPermMap (Hcompat i cnti) = restrPermMap Hlt).
      { erewrite restrPermMap_ext; eauto. }
      assert (Hstep' : corestep (cl_core_sem ge) s (restrPermMap (Hcompat i cnti)) c' m').
      { rewrite Hmem_restr //. }
      iApply step_fupd_intro; first done.
      iNext.
      apply (ev_step_ax2 (Clight_evsem.CLC_evsem ge)) in Hstep' as (ev & Hstep').
      assert (Hmemstep : mem_step (restrPermMap Hlt) m').
      { eapply (CLC_corestep_mem _ _ (restrPermMap Hlt)); eauto. }
      assert (mem_compatible (updThread cnti (Krun c') (getCurPerm m')) m') as Hcompat'.
      { by eapply (CoreLanguageDry.corestep_compatible (Sem := Sem)). }
      assert (Hlock_loads : forall l0, l0 ∈ ls ->
                                  Mem_load_unchecked Mptr m l0.1 l0.2 = Mem_load_unchecked Mptr m' l0.1 l0.2).
      { intros l0 Hl0.
        pose proof (Hlocks l0 Hl0) as Hlock0.
        destruct Hlock0 as (_ & _ & Hne).
        specialize (Hne i cnti ((Hcompat i cnti))).
        rewrite Hmem_restr in Hne.
        rewrite <- (Mem_unchecked_restrPermMap m (perm_of_rmap σ1) Hlt l0).
        unfold Mem_load_unchecked.
        f_equal.
        eapply mem_step_preserves_lock_bytes; eauto.
      }
      iAssert (lock_state m' ls) with "[locks]" as "locks".
      { iApply (lock_state_mem_change m m' ls Hlock_loads with "locks"). }
      iDestruct "S" as (σnew) "(%Heq_new & Hmemi & Hauth & Hfragi & Hext)".
      iSpecialize ("IH" $! _ _ (updThread cnti (Krun c') (getCurPerm m')) m' n ls σnew
                    with "[%] [%] [%] [%] Hext Hauth [Hsafe Hsafei Hfragi] locks Hmemi"); try done.
      * (* threads_wellformed *)
        intros j cntj.
        destruct (eq_dec j i); first by subst; rewrite gssThreadCode.
        pose proof (cntUpdate' _ _ cnti cntj).
        rewrite gsoThreadCode //; apply Htp_wf.
      * (* invariant *)
        eapply (CoreLanguageDry.corestep_invariant(Sem := Sem)); try done.
      * (* locks_coherent *)
        rewrite /locks_coherent in Hlocks |- *.
        intros l0 Hl0.
        destruct (Hlocks l0) as (HlockRes & Hload & HnonEmpty); auto.
        rewrite !gsoThreadLPool.
        split; first exact HlockRes.
        split.
        ** (* value stored in the lock does not change *)
          rewrite <- (Hlock_loads l0 Hl0). done.
        ** (* every thread still sees the lock as Nonempty *)
          intros i0 cnti0 Hp0.
          destruct (Nat.eq_dec i i0) as [-> | Hneq].
          ++ have Hne := HnonEmpty i0 cnti (Hcompat i0 cnti).
             rewrite Hmem_restr in Hne.
             rewrite /nonEmptyRangeCur in Hne |- *.
             intros i1 Hi1.
             rewrite restrPermMap_Cur_eq.
             rewrite (gssThreadRes cnti (Krun c') (getCurPerm m') cnti0) /=.
             rewrite /getCurPerm PMap.gmap /=.
             eapply mem_step_preserves_nonempty_range; eauto.
          ++ (* another thread *)
             assert (cnti_old : containsThread tp i0); try by eapply cntUpdate'; eauto.
             have Hne_old := HnonEmpty i0 cnti_old (Hcompat i0 cnti_old).
             rewrite /nonEmptyRangeCur in Hne_old |- *.
             intros i1 Hi1.
             specialize (Hne_old i1 Hi1).
             rewrite restrPermMap_Cur_eq in Hne_old.
             rewrite restrPermMap_Cur_eq.
             erewrite @gsoThreadRes with (cntj := cnti_old); eauto.
      * (* threads_safe *)
        iApply "Hsafe".
        ** iIntros "!>" (k y (-> & ?)%lookup_seq Hneq) "Hy".
           iDestruct "Hy" as (q0 σ0 cnty) "(%Hqy & Hsafe_y & Hfrag_y)".
           replace (0 + k) with k in * by lia.
           assert (Hneq' : i <> k) by lia.
           set (cnty' := @cntUpdate _ _ _ i (0 + k) tp (Krun c') (getCurPerm m') cnti cnty).
           iExists q0, σ0, cnty'.
           iSplit.
           { iPureIntro. subst cnty'. erewrite gsoThreadRes; eauto. }
           iSplitL "Hsafe_y".
           {
             rewrite /thread_safe.
             iDestruct "Hsafe_y" as (cnty0) "Hsafe_y".
             set (cnty0' := @cntUpdate _ _ _ i k tp (Krun c') (getCurPerm m') cnti cnty0).
             iExists cnty0'.
             subst cnty0'.
             rewrite gsoThreadCode; auto. }
           done.
        ** (* selected thread *)
           set (cnti' := @cntUpdate _ _ _ i i tp (Krun c') (getCurPerm m') cnti cnti).
           iExists q, σ', cnti'.
           iSplit.
           { iPureIntro. subst cnti'. rewrite gssThreadRes //. }
           iSplitL "Hsafei".
           { rewrite /thread_safe.
             iExists cnti'.
             subst cnti'.
             rewrite gssThreadCode /=. done. }
           iFrame.
      * iApply (step_fupdN_mono with "IH").
        iPureIntro; intros Hsafe.
        eapply HybridMachineSig.HybridCoarseMachine.CoreSafe; last exact Hsafe.
        rewrite /HybridMachineSig.MachStep /=.
        change (i :: sch) with (HybridMachineSig.yield (i :: sch)) at 2.
        change m' with (HybridMachineSig.diluteMem m') at 3.
        eapply HybridMachineSig.thread_step; first done.
        instantiate (1 := ev).
        eapply step_dry with (c := s) (m1 := restrPermMap (Hcompat i cnti)) (c' := c') (ev := ev);
          eauto.
  - (* Kblocked: HybridMachineSig.sync_step *)
    pose proof (Htp_wf _ cnti) as Hwfi; rewrite Hi in Hwfi.
    rewrite jsafe_frag_unfold /jsafe_frag_pre.
    iMod "Hsafei" as "Hsafei".
    iDestruct ("Hsafei" $! m σ1 (getThreadR cnti) with "[Hmem Hauth Hfragi Hext]")
      as (Hlt) "[Hhalt | [Hstep | Hext]]".
    { rewrite /thread_state_interp. iExists σ; iFrame. iSplit; auto. }
    (* impossible: blocked external call cannot be halted *)
    { iDestruct "Hhalt" as (? Hhalt') "?"; destruct s; done. }
    (* impossible: corestep cannot start from an external state *)
    { iMod "Hstep" as (??? Hstep) "?"; apply cl_corestep_not_at_external in Hstep; done. }
    (* external case *)
    iDestruct "Hext" as (e args x) "(%Hat_ext & S & Hpre & Hpost)".
    simpl in Hat_ext.
    iAssert (|={⊤}[∅]▷=> ∃ (tp' : t (ThreadPool := OrdinalPool.OrdinalThreadPool)) m' ev σnew,
               ⌜threads_wellformed tp' ∧ invariant tp' ∧ mem_compatible tp' m' ∧
                locks_coherent tp' m' ls ∧ syncStep true cnti Hcompat tp' m' ev⌝ ∧
            ext_auth () ∗ rmap_auth γ σnew ∗ frag_mem_auth m' σnew ∗ threads_safe tp' γ ∗
              lock_state m' ls) with "[Hpost Hsafe locks Hpre S]" as "Hsafe".
    2 : {
      iMod "Hsafe".
      iIntros "!> !>".
      iMod "Hsafe" as (tp' m' ev σnew) "(%Hsync & Hext & Hauth & Hmem & Hth & locks)".
      destruct Hsync as (Htp_wf' & Hinvariant' & Hcompat' & Hlocks' & Hsync).
      iAssert (|={⊤}[∅]▷=>^n ∀ U'', ⌜HybridMachineSig.HybridCoarseMachine.csafe (U'', tr ++ [Events.external i ev], tp') m' n⌝) with "[-]" as "H".
      { rewrite step_fupdN_plain_forall //.
        iIntros.
        iApply ("IH" $! x0 (tr ++ [Events.external i ev]) tp' m' n ls
                 with "[] [] [] [] Hext Hauth Hth locks Hmem"); try done.
      }
      iApply (step_fupdN_mono with "H").
      iPureIntro.
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
      

    

      iDestruct "Hhalt" as (i0 Hhalt') "_". destruct s. done. }

    
    iAssert (⌜coherent (restrPermMap Hlt) σ1⌝) with "[Hfragi]" as "%Hcoh".
    { by iDestruct "Hfragi" as "((? & ?) & ?)". }
    iMod "Hsafei" as "Hsafei".
    iDestruct ("Hsafei" $! (restrPermMap Hlt) σ1
                  with "[$Hfragi $Hext]") as (Hlt0) "[Hhalt | [Hstep | Hext]]".
    { iDestruct "Hhalt" as (? Hhalt') "?"; destruct s; done. }
    { iMod "Hstep" as (??? Hstep) "?"; apply cl_corestep_not_at_external in Hstep; done. }
    (* cl_at_external s = Some (e, args) *)
    iDestruct "Hext" as (???? Hat_ext) "(S & Hpre & Hpost)".
    simpl in Hat_ext.
    iAssert (|={⊤}[∅]▷=> ∃ (tp' : t(ThreadPool := OrdinalPool.OrdinalThreadPool)) m' ev,
                ⌜threads_wellformed tp' ∧ invariant tp' ∧ mem_compatible tp' m' ∧
                 locks_coherent tp' m' ls ∧ syncStep true cnti Hcompat tp' m' ev⌝ ∧
                  (*(∃ (σ : rmap) (Hlt : permMapLt (perm_of_rmap σ) (getMaxPerm m')),
                      frag_state_interp q (restrPermMap Hlt) σ0 ()) *)
                  ext_auth () ∗
                  threads_safe tp' m' ∗ lock_state m' ls )
        with "[Hpost Hsafe locks Hpre S]" as "Hsafe".
      2 : {
        iMod "Hsafe".
        iIntros "!> !>".
        iMod "Hsafe" as (??? (? & ? & ? & ? & ?)) "(Hext & Hth & locks)".
        iAssert (|={⊤}[∅]▷=>^n ∀ U'', ⌜HybridMachineSig.HybridCoarseMachine.csafe (U'', tr ++ [Events.external i ev], tp') m' n⌝) with "[-]" as "H".
        { rewrite step_fupdN_plain_forall //.
          iIntros.
          iApply ("IH" $! x0 (tr ++ [Events.external i ev]) tp' m' n ls
              with "[%] [%] [%] [%] Hext Hth locks"); try done.
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
     
      (* iApply (acquire_safe with "Hsafe Hpost locks"). *) admit.
   + (* release *) admit.
   + (* makelock *) admit.
   + (* freelock *) admit.
   + (* spawn *) admit.

  - (* Kresume: HybridMachineSig.resume_step *)
    pose proof (Htp_wf _ cnti) as Hwfi; rewrite Hi in Hwfi; destruct Hwfi as (? & ->).
    destruct s; try done.
    destruct f; try done.
    assert (HybridMachineSig.resume_thread m cnti (updThreadC cnti (Krun (Returnstate Vundef c)))) as Hresume.
    { unfold cl_at_external in *; destruct (ef_inline e) eqn: Hinline; try done.
        eapply (HybridMachineSig.ResumeThread _ _ _ _ _ _ _ _ _ Hcompat); try done; simpl; by rewrite ?Hinline. }
    iApply step_fupd_intro; first done; iNext.
    iSpecialize ("IH" $! _ _ (updThreadC cnti (Krun (Returnstate Vundef c)))
                  with "[%] [%] [%] [%] Hext [Hsafe Hsafei Hfragi] locks").
    + intros j cntj.
      destruct (eq_dec j i).
      * subst; rewrite gssThreadCC //.
      * pose proof (cntUpdateC' _ cnti cntj) as cntj0.
        rewrite -gsoThreadCC //; apply Htp_wf.
    + by apply ThreadPoolWF.updThreadC_invariant.
    + by apply StepLemmas.updThreadC_compatible.
    + rewrite /locks_coherent in Hlocks |- *.
      intros.
      destruct (Hlocks l1) as (HlockRes & Hload & HnonEmpty); auto.
    + iApply "Hsafe".
      * iIntros "!>" (?? (-> & ?)%lookup_seq ?)
            "(%q0 & %σ0 & (%cnty & %Hltσ0 & %Hqy & Hsafe_y & Hfrag_y))".
        assert (Hik : i <> 0 + k) by lia.
        pose (cnty' := OrdinalPool.cntUpdateC (Krun (Returnstate Vundef c)) cnti cnty).
        pose proof (@OrdinalPool.gThreadCR _ _ i (0 + k) tp cnti cnty
                        (Krun (Returnstate Vundef c)) cnty') as HR.
        iExists q0, σ0, cnty', Hltσ0.
        iSplit; auto.
        ** iPureIntro.
           unfold mem_equiv.access_map_equiv in Hqy |- *.
           intro b.
           specialize (Hqy b).
           pose proof (f_equal (fun pm => pm # b) HR) as HRb.
           etransitivity; eauto.
        ** iFrame.
           rewrite /thread_safe.
           iDestruct "Hsafe_y" as (cnty0) "Hsafe_y".
           assert (cnty0' : containsThread (updThreadC cnti (Krun (Returnstate Vundef c))) (0 + k)); try done.
           iExists cnty0'.
           have -> : (getThreadC cnty0' = getThreadC cnty0) by symmetry; apply gsoThreadCC.
           iFrame.
      * assert (cnti' : containsThread (updThreadC cnti (Krun (Returnstate Vundef c))) i); try done.
        iExists q, σ1, cnti', Hlt.
        iSplit; try iPureIntro.
        have -> : (getThreadR cnti') = (getThreadR cnti); try done.
        { rewrite /getThreadR /=.
          have <- : fintype.Ordinal cnti = fintype.Ordinal cnti'; try done.
          { f_equal; apply proof_irrelevance. } 
        }
        iFrame.
        iExists cnti'.
        rewrite gssThreadCC.
        by iApply ("Hsafei" $! (Returnstate Vundef c)).
    + iApply (step_fupdN_mono with "IH"); iPureIntro; intros Hsafe.
      eapply HybridMachineSig.HybridCoarseMachine.CoreSafe with (tr := []); simpl; rewrite seq.cats0; last apply Hsafe.
      change (i :: sch) with (HybridMachineSig.yield (i :: sch)) at 2.
      eapply HybridMachineSig.resume_step; eauto.
  - (* Kinit: HybridMachineSig.start_step *)
    iDestruct "Hsafei" as (? Hinit) "Hsafei".
    set (m' := restrPermMap (Hcompat i cnti)).
    set (tp' := updThread cnti (Krun q_new) (HybridMachineSig.add_block Hcompat cnti m')).
    assert (HybridMachineSig.start_thread m cnti tp' m'); try econstructor; try done.
    iApply step_fupd_intro; first done; iNext.
    iSpecialize ("IH" $! _ _ tp' m' with "[%] [%] [%] [%] Hext [Hsafe Hsafei Hfragi] locks").
    + (* threads_wellformed tp' *)
      intros j cntj.
      destruct (eq_dec j i).
      * subst; rewrite gssThreadCode //.
      * pose proof (cntUpdate' _ _ cnti cntj); rewrite gsoThreadCode //; apply Htp_wf.
    + (* invariant tp' *)
      by eapply (CoreLanguageDry.initial_core_invariant(Sem := Sem)).
    + (* mem_compatible tp' m' *)
      eapply InternalSteps.start_compatible; try done.
    + rewrite /locks_coherent in Hlocks |- *.
      intros.
      destruct (Hlocks l0) as (HlockRes & Hload & HnonEmpty); auto.
      repeat split; auto.
      unfold nonEmptyRangeCur in *.
      intros.
      subst tp'.
      rewrite restrPermMap_Cur_eq.
      destruct (Nat.eq_dec i i0) as [-> | Hneq].
      * rewrite (gssThreadRes cnti (Krun q_new)
                     (HybridMachineSig.add_block Hcompat cnti m') cnti0).
        rewrite /HybridMachineSig.add_block /= /m' /getCurPerm PMap.gmap /=.
        apply (HnonEmpty i0 cnti (Hcompat i0 cnti) i1); auto.
      * assert (cnti_old : containsThread tp i0); try done.
        have -> : (getThreadR cnti0) = (getThreadR cnti_old).
        { f_equal; rewrite gsoThreadRes //. }
        have Hne_old := HnonEmpty i0 cnti_old (Hcompat i0 cnti_old) i1 H1.
        rewrite restrPermMap_Cur_eq in Hne_old.
        exact Hne_old.
    + iApply "Hsafe".
      * iIntros "!>" (?? (-> & ?)%lookup_seq ?)
            "(%q0 & %σ0 & (%cnty & %Hltσ0 & %Hqy & Hsafe_y & Hfrag_y))".
        have Hik : i <> 0 + k by lia.
        subst tp'.
        have Hltσ0' : permMapLt (perm_of_rmap σ0) (getMaxPerm m') by rewrite /m' restr_Max_eq //.
        assert (cnty' : containsThread (updThread cnti (Krun q_new)
                        (HybridMachineSig.add_block Hcompat cnti m')) (0 + k)).
        { by eapply cntUpdate. }
        iExists q0, σ0, cnty', Hltσ0'.
        iSplit; try iPureIntro; try split; eauto; try rewrite gsoThreadRes //.
        rewrite (restrPermMap_idem Hltσ0') (restr_proof_irr (permMapLt_restr Hltσ0') Hltσ0).
        iFrame.
        rewrite /thread_safe.
        iDestruct "Hsafe_y" as (cnty0) "Hsafe_y".
        assert (cnty0' : containsThread (updThread cnti (Krun q_new)
                       (HybridMachineSig.add_block Hcompat cnti m')) (0 + k)); try done.
        iExists cnty0'.
        have -> : (getThreadC cnty0' = getThreadC cnty0); try iFrame.
        { by apply gsoThreadCode. }
      * have Hlt' : permMapLt (perm_of_rmap σ1) (getMaxPerm m').
        { rewrite /m' restr_Max_eq //. }
        assert (cnti' : containsThread tp' i); try done.
        iExists q, σ1, cnti', Hlt'.
        iSplit; subst tp'.
        ** iPureIntro.
           rewrite gssThreadRes /HybridMachineSig.add_block /=.
           subst m'.
           pose proof (mem_equiv.getCur_restr (getThreadR cnti) m (Hcompat i cnti)) as Hcur.
           unfold mem_equiv.access_map_equiv in *.
           intros b.
           rewrite Heq1 Hcur //.
        ** rewrite /thread_safe.
           rewrite (restrPermMap_idem Hlt') (restr_proof_irr (permMapLt_restr Hlt') Hlt).
           iFrame.
           iExists cnti'.
           rewrite gssThreadCode //.
    + iApply (step_fupdN_mono with "IH"); iPureIntro; intros Hsafe.
      eapply HybridMachineSig.HybridCoarseMachine.CoreSafe with (tr := []); simpl;
        rewrite seq.cats0; last apply Hsafe.
      change (i :: sch) with (HybridMachineSig.yield (i :: sch)) at 2.
      change m' with (HybridMachineSig.diluteMem m').
      eapply HybridMachineSig.start_step; eauto.
Admitted.

End Safety.
