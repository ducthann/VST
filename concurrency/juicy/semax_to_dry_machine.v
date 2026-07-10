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
Require Import VST.veric.Clight_initial_world.
Require Import VST.concurrency.juicy.initial_world_with_rmap.
Require Import VST.veric.initialize.
Require Import iris_ora.algebra.gmap.


Import ThreadPool.
Set Bullet Behavior "Strict Subproofs".

Definition funspec_auth `{!funspecGS Σ} m :=
  own (inG0 := funspec_inG) funspec_name (gmap_view.gmap_view_auth (dfrac.DfracOwn 1) m).

Section semax_prog_with_rmap.
  Context `{!VSTGS OK_ty Σ} (OK_spec : Jext_spec Σ).

  Definition state_interp_with_rmap (m : mem) (z : OK_ty) (σ : rmap) : iProp Σ :=
    frag_mem_auth 1 m σ ∗ ext_auth z.

  Lemma semax_prog_rule_with_rmap {CS : compspecs} :
    forall V G prog m h z,
      postcondition_allows_exit OK_spec Ctypesdefs.tint ->
      semax_prog OK_spec (C := CS) prog z V G  ->
      Genv.init_mem prog = Some m ->
      { b : Values.block & { q : CC_core &
                            (Genv.find_symbol
                               (globalenv prog) (prog_main prog) = Some b) *
      (exists m',
         semantics.initial_core (cl_core_sem (globalenv prog)) h m q m' (Vptr b Ptrofs.zero) nil) *

      (state_interp Mem.empty z ∗ funspec_auth ∅ ∗ has_ext z
       ⊢ |==> ∃ σ : rmap,
           state_interp_with_rmap m z σ ∗
             ⌜mem_equiv.access_map_equiv (perm_of_rmap σ) (getCurPerm m)⌝ ∗
           (jsafeN OK_spec (globalenv prog) ⊤ z q ∧
            matchfunspecs (globalenv prog) G))
    } }%type.
  Proof.
    intros until z.
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
Proof. intros Hpq Hqr b ofs; eapply mem_lemmas.po_trans; eauto.
Qed.

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

Lemma free_contents : forall m b lo hi m',
    Mem.free m b lo hi = Some m' -> Mem.mem_contents m' = Mem.mem_contents m.
Proof.
  intros m b lo hi m' H.
  Transparent Mem.free.
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
    permMapLt q (getCurPerm m) ->
    permMapsDisjoint (getCurPerm m) q ->
    Mem.free m b lo hi = Some m' ->
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

  (*
  Definition other_lt_and_disjoint (p : access_map) (σj : rmap) (m m' : mem) : Prop :=
  permMapLt (perm_of_rmap σj) (getMaxPerm m') /\
    permMapLt (perm_of_rmap σj) (getMaxPerm m) /\
    permMapsDisjoint p (perm_of_rmap σj).
*)
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
         Transparent Mem.alloc.
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
         Transparent Mem.storebytes.
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

  (* Program Definition spr (HH : VSTGS unit Σ) (HL : lockGS Σ) :=
    semax_prog_rule (concurrent_ext_spec CS ext_link) V G prog
      (proj1_sig init_mem) 0 tt _ (all_safe HH HL) (proj2_sig init_mem).
  Next Obligation.
  Proof. intros; iIntros (??); done. Qed. *)

  Program Definition spr
    (HH : VSTGS unit Σ)
    (HL : lockGS Σ) :=
    semax_prog_rule_with_rmap
      (concurrent_ext_spec CS ext_link)
      V G prog
      (proj1_sig init_mem) 0 tt
      _ (all_safe HH HL) (proj2_sig init_mem).
  Next Obligation.
  Proof. intros; iIntros (??); done. Qed.
 

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

Section conc_heap.

  Context `{HH: !VSTGS unit Σ} `{!lockGS Σ}.

  (* Definition frag_mem_auth q (m : mem) (σ : rmap) : iProp Σ :=
    ⌜coherent m σ⌝ ∧ resource_map.resource_map_auth
                       (H1 := gen_heapGpreS_heap (gen_heapGpreS := gen_heap_inG))
                       (gen_heap_name heapGS_gen_heapGS) q σ. *)

  Definition frag_state_interp q (m : mem) (σ : rmap) z : iProp Σ :=
    frag_mem_auth q m σ ∗ ext_auth z.
  
  Lemma locks_init `{InGlock : !inG Σ (gmap_view.gmap_viewR address (later (iPropO Σ)))} (m : mem) :
    ⊢ |==> ∃ HL : lockGS Σ, ∀ heapGS0 : heapGS Σ,
        @lock_state Σ heapGS0 HL m (∅ : gset address).
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
        ∃ (HG : gen_heapGS share address resource Σ) (FS : funspecGS Σ)
          (ES : externalGS Z Σ) (HL : lockGS Σ),
          @state_interp Σ Z HG ES Mem.empty z ∗
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
    iModIntro.
    iIntros (Hinv).
    pose (HG := {| gen_heap_inG := VSTGpreS_heap; gen_heap_name := γh; gen_meta_name := γmeta |}).
    pose (FS := FunspecG _ _ γf).
    pose (HGS := ({| heapGS_invGS := Hinv; heapGS_gen_heapGS := HG; heapGS_funspecGS := FS |} : heapGS Σ)).
    iSpecialize ("Hlocks" $! HGS).
    iExists HG, FS, ES, HL.
    rewrite /gen_heap_meta_auth /=.
    iFrame.
    iPureIntro.
    split; auto.
    apply empty_coherent.
    rewrite /access_at //.
  Qed.

  Lemma frag_mem_auth_corestep_other (q : Qp) (m m' : mem) (p : access_map) (σ : rmap)
    (Hp : permMapLt p (getMaxPerm m)) (Hσ : permMapLt (perm_of_rmap σ) (getMaxPerm m))
    (Hσ' : permMapLt (perm_of_rmap σ) (getMaxPerm m')):
    mem_step (restrPermMap Hp) m' -> permMapsDisjoint p (perm_of_rmap σ) ->
    frag_mem_auth q (restrPermMap Hσ) σ -∗ frag_mem_auth q (restrPermMap Hσ') σ.
  Proof.
    intros Hstep Hdisj.
    rewrite /frag_mem_auth.
    iIntros "((%Hcoh & %Hperm) & Hfrag)".
    iSplit; iFrame.
    iPureIntro; split.
    - eapply coherent_mem_step_other_aux; eauto.
    - intro b; extensionality ofs; rewrite getCurPerm_correct restrPermMap_Cur //.
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
  
  Program Definition jsafe_frag_pre q (jsafe : coPset -d> unit -d> CC_core -d> iPropO Σ) :
    coPset -d> unit -d> CC_core -d> iPropO Σ := λ E z c,
     |={E}=>
    ∀ (m : mem) (σ : rmap),
    frag_state_interp q m σ z -∗
      (* Hlt is derived from the current fragment state. *)
       ∃ (Hlt : permMapLt (perm_of_rmap σ) (getMaxPerm m)),
      (∃ i, ⌜halted (cl_core_sem ge) c i⌝ ∧ (*frag_state_interp_1 q m σ z ∗ *)
        Jext_spec_exit (concurrent_ext_spec CS ext_link) (Some (Vint i))) ∨
      
      (|={E}=> ∃ c' m' σ',
          ⌜corestep (cl_core_sem ge) c (restrPermMap Hlt) c' m'⌝ ∧
          frag_state_interp q m' σ' z ∗ ▷ jsafe E z c') ∨
      
      (∃ e args x σ1, ⌜at_external (cl_core_sem ge) c (restrPermMap Hlt) = Some (e, args)⌝ ∧
        frag_state_interp q m σ1 z ∗
          Jext_spec_pre (concurrent_ext_spec CS ext_link) e x
          (genv_symb_injective ge) (sig_args (ef_sig e)) args ∗
        ▷ (∀ ret m' σ' z' (*(Hlt' : permMapLt (perm_of_rmap σ') (getMaxPerm m')) *),
            ⌜Val.has_type_list args (sig_args (ef_sig e)) ∧ Builtins0.val_opt_has_rettype ret (sig_res (ef_sig e))⌝ →
            |={E}=> frag_state_interp q m' σ' z' -∗
            Jext_spec_post (concurrent_ext_spec CS ext_link) e x (genv_symb_injective ge)
              (sig_res (ef_sig e)) ret -∗
            ∃ c' σ2, ⌜after_external (cl_core_sem ge) ret c m' = Some c'⌝ ∧
              frag_state_interp q m' σ2 z' ∗ jsafe E z' c')).

  Local Instance jsafe_frag_pre_contractive q: Contractive (jsafe_frag_pre q).
  Proof.
    rewrite /jsafe_frag_pre => n jsafe jsafe' Hsafe E z c.
    do 19 f_equiv.
    - try f_contractive; repeat f_equiv. apply Hsafe.
    - do 2 f_equiv. f_contractive; repeat f_equiv. apply Hsafe.
  Qed.

  Local Definition jsafe_frag_def q: coPset -> unit -> CC_core -> iProp Σ :=
    fixpoint (jsafe_frag_pre q).
  Local Definition jsafe_frag_aux : seal (jsafe_frag_def). Proof. by eexists. Qed.
  Definition jsafe_frag := jsafe_frag_aux.(unseal).
  Local Lemma jsafe_frag_unseal : jsafe_frag = jsafe_frag_def.
  Proof. rewrite -jsafe_frag_aux.(seal_eq) //. Qed.

  Lemma jsafe_frag_unfold q E z c :
    jsafe_frag q E z c ⊣⊢ jsafe_frag_pre q (jsafe_frag q) E z c.
  Proof.
    rewrite jsafe_frag_unseal.
    apply (fixpoint_unfold (jsafe_frag_pre q)).
  Qed.

  Lemma frag_state_interp_1_to_state_interp m σ z:
    frag_state_interp 1 m σ z  -∗ state_interp m z.
  Proof.
    rewrite /frag_state_interp /state_interp /frag_mem_auth.
    iIntros "(((% & %) & ?) & ?)"; iFrame. done.
  Qed.

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

  Lemma frag_state_interp_1_to_state_interp_restr m σ z
    (Hlt : permMapLt (perm_of_rmap σ) (getMaxPerm m)) :
    frag_state_interp 1 m σ z -∗ state_interp (restrPermMap Hlt) z.
  Proof.
    rewrite /frag_state_interp /frag_mem_auth /state_interp /mem_auth.
    iIntros "(((%Hcoh & %Heq) & Hauth) & Hext)".
    iFrame; iPureIntro; split; auto; apply coherent_restrPermMap; auto.
  Qed.
(*
  Lemma coherent_to_exact_rmap
    (m : mem) (s : rmap)
    (block_bounds : Values.block -> Z * nat)
    {F : Type}
    (ge : Genv.t (fundef F) type)
    (G : funspecs)
    (Hcover : block_bounds_cover m block_bounds) :
    coherent m s ->
    exists s',
      coherent m s' /\
        mem_equiv.access_map_equiv (getCurPerm m) (perm_of_rmap s') /\
        resource_map.resource_map_auth (H1 := gen_heapGpreS_heap
                                                (gen_heapGpreS := gen_heap_inG))
          (gen_heap_name heapGS_gen_heapGS) 1 s ~~>
          resource_map.resource_map_auth (gen_heap_name heapGS_gen_heapGS)  1 s'.
  Proof.
    intros Hcoh.

    set (s' :=
           rmap_of_mem_with_rmap
             (Σ := Σ) m block_bounds ge G).

    exists s'.
    split.
    - rewrite /coherent.
      intro loc.
      apply rmap_of_mem_with_rmap_coherent.
      apply rmap_of_mem_with_rmap_valid.

      split.
    - symmetry.
      apply access_map_pointwise_eq_equiv.
      unfold s'.
      apply perm_of_rmap_of_mem_with_rmap_exact.
      exact Hcover.

    - apply resource_map_auth_full_update.
      apply rmap_of_mem_with_rmap_valid.
  Qed.
  *)


  Lemma resource_map_auth_increase γ s s' :
    ✓ s' ->
    s ≼ s' ->
    resource_map.resource_map_auth
      (H1 := gen_heapGpreS_heap (gen_heapGpreS := gen_heap_inG))
      γ 1 s
    ==∗
        resource_map.resource_map_auth
        (H1 := gen_heapGpreS_heap (gen_heapGpreS := gen_heap_inG))
        γ 1 s'.
  Proof.
    intros Hvalid Hinc.
    destruct Hinc as (δ & Hδ).
    iIntros "Hauth".
    rewrite resource_map.resource_map_auth_unseal.
    unfold resource_map.resource_map_auth_def.
    iMod (own_update
            _
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

  (*
  Lemma res_of_loc_with_rmap_perm
    (m : mem) {F : Type}
    (ge : Genv.t (Ctypes.fundef F) type)
    (G : funspecs)
    (loc : address) :
    perm_of_res (resR_to_resource
         (Some (res_of_loc_with_rmap (Σ := Safety.Σ) m ge G loc))) =
      access_at m loc Cur.
  Proof.
    unfold res_of_loc_with_rmap.
    destruct (access_at m loc Cur) as [p|] eqn:Hcur; simpl.
    - destruct p; simpl; try rewrite elem_of_to_agree.
      + unfold Tsh.
        apply perm_of_freeable.
      + apply perm_of_Ews.
      + apply perm_of_Ers.
      + destruct (funspec_of_loc ge G loc) as [fs|] eqn:Hfs; simpl; auto.
        * rewrite elem_of_to_agree //.
        * rewrite if_false; auto.
          apply Lsh_bot_neq.
    - rewrite if_true; auto.
  Qed.

  Lemma join_sub_Rsh_glb : forall x, sepalg.join_sub Share.Rsh x -> Share.glb Share.Rsh x = Share.Rsh.
  Proof.
    intros x (y & Hjoin).
    unfold sepalg.join in Hjoin.
    destruct Hjoin as (Hglb & Hlub).
    subst.
    rewrite Share.distrib1 Share.glb_idem Hglb Share.lub_bot //.
  Qed.

  Lemma nonreadable_extend_to_exact_readable sh:
    sh <> Share.bot -> ~ readable_share sh ->
    exists sh', sepalg.join_sub sh sh' /\ readable_share sh' /\ ~ writable_share sh'.
  Proof.
    intros _ Hnotread.
    set (h := (Share.split Share.Rsh).1).
    exists (Share.lub sh h).
    assert (Hsh_no_Rsh : Share.glb Share.Rsh sh = Share.bot).
    {
      destruct (dec_share_identity (Share.glb Share.Rsh sh)) as [Hid | Hnonid].
      - apply identity_share_bot; auto.
      - exfalso.
        apply Hnotread.
        by unfold readable_share, nonempty_share.
    }
    assert (Hh_in_Rsh : Share.glb Share.Rsh h = h).
    { subst h.
      apply glb_split_x. }
    assert (Hh_nonid : sepalg.nonidentity h).
    { subst h.
      destruct (Share.split Share.Rsh) as [h1 h2] eqn:Hsplit; simpl.
      unfold sepalg.nonidentity.
      intros Hid.
      apply (nonemp_split_neq2 Share.Rsh h1 h2 Rsh_nonidentity Hsplit).
      Check Hid h2 Share.Rsh.
      apply (Hid h2 Share.Rsh).
      eapply split_join; auto. }
    assert (Hh_neq_Rsh : h <> Share.Rsh).
    { subst h.
      destruct (Share.split Share.Rsh) as [h1 h2] eqn:Hsplit; simpl.
      apply (nonemp_split_neq1 Share.Rsh h1 h2 Rsh_nonidentity Hsplit). }
    repeat split.
    - (* sepalg.join_sub sh (Share.lub sh h) *)
      rewrite <- leq_join_sub.
      apply Share.lub_upper1.
    - Search readable_share Share.lub.
      apply readable_share_lub.
      unfold readable_share.
      rewrite Hh_in_Rsh //.
    - unfold writable_share.
      intros Hw.
      Search sepalg.join_sub.
      assert (Hglb : Share.glb Share.Rsh (Share.lub sh h) = h).
      { rewrite Share.distrib1 Hsh_no_Rsh Hh_in_Rsh Share.lub_commute Share.lub_bot //. }
      assert (Hw0 : writable0_share (Share.lub sh h)).
      { unfold writable0_share.
        destruct Hw as [_ Hsub].
        apply Hsub. }
      destruct Hw as [_ Hsub].
      apply Hh_neq_Rsh.
      rewrite <- Hglb.
      by apply join_sub_Rsh_glb.
  Qed.

  Lemma nonreadable_extend_to_exact_readable1 (sh : share) :
    sh <> Share.bot -> ~ readable_share sh ->
    exists sh', sepalg.join_sub sh sh' /\ readable_share sh' /\ ~ writable0_share sh'.
  Proof.
    intros _ Hnotread.
    set (h := (Share.split Share.Rsh).1).
    exists (Share.lub sh h).
    assert (Hsh_no_Rsh : Share.glb Share.Rsh sh = Share.bot).
    { destruct (dec_share_identity (Share.glb Share.Rsh sh)) as [Hid | Hnonid].
      - apply identity_share_bot; auto.
      - exfalso.
        apply Hnotread.
        by unfold readable_share, nonempty_share.
    }
    assert (Hh_in_Rsh : Share.glb Share.Rsh h = h).
    { subst h; apply glb_split_x. }
    assert (Hh_nonid : sepalg.nonidentity h).
    { subst h.
      destruct (Share.split Share.Rsh) as [h1 h2] eqn:Hsplit; simpl.
      unfold sepalg.nonidentity.
      intros Hid.
      apply (nonemp_split_neq2 Share.Rsh h1 h2 Rsh_nonidentity Hsplit).
      apply (Hid h2 Share.Rsh).
      eapply split_join; auto. }
    assert (Hh_neq_Rsh : h <> Share.Rsh).
    { subst h.
      destruct (Share.split Share.Rsh) as [h1 h2] eqn:Hsplit; simpl.
      apply (nonemp_split_neq1 Share.Rsh h1 h2 Rsh_nonidentity Hsplit). }
    repeat split.
    - (* sepalg.join_sub sh (Share.lub sh h) *)
      rewrite <- leq_join_sub.
      apply Share.lub_upper1.
    - (* readable_share (Share.lub sh h) *)
      apply readable_share_lub.
      unfold readable_share.
      rewrite Hh_in_Rsh //.
    - (* ~ writable0_share (Share.lub sh h) *)
      unfold writable0_share.
      intros Hsub.
      assert (Hglb : Share.glb Share.Rsh (Share.lub sh h) = h).
      { rewrite Share.distrib1 Hsh_no_Rsh Hh_in_Rsh Share.lub_commute Share.lub_bot //. }
      apply Hh_neq_Rsh.
      rewrite <- Hglb.
      by apply join_sub_Rsh_glb.
  Qed.
  
  Lemma share_extend_nonempty_to_readable (sh : share) :
    perm_of_dfrac (DfracOwn (Share sh)) = Some Nonempty ->
    exists sh', sepalg.join_sub sh sh' /\ perm_of_dfrac (DfracOwn (Share sh')) = Some Readable.
  Proof.
    intros Hperm.
    assert (Hnonbot : sh <> Share.bot).
    { unfold perm_of_dfrac, perm_of_sh' in Hperm;
      intro Hbot; subst; unfold perm_of_sh in Hperm; if_tac in Hperm; try easy.
      if_tac in Hperm; try easy.
      if_tac in Hperm; try easy.
      if_tac in Hperm; try easy.
    }
    assert (Hnotread : ~ readable_share sh).
    { intro Hread.
      unfold perm_of_dfrac, perm_of_sh, perm_of_sh', perm_of_sh in Hperm.
      repeat if_tac in Hperm; easy.
    }
    destruct (nonreadable_extend_to_exact_readable1 sh Hnonbot Hnotread)
      as (sh' & Hsub & Hread & Hnotwrite).
    exists sh'.
    split; auto.
    unfold perm_of_dfrac.
    simpl.
    destruct (writable0_share_dec sh') as [Hw0 | Hnw0].
    + exfalso.
      apply Hnotwrite; auto.
    + destruct (readable_share_dec sh') as [Hr | Hnr].
      * unfold perm_of_sh.
        repeat if_tac; easy.
      * exfalso.
        by apply Hnr.
  Qed.

  Lemma share_extend_to_perm
    (sh : share) (p : option permission) :
    Mem.perm_order'' p (perm_of_dfrac (DfracOwn (Share sh))) ->
    exists sh',
      sepalg.join_sub  sh sh' /\
        perm_of_dfrac (DfracOwn (Share sh')) = p.
  Proof.
    intros Hord.
    destruct p as [p|].
    - destruct p.
      + exists Tsh.
        split; auto.
        * exists (Share.comp sh).
          apply join_comp_Tsh.
        * unfold perm_of_dfrac.
          simpl.
          unfold perm_of_sh .
          rewrite ! if_true; auto.
      + destruct (perm_of_dfrac (DfracOwn (Share sh))) eqn:Hperm.
        * destruct p; inv Hord.
          ++ exists sh.
             split; auto.
             unfold sepalg.join_sub.
             exists Share.bot.
             eapply sepalg.join_comm.
             apply bot_join_eq.
          ++ unfold perm_of_dfrac, perm_of_sh' in Hperm.
            exists Ews.
             split; auto.
             unfold sepalg.join_sub.
             admit.
             unfold perm_of_dfrac; simpl.
             apply perm_of_Ews.
          ++ exists (Share.lub sh Ews).
             admit.
        * exists Ews.
          split.
          ++ unfold perm_of_dfrac in Hperm.
             destruct (eq_dec sh Share.bot) as [Hbot | Hbot].
             ** subst sh.
                exists Ews. apply bot_join_eq.
             ** unfold perm_of_sh' in Hperm.
                apply perm_of_sh_None in Hperm. done.
          ++ unfold perm_of_dfrac, perm_of_sh' in Hperm |- *.
             apply perm_of_Ews.
      + destruct (perm_of_dfrac (DfracOwn (Share sh))) eqn:Hperm.
        * destruct p; inv Hord.
          ++ exists sh.
             split; auto.
             unfold sepalg.join_sub.
             exists Share.bot.
             apply sepalg.join_comm.
             apply bot_join_eq.
          ++ apply share_extend_nonempty_to_readable; auto.
        * exists shares.Ers.
          split.
          ++ unfold perm_of_dfrac, perm_of_sh' in Hperm.
             destruct (eq_dec sh Share.bot) as [Hbot | Hbot].
             ** subst.
                exists shares.Ers.
                apply bot_join_eq.
             ** apply perm_of_sh_None in Hperm; done.
          ++ unfold perm_of_dfrac, perm_of_sh' in Hperm |- *.
             unfold perm_of_sh.
             destruct (writable0_share_dec Ers) as [Hw | Hnw].
             ** exfalso.
                pose proof perm_of_Ers as HErs.
                unfold perm_of_sh in HErs.
                rewrite if_true // in HErs.
                destruct (eq_dec Ers Share.top); discriminate.
             ** rewrite if_true //.
                apply readable_Ers.
      + destruct (perm_of_dfrac (DfracOwn (Share sh))) eqn:Hperm.
        * destruct p; inv Hord.
          ++ exists sh. split; try apply sepalg.join_sub_refl; done.
          ++ simpl in Hperm.
             destruct (eq_dec sh Share.bot) as [-> | Hnb].
             ** pose proof (perm_of_empty).
                rewrite Hperm in H. done.
             ** exists sh.
                split; try apply sepalg.join_sub_refl.
                done.
        * simpl in Hperm.
          unfold perm_of_sh in Hperm.
          destruct (writable0_share_dec sh) as [Hw | Hnw].
          ++ destruct (eq_dec sh Share.top); subst.
             ** rewrite if_true // in Hperm; try contradiction.
             ** rewrite if_false // in Hperm.
          ++ destruct (readable_share_dec sh) as [Hr | Hnr]; try easy.
             destruct (eq_dec sh Share.bot) as [Hbot | Hnb]; subst; last first.
             rewrite if_false // in Hperm.
             exists Share.Lsh.
             split; try eexists; try apply bot_join_eq.
             simpl.
             apply perm_of_Lsh.
    - exists sh.
      split.
      + unfold sepalg.join_sub.
        exists Share.bot.
        apply sepalg.join_comm.
        apply bot_join_eq.
      + destruct (perm_of_dfrac (DfracOwn (Share sh))) eqn:Hperm; auto.
        pose proof (perm_order''_None (Some p)). done.
  Admitted.

  Lemma coherent_loc_extend_to_curPerm
    (m : mem) (loc : address)
    (r : shared.sharedR (leibnizO resource)) :
    ✓ r ->
    coherent_loc m loc (resR_to_resource (Some r)) ->
    Mem.perm_order''
      (access_at m loc Cur)
      (perm_of_res (resR_to_resource (Some r))) ->
    exists r',
      ✓ r' /\
        r ≼ r' /\
        coherent_loc m loc (resR_to_resource (Some r')) /\
        perm_of_res (resR_to_resource (Some r')) = access_at m loc Cur.
  Proof.
    intros Hvalid Hcoh Horder.
    destruct r.
    - destruct dq; simpl in *.
      destruct s as [sh |]; simpl in *.
      + destruct (`(resource_map.elem_of_agree v)) eqn:Hv; simpl in *.
        * destruct x; simpl in Horder.
          ++ change (perm_of_sh sh)
               with (perm_of_dfrac (DfracOwn (Share sh))) in Horder.
             destruct (share_extend_to_perm sh (access_at m loc Cur) Horder)
               as (sh' & Hsub & Hperm').
             assert (rsh' : readable_share sh').
             { eapply join_sub_readable; try eapply rsh; done. }
             assert (rshd' : readable_dfrac (DfracOwn (Share sh'))).
             { auto. }
             exists (shared.YES (DfracOwn (Share sh')) rshd' v).
             repeat split.
             ** destruct Hvalid as [_ Hvalid]; auto.
             ** destruct Hsub as [sh0 Hjoin].
                assert (Hdq : DfracOwn (Share sh) ⋅ DfracOwn (Share sh0) =
                                DfracOwn (Share sh')).
                { rewrite dfrac_op_own.
                  apply f_equal.
                  apply share_op_join.
                  exists sh, sh0. repeat split; auto.
                  apply share_op_is_join; auto.
                }
                unfold included.
                destruct (shared.readable_dfrac_dec (DfracOwn (Share sh0))) as [rsh0d | Hnr0d].
                -- exists (shared.YES (DfracOwn (Share sh0)) rsh0d v).
                   rewrite shared.YES_op'.  
                   destruct (shared.readable_dfrac_dec
                               (DfracOwn (Share sh) ⋅ DfracOwn (Share sh0))) as [rshj | Hbad].
                   *** destruct Hdq.
                       rewrite agree_idemp.
                       apply shared.YES_irrel.
                   *** exfalso.
                       apply Hbad.
                       rewrite Hdq //.
                -- exists (shared.NO (V := leibnizO resource) (Share sh0) Hnr0d).
                   assert (rsh0j : readable_dfrac (DfracOwn (Share sh0) ⋅ DfracOwn (Share sh))).
                   { rewrite (comm _ (DfracOwn (Share sh)) (DfracOwn (Share sh0))) in Hdq.
                     rewrite Hdq //. }
                   transitivity
                     (shared.YES (DfracOwn (Share sh0) ⋅ DfracOwn (Share sh)) rsh0j v).
                   *** replace (DfracOwn (Share sh0) ⋅ DfracOwn (Share sh))
                         with (DfracOwn (Share sh')); last first.
                       rewrite (comm _ (DfracOwn (Share sh))) // in Hdq.
                       rewrite (comm _ (DfracOwn (Share sh))) in Hdq.
                       destruct Hdq.
                       apply shared.YES_irrel.
                   *** rewrite <- (shared.NO_YES_op _ (Share sh0) (DfracOwn (Share sh))
                                    Hnr0d rsh rsh0j v).
                       apply comm.
                       apply _.
             ** simpl.
                rewrite Hv.
                unfold coherent_loc in Hcoh.
                by destruct Hcoh as [Hcontents _].
             ** simpl.
                rewrite Hv.
                unfold coherent_loc in Hcoh.
                destruct Hcoh as [_ Hacc].
                unfold access_cohere.
                simpl.
                rewrite <- Hperm'; simpl.
                apply po_refl.
             ** simpl; rewrite Hv; done.
          ++ assert (rshd : readable_dfrac (DfracOwn (Share sh))) by done.
             exists (shared.YES (DfracOwn (Share sh)) rshd v).
             assert (Hrsh : rshd = rsh) by apply proof_irrelevance.
             repeat split.
             ** destruct Hvalid as [_ Hvalid]; auto.
             ** subst.
                eapply (dora_dist_order (shared.sharedR (leibnizO resource))); eauto.
                admit.
             ** simpl.
                rewrite Hv.
                unfold coherent_loc in Hcoh.
                by destruct Hcoh as [Hcontents _].
             ** simpl.
                rewrite Hv.
                unfold coherent_loc in Hcoh.
                destruct Hcoh as [_ Hacc].
                unfold access_cohere.
                simpl. done.
             ** simpl. rewrite Hv.
                cbn.
                admit.
          ++ admit.
      + admit.
  Admitted.

  
  Lemma coherent_rmap_extend_to_curPerm
    (m : mem)
    (s : resource_map.rmapUR share (positive * Z) (leibnizO resource)) :
    ✓ s ->
    coherent m s ->
    exists s' : resource_map.rmapUR share (positive * Z) (leibnizO resource),
      (✓ s' /\
         s ≼ s' /\
         coherent m s' /\
         mem_equiv.access_map_equiv (getCurPerm m) (perm_of_rmap s'))%type.
  Proof.
    intros Hv Hcoh.
    assert (Hchoose_pack :
             { choose :
               address ->
               shared.sharedR (leibnizO resource) ->
               option (shared.sharedR (leibnizO resource)) |
               forall loc r,
                 s !! loc = Some r ->
                 exists r',
                   choose loc r = Some r' /\
                     ✓ r' /\
                     r ≼ r' /\
                     coherent_loc m loc (resR_to_resource (Some r')) /\
                     perm_of_res (resR_to_resource (Some r')) = access_at m loc Cur }).
    { admit. }
    destruct Hchoose_pack as [choose Hchoose].
    exists (map_imap choose s).
    repeat split.
    - intros loc.
      rewrite map_lookup_imap.
      destruct (s !! loc) as [r|] eqn:Hs_loc; simpl.
      + destruct (Hchoose loc r Hs_loc) as
          (r' & Hchoose_eq & Hr_valid & Hr_incl & Hr_coh & Hr_perm).
        rewrite Hs_loc.
        simpl.
        rewrite Hchoose_eq //.
      + rewrite Hs_loc. done.
    - apply (proj2 (gmap.lookup_included s (map_imap choose s))).
      intros loc.
      destruct (s !! loc) as [r|] eqn:Hs_loc.
      + destruct (Hchoose loc r Hs_loc) as
        (r' & Hchoose_eq & Hr_valid & Hr_incl & Hr_coh & Hr_perm).
        rewrite map_lookup_imap.
        rewrite Hs_loc.
        simpl.
        rewrite Hchoose_eq //.
        apply Some_included.
        right. done.
      + rewrite map_lookup_imap.
        rewrite Hs_loc. done.
    - intro Hge.
      rewrite map_lookup_imap.
      destruct (s !! loc) as [r|] eqn:Hs_loc.
      + exfalso.
        unfold coherent in Hcoh.
        specialize (Hcoh loc).
        rewrite Hs_loc in Hcoh.
        destruct Hcoh as [Hbounds _].
        specialize (Hbounds Hge).
        discriminate.
      + rewrite Hs_loc. done.
    - destruct (s !! loc) as [r|] eqn:Hs_loc.
      + destruct (Hchoose loc r Hs_loc) as
        (r' & Hchoose_eq & Hr_valid & Hr_incl & Hr_coh & Hr_perm).
        unfold coherent_loc in Hr_coh.
        destruct Hr_coh as (Hr_contents & _).
        unfold resource_at.
        rewrite map_lookup_imap.
        rewrite Hs_loc.
        simpl.
        rewrite Hchoose_eq //.
      + unfold coherent in Hcoh.
        specialize (Hcoh loc).
        destruct Hcoh as (_ & Hcontents & _).
        unfold resource_at.
        rewrite map_lookup_imap.
        rewrite Hs_loc //.
    - destruct (s !! loc) as [r|] eqn:Hs_loc.
      + destruct (Hchoose loc r Hs_loc) as (r' & Hchoose_eq & _ & _ & Hr_coh & _).
        unfold coherent_loc in Hr_coh.
        destruct Hr_coh as (_ & Hr_access).
        unfold resource_at.
        rewrite map_lookup_imap.
        rewrite Hs_loc.
        simpl.
        rewrite Hchoose_eq //.
      + unfold coherent in Hcoh.
        specialize (Hcoh loc).
        destruct Hcoh as (_ & _ & Haccess).
        unfold resource_at in *.
        rewrite map_lookup_imap.
        rewrite Hs_loc /= in Haccess.
        rewrite Hs_loc /= //.
    - unfold mem_equiv.access_map_equiv.
      intros loc.
      extensionality ofs.
      rewrite perm_of_rmap_lookup.
      destruct (s !! (loc, ofs)) as [r|] eqn:Hs_loc.
      + destruct (Hchoose (loc, ofs) r Hs_loc) as
          (r' & Hchoose_eq & _ & _ & _ & Hr_perm).
        unfold resource_at.
        rewrite map_lookup_imap.
        rewrite Hs_loc.
        simpl.
        rewrite Hchoose_eq Hr_perm access_at_cur_getCurPerm //.
      + unfold resource_at.
        rewrite map_lookup_imap.
        rewrite Hs_loc.
        simpl.
        rewrite if_true; auto.
        admit.
  Admitted.
    

  
  Lemma coherent_exists_rmap_update γ (m : mem) (s : rmap):
    coherent m s ->
    resource_map.resource_map_auth (H1 := gen_heapGpreS_heap (gen_heapGpreS := gen_heap_inG))
      γ 1 s ==∗
    ∃ s', ⌜coherent m s' /\ mem_equiv.access_map_equiv (getCurPerm m) (perm_of_rmap s')⌝ ∗
     resource_map.resource_map_auth (H1 := gen_heapGpreS_heap (gen_heapGpreS := gen_heap_inG)) γ 1 s'.
  Proof.
    intros Hcoh.
    iIntros "Hauth".
    Admitted.
  (*
    pose proof (coherent_rmap_extend_to_curPerm m s Hcoh) as
      (s' & Hvalid' & Hincl & Hcoh' & Hperm').
    iMod (resource_map_auth_increase γ s s' with "Hauth") as "Hauth"; try done.
    iExists s'.
    iFrame.
    iPureIntro.
    split; auto.
  Qed. *)
  *)

  Lemma coherent_access_map_equiv (m : mem) (σ : rmap) :
    coherent m σ -> mem_equiv.access_map_equiv (perm_of_rmap σ) (getCurPerm m).
  Proof.
    intros Hcoh b; extensionality ofs.
    rewrite perm_of_rmap_lookup.
    destruct (Hcoh (b, ofs)) as [_ [_ Hacc]].
    rewrite /access_cohere access_at_cur_getCurPerm // in Hacc.
  Qed.
  
  Lemma jsafe_jsafe_frag : forall E z c,
      jsafe(genv_symb := genv_symb_injective) (cl_core_sem ge) (concurrent_ext_spec CS ext_link)
        ge E z c ⊢ jsafe_frag 1 E z c.
  Proof.
    intros.
    iLöb as "IH" forall (z c).
    rewrite jsafe_unfold jsafe_frag_unfold /jsafe_pre /jsafe_frag_pre.
    iIntros ">H !> % % S".
    rewrite /frag_state_interp /frag_mem_auth.
    iDestruct "S" as "(((%Hcoh & %Heq) & Hrmap) & Hext)".
    pose proof Hcoh as Hcoh'.
    apply coherent_restrPermMap_of_coherent in Hcoh'.
    destruct Hcoh' as (Hlt & Hcoh').
    iDestruct (frag_state_interp_1_to_state_interp (restrPermMap Hlt)
                with "[$Hrmap $Hext]") as "S"; try done.
    { iPureIntro; do 2 split; last apply coherent_access_map_equiv; auto. }
    iExists Hlt.
    iDestruct ("H" with "S") as "[H | [H | H]]".
    - iLeft; iDestruct "H" as (?) "($ & _ & $)".
    - iRight; iLeft.
      iMod "H" as (c' m') "(%Hstep & Hstate & Hsafe)".
      iDestruct "Hstate" as "((%σ0 & %Hcoh0 & Hma) & Hext)".
      pose proof Hcoh0 as Hcoh1.
      apply coherent_access_map_equiv in Hcoh0.
      iExists c', m', σ0.
      iFrame.
      iModIntro.
      repeat iSplit; auto.
      by iApply "IH".
    - iRight; iRight.
      iDestruct "H" as (????) "((Hmem & $) & $ & H)".
      iDestruct "Hmem" as (σ1) "(%Hcoh1 & Hmem)".
      assert (coherent m σ1) as Hcoh1'.
      { eapply coherent_of_restrPermMap_coherent; eauto. }
      iExists σ1.
      iSplit; first done. 
      iSplitL "Hmem"; try iSplit; try done.
      { iPureIntro; split; auto; apply coherent_access_map_equiv; auto. }
      iIntros "!>" (?????).
      rewrite /state_interp.
      iSpecialize ("H" $! ret m' z' with "[%]"); try done.
      iMod "H" as "H".
      iIntros "!> S Hpost".
      iDestruct "S" as "(((%Hcoh_m' & %Hacc) & Hauth') & Hext')".
      iDestruct ("H" with "[Hauth' Hext'] Hpost") as (c') "(%Hafter & [Hmem Hext'] & Hsafe)".
      { iFrame; iPureIntro; try done. }
      iPoseProof ("IH" with "Hsafe") as "Hsafe_frag".
      iDestruct "Hmem" as (σ2) "(% & Hmem)".
      iExists c', σ2.
      iFrame "%". iFrame.
      iPureIntro.
      do 2 split; auto; apply coherent_access_map_equiv; auto.
   Qed.
  
  Existing Instance mem_equiv.access_map_equiv_Equivalence.

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
  
  Definition thread_safe (tp : dtp) i (q : Qp):=
    ∃ cnti : containsThread tp i,
      match getThreadC cnti with
      | Krun c | Kblocked c => jsafe_frag q ⊤ tt c
      | Kresume c v =>
          ∀ c',
            (* [v] is not used here. The problem is probably coming from
           the definition of JuicyMachine.resume_thread'. *)
            ⌜cl_after_external None c = Some c'⌝ →
            jsafe_frag q ⊤ tt c'
      | Kinit v1 v2 =>
          ∃ q_new,
    ⌜cl_initial_core ge v1 (v2 :: nil) = Some q_new⌝ ∧
      jsafe_frag q ⊤ tt q_new
  end%I.

 (* Definition threads_safe (tp : dtp) (qs : gmap nat Qp) (m : mem) : iProp Σ :=
    [∗ list] _ ↦ i ∈ seq 0 (pos.n (OrdinalPool.num_threads tp)),
      ∃ q (σ : rmap) (cnti : containsThread tp i)
        (Hlt : permMapLt (perm_of_rmap σ) (getMaxPerm m)),
        ⌜qs !! i = Some q ∧ permMapLt (perm_of_rmap σ) (getThreadR cnti).1⌝ ∗
            thread_safe tp i q ∗ frag_mem_auth q (restrPermMap Hlt) σ. *)

  Definition threads_safe (tp : dtp) (qs : gmap nat Qp) (m : mem) : iProp Σ :=
    [∗ list] _ ↦ i ∈ seq 0 (pos.n (OrdinalPool.num_threads tp)),
      ∃ q (σ : rmap) (cnti : containsThread tp i)
        (Hlt : permMapLt (perm_of_rmap σ) (getMaxPerm m)),
        ⌜qs !! i = Some q ∧
          mem_equiv.access_map_equiv (perm_of_rmap σ) (getThreadR cnti).1⌝ ∗
            thread_safe tp i q ∗
            frag_mem_auth q (restrPermMap Hlt) σ.

  
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
    Transparent Mem.storebytes.
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
      (* apply free_list_contents in Hfl.
      by rewrite Hfl. *)
      Admitted. 

  (*
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
Qed. *)

(*
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
*)

Lemma Mem_unchecked_restrPermMap :
  forall (m: Mem.mem) (p: access_map) (Hlt : permMapLt p (getMaxPerm m)) l,
    Mem_load_unchecked Mptr (restrPermMap Hlt) l.1 l.2 =
      Mem_load_unchecked Mptr m l.1 l.2.
Proof. intros m p Hlt [b ofs]; by unfold Mem_load_unchecked. Qed.

Lemma state_interp_with_rmap_to_frag m (z : unit) σ :
  state_interp_with_rmap m z σ ⊢ frag_state_interp 1 m σ z.
Proof.
  rewrite /state_interp /frag_state_interp /frag_mem_auth /mem_auth .
  iIntros "(Hmem & Hext)".
  iFrame.
Qed.

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
    pose proof (empty_coherent Mem.empty) as Hcoh_empty.
    iMod (init_conc_VST_frag () tt) as "H".
    iSpecialize ("H" $! Hinv).
    iDestruct "H" as (HG FS ES HL) "(Hstate & Hfunspec & Hext & locks & _)".
    set (HHfrag := Build_VSTGS _ _
             ({| heapGS_invGS := Hinv;
                heapGS_gen_heapGS := HG;
                heapGS_funspecGS := FS |} : heapGS Σ) ES).
    destruct (spr HHfrag HL) as (b & q & (? & ? & Hinit) & Hsafe); [| done..].
    iMod (Hsafe with "[$Hstate $Hfunspec $Hext]") as (?) "(S & Heq & Hsafe)".
    iDestruct "Heq" as "%Heq".
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
    iPoseProof (state_interp_with_rmap_to_frag with "S") as "S".
    set qs := (<[0 := 1%Qp]> (∅ : gmap nat Qp)).
    rewrite /frag_state_interp /frag_mem_auth.
    iDestruct "S" as "([(%Hcoh & %Haceq) Hmem] & Hext)".
    iAssert (@threads_safe HHfrag HL tp qs (`init_mem)) with "[Hsafe Hmem]" as "Hsafe".
    { subst tp.
      rewrite /frag_state_interp /threads_safe /thread_safe /frag_mem_auth /=.
      iSplit; auto.
      assert (Hlt : permMapLt (perm_of_rmap σ) (getMaxPerm (`init_mem))).
      { apply (coherent_perm_of_rmap_max (`init_mem) σ Hcoh). }
      iExists 1%Qp, σ, _, Hlt.
      repeat iSplit; auto.
      iSplitL "Hsafe".
      - unshelve iExists _; first done; iApply (jsafe_jsafe_frag with "Hsafe").
      - iSplit; auto.
        iPureIntro.
        apply coherent_restrPermMap with (Hlt := Hlt) in Hcoh.
        split; auto.
        apply coherent_access_map_equiv; auto.
    }
    assert (locks_coherent tp (`init_mem) ∅) as Hlocks by done.
    forget (proj1_sig init_mem) as m.
    forget (@nil Events.machine_event) as tr.
    clearbody tp.
    set (ls := ∅) in Hlocks |- *.
    clearbody ls.
    clear dependent b x q.
    clearbody qs.
    clear Heq Hcoh Haceq σ.
    iLöb as "IH" forall (sch tr tp m n ls qs Htp_wf Hinvariant Hcompat Hlocks).
    destruct n as [|n].
    { iPureIntro. constructor. }
    destruct sch as [|i sch].
    { iApply step_fupdN_intro; first done; iPureIntro. constructor; done. }
    simpl; destruct (lt_dec i (pos.n (OrdinalPool.num_threads tp))).
    2 : {
      Local Opaque lock_state.
      iApply step_fupd_intro; try done.
      iNext.
      iAssert (|={⊤}[∅]▷=>^n ∀ U'',
             ⌜HybridMachineSig.HybridCoarseMachine.csafe (U'', tr, tp) m n⌝) with "[-]" as "H".
      { rewrite step_fupdN_plain_forall //.
        iIntros (U'').
        iApply ("IH" $! U'' tr tp m n ls qs with "[] [] [] [] locks Hext"); try done. }
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
    iPoseProof (big_sepL_lookup_acc_impl i i with "[$Hsafe]") as "Hsafe".
    apply lookup_seq; eauto.
    iDestruct "Hsafe" as "((% & %σ1 & % & % & (% & %Heq1) & ((% & Hsafei) &  Hfragi)) & Hsafe)".
    replace cnti0 with cnti by apply ProofIrrelevance.proof_irrelevance.
    clear cnti0.
    destruct (getThreadC cnti) eqn: Hi.
    - (* Krun *)
      destruct (cl_halted s) eqn: Hhalt; [|destruct (cl_at_external s) eqn: Hat_ext].
      + (* halted *)
        assert (HybridMachineSig.halted_thread cnti Int.zero) as Hhalt'.
        { econstructor; eauto. hnf; rewrite Hhalt //. }
        iApply step_fupd_intro; first done; iNext.
        iAssert (threads_safe tp qs m) with "[Hsafei Hfragi Hsafe]" as "Hsafe".
        { iApply "Hsafe".
          + iIntros "!>" (????) "H"; iApply "H".
          + iExists q, σ1 , cnti, Hlt.
            iSplit; auto; iFrame.
            rewrite /thread_safe.
            iExists cnti; rewrite Hi //. }
        iAssert (|={⊤}[∅]▷=>^n ∀ U'',
            ⌜HybridMachineSig.HybridCoarseMachine.csafe (U'', tr, tp) m n⌝) with "[-]" as "H".
        { rewrite step_fupdN_plain_forall //.
          iIntros (x).
          iApply ("IH" $! _ _ _ _ _ _ with "[] [] [] [] locks Hext Hsafe"); try done.
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
          iApply ("IH" $! x tr (updThreadC cnti (Kblocked s)) m n ls qs
                   with "[%] [%] [%] [%] locks Hext [Hsafe Hfragi Hsafei]"); try done.
          - intros j cntj.
            destruct (eq_dec j i) as [-> | Hneq].
            + rewrite (gssThreadCC cnti (Kblocked s) cntj) /= Hat_ext //.
            + pose proof (cntUpdateC' (Kblocked s) cnti cntj) as cntj0.
              rewrite -gsoThreadCC //; by apply Htp_wf.
          - by apply ThreadPoolWF.updThreadC_invariant.
          - by apply StepLemmas.updThreadC_compatible.
          - iApply "Hsafe".
            + iIntros "!>" (k y (-> & ?)%lookup_seq Hneq) "Hy".
              iDestruct "Hy" as (q0 σ0 cnty Hltσ) "((%Hqy & %Hlt2) & Hsafe_y & Hfrag_y)".
              iExists q0, σ0, (cntUpdateC _ _ cnty), Hltσ.
              iSplit.
              * iPureIntro.
                split; auto.
                rewrite gThreadCR //.
              * iFrame.
                replace (0 + k) with k by lia.
                assert (Hneq' : i <> k) by lia.
                iDestruct "Hsafe_y" as (cntyk) "Hsafe_y".
                iExists (cntUpdateC (Kblocked s) cnti cntyk).
                rewrite -(gsoThreadCC Hneq') //.
            + iExists q, σ1, (cntUpdateC (Kblocked s) cnti cnti), Hlt.
              iSplit; auto.
              * destruct H; iSplit; auto.
                rewrite (gThreadCR cnti cnti (Kblocked s) (cntUpdateC (Kblocked s) cnti cnti)) //.
              * iFrame; iExists (cntUpdateC (Kblocked s) cnti cnti); rewrite gssThreadCC //.
        }
        iApply (step_fupdN_mono with "H"); iPureIntro; intros Hsafe.
        eapply HybridMachineSig.HybridCoarseMachine.AngelSafe
          with (tr := []); simpl; rewrite seq.cats0; last apply Hsafe.
        eapply HybridMachineSig.suspend_step; eauto.
      + (* corestep: HybridMachineSig.thread_step *)
        rewrite jsafe_frag_unfold /jsafe_frag_pre.
        iAssert (⌜coherent (restrPermMap Hlt) σ1⌝) with "[Hfragi]" as "%Hcoh".
        { by iDestruct "Hfragi" as "((? & ?) & ?)". }
        iMod "Hsafei" as "Hsafei".
        iDestruct ("Hsafei" $! (restrPermMap Hlt) σ1
                    with "[$Hfragi $Hext]") as (Hlt0) "[Hhalt | [Hstep | Hext]]".
        { iDestruct "Hhalt" as (? Hhalt') "?"; done. }
        2 : { iDestruct "Hext" as (???? Hext) "?". simpl in Hext; congruence. }
        (* HStep *)
 
        assert (Hrestr: restrPermMap Hlt0 = restrPermMap Hlt).
        { etransitivity; try apply restrPermMap_idem; apply restr_proof_irr. } 
        iMod "Hstep" as (???) "(%Hstep & S & Hsafei)".
        rewrite Hrestr in Hstep.
        clear Hrestr Hlt0.
        assert (Hmem :
                 restrPermMap (ssrfun.pair_of_and (Hcompat i cnti)).1 =
                   restrPermMap Hlt).
        { erewrite restrPermMap_ext; eauto. }
        assert (corestep (cl_core_sem ge) s
                  (restrPermMap (ssrfun.pair_of_and (Hcompat i cnti)).1) c' m') as Hstep'.
        { rewrite Hmem //. }
        iApply step_fupd_intro; first done; iNext.
        apply (ev_step_ax2 (Clight_evsem.CLC_evsem ge)) in Hstep' as (? & Hstep').
        (* Does we need getThreadR cnti = perm_of_rmap σ *)
        assert (Hmemstep : mem_step (restrPermMap Hlt) m').
        { eapply (CLC_corestep_mem _ _ (restrPermMap Hlt)); eauto. }
        assert (mem_compatible (updThread cnti (Krun c') (getCurPerm m', (getThreadR cnti).2)) m')
          as Hcompat' by by eapply (CoreLanguageDry.corestep_compatible(Sem := Sem)).
        iDestruct "S" as "(Hfragi & Hext)".
        iSpecialize ("IH" $! _ _ (updThread cnti (Krun c')
                                    (getCurPerm m', (getThreadR cnti).2)) m' n ls qs
                      with "[%] [%] [%] [%] locks Hext [Hsafe Hsafei Hfragi]"); try done.
        * (* threads_wellformed *)
          intros j cntj.
          destruct (eq_dec j i); first by subst; rewrite gssThreadCode.
          pose proof (cntUpdate' _ _ cnti cntj).
          rewrite gsoThreadCode //; apply Htp_wf.
        * (* invariant *)
          eapply (CoreLanguageDry.corestep_invariant(Sem := Sem)); try done.
        * (* locks_coherent *)
          admit.
        * iApply "Hsafe".
          ** iIntros "!>" (k y (-> & ?)%lookup_seq Hneq) "Hy".
             iDestruct "Hy" as (q0 σ0 cnty Hltσ0) "((% & %Hqy) & Hsafe_y & Hfrag_y)".
             replace (0 + k) with k in * by lia.
             assert (Hneq' : i <> k) by lia.
             set (cnty' :=
                    @cntUpdate _ _ _ i (0 + k) tp
                      (Krun c')
                      (getCurPerm m', (getThreadR cnti).2)
                      cnti cnty).
             iExists q0, σ0, cnty'.
             pose proof ((no_race_thr _ Hinvariant) _ _ cnti cnty Hneq') as Hthread_disj2.
             assert (Hrmap_disj : permMapsDisjoint (perm_of_rmap σ1) (perm_of_rmap σ0)).
             { unfold permMapsDisjoint in *.
               intros b ofs.
               rewrite /permMapsDisjoint2 in Hthread_disj2.
               eapply perm_union_lower_2.
               - eapply ((proj1 Hthread_disj2) b ofs).
               - rewrite (Heq1 b). apply po_refl.
               - rewrite (Hqy b). apply po_refl. }
             assert (Hdecay : decay (restrPermMap Hlt) m').
             { apply (@msem_decay CC_core (CLC_memsem ge) s (restrPermMap Hlt) c' m' Hstep). }
             assert (Hpres : permMapLt (perm_of_rmap σ0) (getMaxPerm m')).
             { eapply (permMapLt_decay_disjoint _ (restrPermMap Hlt)); eauto.
               + by rewrite restr_Max_eq.
               + unfold permMapsDisjoint in *.
                 intros b ofs.
                 rewrite getCurPerm_correct.
                 rewrite (restrPermMap_Cur Hlt b ofs).
                 apply (Hrmap_disj b ofs).
             }
             iExists Hpres.
             iSplit; auto.
             ++ iPureIntro. split; auto.
                subst cnty'.
                erewrite gsoThreadRes; eauto.
             ++ iDestruct "Hsafe_y" as (cnty0) "Hsafe_y".
                iSplitL "Hsafe_y".
                { iExists cnty'; rewrite gsoThreadCode; auto. }
                iApply (frag_mem_auth_corestep_other
                    q0 m m' (perm_of_rmap σ1)  σ0 Hlt Hltσ0 Hpres Hmemstep Hrmap_disj); auto.
                ** iDestruct "Hfragi" as "((%Hσ' & Heqσ') & Hauth)".
                   assert (Hltσ' : permMapLt (perm_of_rmap σ') (getMaxPerm m')).
                   { apply coherent_perm_of_rmap_max; auto. }
                   iExists q, σ', _, Hltσ'.
                   repeat iSplit; auto.
                   rewrite gssThreadRes; auto.
                   iSplitR "Hauth".
                   { iExists _; rewrite gssThreadCode; auto. }
                   iFrame.
                   iPureIntro.
                   apply coherent_restrPermMap with (Hlt := Hltσ') in Hσ'.
                   do 2 split; auto.
                   apply coherent_access_map_equiv; auto.
        * iApply (step_fupdN_mono with "IH").
          iPureIntro; intros Hsafe.
          eapply HybridMachineSig.HybridCoarseMachine.CoreSafe; last exact Hsafe.
          rewrite /HybridMachineSig.MachStep /=.
          change (i :: sch) with (HybridMachineSig.yield (i :: sch)) at 2.
          change m' with (HybridMachineSig.diluteMem m') at 3.
          eapply HybridMachineSig.thread_step; first done.
          simpl in Hsafe.
          eapply step_dry; eauto.
          rewrite Hmem in Hstep'.
          instantiate (1 := x).
          by change (ev_step (Clight_evsem.CLC_evsem ge) s (restrPermMap Hlt) x c' m').
    - (* Kblocked: HybridMachineSig.sync_step *)
      pose proof (Htp_wf _ cnti) as Hwfi; rewrite Hi in Hwfi.
      rewrite jsafe_frag_unfold /jsafe_frag_pre.
      iAssert (⌜coherent (restrPermMap Hlt) σ1⌝) with "[Hfragi]" as "%Hcoh".
      { by iDestruct "Hfragi" as "((? & ?) & ?)". }
      iMod "Hsafei" as "Hsafei".
      iDestruct ("Hsafei" $! (restrPermMap Hlt) σ1
                  with "[$Hfragi $Hext]") as (Hlt0) "[Hhalt | [Hstep | Hext]]".
      { iDestruct "Hhalt" as (? Hhalt') "?"; destruct s; done. }
      { iMod "Hstep" as (??? Hstep) "?".
        apply cl_corestep_not_at_external in Hstep; done. }
      (* cl_at_external s = Some (e, args) *)
      iDestruct "Hext" as (???? Hat_ext) "(S & Hpre & Hpost)".
      simpl in Hat_ext.

      admit.

    - (* Kresume: HybridMachineSig.resume_step *)
      pose proof (Htp_wf _ cnti) as Hwfi; rewrite Hi in Hwfi; destruct Hwfi as (? & ->).
      destruct s; try done.
      destruct f; try done.
      assert (HybridMachineSig.resume_thread m cnti (updThreadC cnti (Krun (Returnstate Vundef c)))) as Hresume.
      { unfold cl_at_external in *; destruct (ef_inline e) eqn: Hinline; try done.
        eapply (HybridMachineSig.ResumeThread _ _ _ _ _ _ _ _ _ Hcompat); try done; simpl; by rewrite ?Hinline. }
      iApply step_fupd_intro; first done; iNext.
      iSpecialize ("IH" $! _ _ (updThreadC cnti (Krun (Returnstate Vundef c)))
                    with "[%] [%] [%] [%] locks Hext [Hsafe Hsafei Hfragi]").
      + intros j cntj.
        destruct (eq_dec j i).
        * subst; rewrite gssThreadCC //.
        * pose proof (cntUpdateC' _ cnti cntj) as cntj0.
          rewrite -gsoThreadCC //; apply Htp_wf.
      + by apply ThreadPoolWF.updThreadC_invariant.
      + by apply StepLemmas.updThreadC_compatible.
      + rewrite /locks_coherent in Hlocks |- *.
        intros. admit.
      + iApply "Hsafe".
        * iIntros "!>" (?? (-> & ?)%lookup_seq ?)
            "(%q0 & %σ0 & (%cnty & %Hltσ0 & (%Hqs & %Hqy) & Hsafe_y & Hfrag_y))".
          assert (Hik : i <> 0 + k) by lia.
          Check OrdinalPool.cntUpdateC (Krun (Returnstate Vundef c)) cnti cnty.
          pose (cnty' := OrdinalPool.cntUpdateC (Krun (Returnstate Vundef c)) cnti cnty).
          pose proof (@OrdinalPool.gThreadCR _ _ i (0 + k) tp cnti cnty
                        (Krun (Returnstate Vundef c)) cnty') as HR.
          iExists q0, σ0, cnty', Hltσ0.
          iSplit; auto.
          ** iPureIntro.
             split; eauto.
             pose proof (f_equal (fun r => r.1) HR) as HR1.
             rewrite HR1 //.
          ** iFrame.
             rewrite /thread_safe.
             iDestruct "Hsafe_y" as (cnty0) "Hsafe_y".
             assert (cnty0' : containsThread (updThreadC cnti (Krun (Returnstate Vundef c))) (0 + k)); try done.
             iExists cnty0'.
             have -> : (getThreadC cnty0' = getThreadC cnty0).
             { by symmetry; apply gsoThreadCC. }
             iFrame.
        * assert (cnti' : containsThread (updThreadC cnti (Krun (Returnstate Vundef c))) i); try done.
          iExists q, σ1, cnti', Hlt.
          iSplit; try iPureIntro.
          split; auto.
          have -> : (getThreadR cnti').1 = (getThreadR cnti).1; try done.
          { rewrite /getThreadR /=.
            have <- : fintype.Ordinal cnti = fintype.Ordinal cnti'.
            { f_equal; apply proof_irrelevance. } 
            done.
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
      set (m' := restrPermMap (ssrfun.pair_of_and (Hcompat i cnti)).1).
      set (tp' := updThread cnti (Krun q_new) (HybridMachineSig.add_block Hcompat cnti m')).
      assert (HybridMachineSig.start_thread m cnti tp' m').
      { econstructor; done. }
      iApply step_fupd_intro; first done; iNext.
      iSpecialize ("IH" $! _ _ tp' m' with "[%] [%] [%] [%] locks Hext [Hsafe Hsafei Hfragi]").
      + (* threads_wellformed tp' *)
        intros j cntj.
        destruct (eq_dec j i).
        * subst; rewrite gssThreadCode //.
        * pose proof (cntUpdate' _ _ cnti cntj).
          rewrite gsoThreadCode //; apply Htp_wf.
      + (* invariant tp' *)
        by eapply (CoreLanguageDry.initial_core_invariant(Sem := Sem)).
      + (* mem_compatible tp' m' *)
        eapply InternalSteps.start_compatible; try done.
      + admit.
      + iApply "Hsafe".
        * iIntros "!>" (?? (-> & ?)%lookup_seq ?)
            "(%q0 & %σ0 & (%cnty & %Hltσ0 & (%Hqs & %Hqy) & Hsafe_y & Hfrag_y))".
          have Hik : i <> 0 + k by lia.
          subst tp'.
          have Hltσ0' : permMapLt (perm_of_rmap σ0) (getMaxPerm m').
          { rewrite /m' restr_Max_eq //. }
          assert (cnty' : containsThread (updThread cnti (Krun q_new)
                        (HybridMachineSig.add_block Hcompat cnti m')) (0 + k)).
          { by eapply cntUpdate. }
          iExists q0, σ0, cnty', Hltσ0'.
          iSplit.
          ** iPureIntro.
             split; eauto.
             rewrite gsoThreadRes //.
          ** rewrite (restrPermMap_idem Hltσ0') (restr_proof_irr (permMapLt_restr Hltσ0') Hltσ0).
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
          iSplit.
          ** iPureIntro.
             split; auto.
             subst tp'.
             rewrite gssThreadRes.
             rewrite /HybridMachineSig.add_block /=.
             subst m'.
             pose proof (mem_equiv.getCur_restr (getThreadR cnti).1 m
                  (ssrfun.pair_of_and (Hcompat i cnti)).1) as Hcur.
             unfold mem_equiv.access_map_equiv in *.
             intros b.
             rewrite Heq1 Hcur //.
          ** subst tp'.
             rewrite /thread_safe.
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
