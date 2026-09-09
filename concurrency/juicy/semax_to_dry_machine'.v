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

  Lemma CEspec_acquire_pre `{!VSTGS unit Σ, !lockGS Σ}
    (x : Jext_spec_type (concurrent_ext_spec CS ext_link) LOCK)
    (args : list val) :
    Jext_spec_pre (concurrent_ext_spec CS ext_link) LOCK x (genv_symb_injective ge) (sig_args (ef_sig LOCK)) args ⊣⊢
      match acquire_spec with
      | mk_funspec _ _ A _ P _ =>
          ∃ x'',
    ⌜JMeq.JMeq x x''⌝ ∧ funspec2pre' A P x'' (genv_symb_injective ge) (sig_args (ef_sig LOCK)) args
  end.
  Proof.
    solve_spec x.
  Qed.

  Lemma CEspec_acquire_post `{!VSTGS unit Σ, !lockGS Σ} (x : Jext_spec_type (concurrent_ext_spec CS ext_link) LOCK) (ret : option val) :
    Jext_spec_post (concurrent_ext_spec CS ext_link) LOCK x (genv_symb_injective ge) (sig_res (ef_sig LOCK)) ret ⊣⊢
      match acquire_spec with
      | mk_funspec _ _ A _ _ Q => ∃ x'', ⌜JMeq.JMeq x x''⌝ ∧ funspec2post' A Q x'' (genv_symb_injective ge) (sig_res (ef_sig LOCK)) ret
  end.
  Proof.
    solve_spec x.
  Qed.

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

  Program Definition spr (HH : VSTGS unit Σ) (HL : lockGS Σ) :=
    semax_prog_rule_with_rmap (concurrent_ext_spec CS ext_link) V G prog
      (proj1_sig init_mem) 0 tt _ (all_safe HH HL) (proj2_sig init_mem).
  Next Obligation. Proof. intros; iIntros (??); done. Qed.
 
  Instance Sem : Semantics :=
    ClightSemanticsForMachines.ClightSem (Clight.globalenv CPROOF.(CSL_prog)).
  
  Existing Instance HybridMachineSig.HybridCoarseMachine.DilMem.
  Existing Instance HybridMachineSig.HybridCoarseMachine.scheduler.

  Print frag_mem_auth.
  Print coherent.
  Print coherent_loc .
  Print access_cohere.
  Print acquire_spec.
  Print funspec2post'.
  Search (lockRes _ _ = Some _ -> _).
  Search (frag_mem_auth _ _ _ -∗ _ -∗ _).
  Search (build_delta_content _ _).

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

  Definition frag_state_interp q (m : mem) (σ : rmap) z : iProp Σ :=
    frag_mem_auth q m σ ∗ ext_auth z.
  
  Lemma locks_init `{InGlock : !inG Σ (gmap_view.gmap_viewR address (later (iPropO Σ)))}
    (m : mem) :
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
        ∃ (HG : gen_heapGS share address resource Σ) (FS : funspecGS Σ) (ES : externalGS Z Σ) (HL : lockGS Σ),
          @state_interp Σ Z HG ES Mem.empty z ∗ @funspec_auth Σ FS (∅ : gmap address funspecO') ∗
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

  (** jsafe_frag_pre **)
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

  Lemma state_interp_with_rmap_to_frag m (z : unit) σ :
    state_interp_with_rmap m z σ ⊢ frag_state_interp 1 m σ z.
  Proof.
    rewrite /state_interp /frag_state_interp /frag_mem_auth /mem_auth .
    iIntros "(Hmem & Hext)".
    iFrame.
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
  Qed. *)

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
            lockRes tp l = Some (empty_map, empty_map)) \/
            (Mem_load_unchecked Mptr m l.1 l.2 = (Vptrofs Ptrofs.one))) /\
      (forall i  (cnti : containsThread tp i) (Hp : permMapLt (getThreadR cnti).1 (getMaxPerm m)),
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

  (* *)

  Lemma lock_inv_in_lock_state m ls sh l R :
    lock_state m ls -∗ lock_inv sh l R -∗ ⌜∃ l_addr, val2adr l l_addr ∧ l_addr ∈ ls⌝.
  Proof.
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

  Lemma lock_inv_acquire (q : Qp) (m : mem) (ls : gset address) (σ0 : rmap)
    (Hlt : permMapLt (perm_of_rmap σ0) (getMaxPerm m)) sh b (o : ptrofs) (R : mpred) :
    Mem_load_unchecked Mptr m b (Ptrofs.unsigned o) = Vptrofs Ptrofs.one →
    frag_mem_auth q (restrPermMap Hlt) σ0 -∗ lock_state m ls -∗ lock_inv sh (Vptr b o) R ==∗
     let m' := Mem_store_unchecked Mptr m b (Ptrofs.unsigned o) (Vptrofs Ptrofs.zero) in
     ∃ Hlt' : permMapLt (perm_of_rmap σ0) (getMaxPerm m'),
       frag_mem_auth q (restrPermMap Hlt') σ0 ∗ lock_state m' ls ∗ lock_inv sh (Vptr b o) R ∗ ▷ R.
  Admitted.

  Lemma locks_coherent_acquire_update (tp : dtp) (m m' : mem) (ls : gset address) (i : nat)
    (cnti : containsThread tp i) (c : CC_core) (newThreadPerm : access_map * access_map)
    (l : address) (Hl : l ∈ ls) (Hlocks : locks_coherent tp m ls)
    (* The store changes the acquired lock to zero. *)
    (Hload_same : Mem_load_unchecked Mptr m' l.1 l.2 = Vptrofs Ptrofs.zero)
    (* The store does not change any other lock. *)
    (Hload_other : forall l', l' ∈ ls -> l' <> l -> Mem_load_unchecked Mptr m' l'.1 l'.2 =
                                              Mem_load_unchecked Mptr m l'.1 l'.2)
    (* All threads in the resulting pool retain Nonempty on lock addresses. *)
    (Hnonempty : forall (l' : address),
        l' ∈ ls -> forall (j : nat)
           (cntj : containsThread (updLockSet (updThread cnti (Kresume c Vundef)newThreadPerm) l
                   (empty_map, empty_map)) j)
           (Hp : permMapLt (getThreadR cntj).1 (getMaxPerm m')),
         nonEmptyRangeCur (restrPermMap Hp) l') :
  locks_coherent (updLockSet (updThread cnti (Kresume c Vundef) newThreadPerm) l (empty_map, empty_map)) m' ls.
  Proof.
    rewrite /locks_coherent in Hlocks |- *.
    intros l' Hl'.
    destruct (decide (l' = l)) as [Heq | Hneq].
    - subst l'.
      split.
      + rewrite gssLockRes //.
      + split. left.
        split; auto.
        rewrite gssLockRes //.
        intros j cntj Hp.
        eapply Hnonempty; auto.
    - pose proof (Hlocks l' Hl') as Hlocks'.
      destruct Hlocks' as (HlockRes' & HlockState' & Hrange').
      assert (HlockRes_eq : lockRes (updLockSet (updThread cnti (Kresume c Vundef) newThreadPerm)
                                       l (empty_map, empty_map)) l' = lockRes tp l').
      { rewrite gsoLockRes //. }
      split.
      + rewrite HlockRes_eq //.
      + split; last first.
        intros j cntj Hp.
        eapply Hnonempty; auto.
        rewrite HlockRes_eq Hload_other //.
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

  Definition acquire_virtue_map
    (maxp lockp threadp : access_map) : delta_map :=
    PTree.map
      (fun b max_b =>
       fun ofs =>
         match max_b ofs, lockp # b ofs with
         | Some _, Some _ =>
             perm_union (lockp # b ofs) (threadp # b ofs)
         | _, _ => None
         end)
      maxp.2.

  Locate permjoin.
  Lemma perm_union_permjoin :
    forall p1 p2 p3,
      perm_union p1 p2 = Some p3 ->
      permjoin_def.permjoin p1 p2 p3.
  Proof.
    intros p1 p2 p3 Hunion.
    destruct p1 as [p1 |], p2 as [p2 |];
      try destruct p1;
      try destruct p2;
      cbn in Hunion;
      try discriminate;
      inversion Hunion;
      subst;
      constructor.
  Qed.

  Lemma permMapLt_at_None :
    forall pmap maxp b ofs,
      permMapLt pmap maxp ->
      maxp # b ofs = None ->
      pmap # b ofs = None.
  Proof.
    intros pmap maxp b ofs Hlt Hmax.
    specialize (Hlt b ofs).
    rewrite Hmax in Hlt.
    destruct (pmap # b ofs) as [p |] eqn:Hp; auto.
    simpl in Hlt.
    contradiction.
  Qed.

  Locate sub_map.
  Lemma acquire_virtue_map_sub :
    forall maxp lockp threadp,
      bounded_maps.sub_map (acquire_virtue_map maxp lockp threadp)
        maxp.2.
  Proof.
    intros maxp lockp threadp.
    unfold bounded_maps.sub_map.
    intros b delta_b Hdelta.

    unfold acquire_virtue_map in Hdelta.
    rewrite PTree.gmap in Hdelta.

    destruct (maxp.2 !! b)%maps  as [max_b |] eqn:Hmax;
      try discriminate.

    inversion Hdelta; subst delta_b.
    exists max_b.
    split; auto.
    unfold bounded_maps.fun_leq'.
    intros ofs Hsome.
    destruct (max_b ofs) as [pmax |] eqn:Hmaxofs;
      simpl in *;
      auto.
  Qed.

  Check acquire_virtue_map _ _ _.
  Check computeMap.

  Lemma computeMap_acquire_virtue_map :
  forall maxp lockp threadp b ofs result,
    isCanonical maxp ->
    permMapLt lockp maxp ->
    perm_union
      (lockp # b ofs)
      (threadp # b ofs) = Some result ->
    (computeMap
      threadp
      (acquire_virtue_map maxp lockp threadp))
      # b ofs = result.
Proof.
  intros maxp lockp threadp b ofs result
    Hcanonical Hlocklt Hunion.

  destruct (maxp.2 !! b)%maps as [max_b |] eqn:Hmaxb.

  - (* The maximum-permission tree contains b. *)
    assert (Hdelta :
             ((acquire_virtue_map maxp lockp threadp) !! b)%maps =
      Some
        (fun z =>
           match max_b z, lockp # b z with
           | Some _, Some _ =>
               perm_union (lockp # b z) (threadp # b z)
           | _, _ => None
           end)).
    {
      unfold acquire_virtue_map.
      rewrite PTree.gmap.
      rewrite Hmaxb.
      reflexivity.
    }

    destruct (max_b ofs) as [pmax |] eqn:Hmaxofs.

    + destruct (lockp # b ofs) as [plock |] eqn:Hlock.

      * (* The lock contributes at this address. *)
        eapply computeMap_1 with
          (df :=
             fun z =>
               match max_b z, lockp # b z with
               | Some _, Some _ =>
                   perm_union
                     (lockp # b z)
                     (threadp # b z)
               | _, _ => None
               end).
        -- exact Hdelta.
        -- rewrite Hmaxofs Hlock.
           exact Hunion.
      * (* The lock contributes nothing: preserve threadp. *)
        assert (Hdelta_ofs :
          (fun z =>
             match max_b z, lockp # b z with
             | Some _, Some _ =>
                 perm_union
                   (lockp # b z)
                   (threadp # b z)
             | _, _ => None
             end) ofs = None).
        {
          rewrite Hmaxofs Hlock.
          reflexivity.
        }
        simpl in Hunion.
        injection Hunion as Hresult.
        subst result.
        unfold PMap.get.
        rewrite PTree.gcombine; auto.
        rewrite Hdelta.
        simpl.
        destruct (threadp.2 !! b)%maps as [thread_b |] eqn:Hthread_b;
          cbn;
          rewrite Hdelta_ofs;
          reflexivity.
    + (* maxp is None at this offset, so lockp is also None. *)
      assert (Hmaxnone : maxp # b ofs = None).
      {
        unfold Maps.PMap.get.
        rewrite Hmaxb.
        exact Hmaxofs.
      }

      pose proof
        (permMapLt_at_None
           lockp maxp b ofs Hlocklt Hmaxnone)
        as Hlocknone.

      assert (Hdelta_ofs :
        (fun z =>
           match max_b z, lockp # b z with
           | Some _, Some _ =>
               perm_union
                 (lockp # b z)
                 (threadp # b z)
           | _, _ => None
           end) ofs = None).
      {
        rewrite Hmaxofs.
        reflexivity.
      }

      rewrite Hlocknone in Hunion.
      cbn in Hunion.
      inversion Hunion; subst result.

      eapply computeMap_2;
        eauto.

  - (* maxp has no tree entry for b. *)
    assert (Hdeltanone :
             (acquire_virtue_map maxp lockp threadp !! b)%maps = None).
    {
      unfold acquire_virtue_map.
      rewrite PTree.gmap.
      rewrite Hmaxb.
      reflexivity.
    }

    assert (Hmaxnone : maxp # b ofs = None).
    {
      unfold isCanonical in Hcanonical.
      unfold Maps.PMap.get.
      rewrite Hmaxb.
      rewrite Hcanonical.
      reflexivity.
    }

    pose proof
      (permMapLt_at_None
         lockp maxp b ofs Hlocklt Hmaxnone)
      as Hlocknone.

    rewrite Hlocknone in Hunion.
    cbn in Hunion.
    inversion Hunion; subst result.

    eapply computeMap_3;
      eauto.
Qed.

Lemma acquire_virtue_map_join :
  forall maxp lockp threadp,
    isCanonical maxp ->
    permMapLt lockp maxp ->
    permMapsDisjoint lockp threadp ->
    permMapJoin
      lockp
      threadp
      (computeMap
         threadp
         (acquire_virtue_map maxp lockp threadp)).
Proof.
  intros maxp lockp threadp
    Hcanonical Hlocklt Hdisjoint.

  unfold permMapJoin.
  intros b ofs.

  destruct (Hdisjoint b ofs) as [result Hunion].

  erewrite computeMap_acquire_virtue_map;
    eauto.

  eapply perm_union_permjoin.
  exact Hunion.
Qed.

Lemma acquire_virtue_map_lt :
  forall maxp lockp threadp,
    isCanonical maxp ->
    permMapLt lockp maxp ->
    permMapLt threadp maxp ->
    permMapsDisjoint lockp threadp ->
    permMapLt
      (computeMap
         threadp
         (acquire_virtue_map maxp lockp threadp))
      maxp.
Proof.
  intros maxp lockp threadp
    Hcanonical Hlocklt Hthreadlt Hdisjoint.
  unfold permMapLt in Hlocklt, Hthreadlt |- *.
  unfold permMapsDisjoint in Hdisjoint.
  intros b ofs.
  specialize (Hlocklt b ofs).
  specialize (Hthreadlt b ofs).

  destruct ((maxp.2 !! b)%maps) as [max_b |] eqn:Hmaxb.
  - set (df :=
      fun z : Z =>
        match max_b z with
        | Some _ =>
            match lockp # b z with
            | Some _ =>
                perm_union (lockp # b z) (threadp # b z)
            | None => None
            end
        | None => None
        end).

    assert (Hdelta :
      (acquire_virtue_map maxp lockp threadp !! b)%maps = Some df).
    {
      unfold acquire_virtue_map, df.
      rewrite Maps.PTree.gmap Hmaxb.
      reflexivity.
    }

    destruct (max_b ofs) as [pmax |] eqn:Hmaxofs.
    + destruct (lockp # b ofs) as [plock |] eqn:Hlock.
      * destruct (Hdisjoint b ofs) as [result Hunion].

        assert (Hdf : df ofs = Some result).
        {
          unfold df.
          rewrite Hmaxofs Hlock.
          rewrite Hlock in Hunion.
          exact Hunion.
        }
        pose proof
          (computeMap_1
             threadp
             (acquire_virtue_map maxp lockp threadp)
             b ofs Hdelta Hdf) as Hcompute.
        rewrite Hcompute.
        
        destruct
          (@perm_union_result
             (lockp # b ofs)
             (threadp # b ofs)
             result Hunion) as [Hresult | Hresult].
        -- rewrite Hresult.
           rewrite Hlock //.
        -- rewrite Hresult.
           exact Hthreadlt.
      * assert (Hdf : df ofs = None).
        {
          unfold df.
          rewrite Hmaxofs Hlock.
          reflexivity.
        }
        pose proof
          (computeMap_2
             threadp
             (acquire_virtue_map maxp lockp threadp)
             b ofs Hdelta Hdf) as Hcompute.
        rewrite Hcompute.
        done.
    + assert (Hdf : df ofs = None).
      {
        unfold df.
        rewrite Hmaxofs.
        reflexivity.
      }
      pose proof
        (computeMap_2
           threadp
           (acquire_virtue_map maxp lockp threadp)
           b ofs Hdelta Hdf) as Hcompute.
      rewrite Hcompute. done.
  - assert (Hdelta :
      (acquire_virtue_map maxp lockp threadp !! b)%maps = None).
    {
      unfold acquire_virtue_map.
      rewrite Maps.PTree.gmap Hmaxb.
      reflexivity.
    }
    pose proof
      (computeMap_3
         threadp
         (acquire_virtue_map maxp lockp threadp)
         b ofs Hdelta) as Hcompute.
    rewrite Hcompute //.
  Qed.

Print frag_mem_auth.
Print lock_state.
Print lock_inv.
Print coherent.
Print perm_of_rmap.
Print resource_map.resource_map_auth.

Lemma lock_inv_acquire_transfer1 
    (q : Qp) (m m_thread m_global' : mem)
    (ls : gset address)
    (σ0 σacq : rmap)
    (newThreadPerm : access_map * access_map)
    (sh : share) (b : Values.block) (o : ptrofs) (R : mpred)
    (Hload : Mem_load_unchecked Mptr m b (Ptrofs.unsigned o) = Vptrofs Ptrofs.one)
    (Hstore : m_global' = Mem_store_unchecked Mptr m b (Ptrofs.unsigned o) (Vptrofs Ptrofs.zero))
    (Hlt_acq :
       permMapLt newThreadPerm.1 (getMaxPerm m_global'))
    (Hcoh_acq :
       coherent (restrPermMap Hlt_acq) σacq)
    (Heq_acq :
       mem_equiv.access_map_equiv
         (perm_of_rmap σacq)
         (getCurPerm (restrPermMap Hlt_acq)))
    (Hsigma :
      frag_mem_auth q m_thread σ0 ∗
        LKspec LKSIZE sh (b, Ptrofs.unsigned o) ∗ ▷ R
        ⊢ |==>
        frag_mem_auth q (restrPermMap Hlt_acq) σacq ∗
        LKspec LKSIZE sh (b, Ptrofs.unsigned o) ∗ ▷ R):
  frag_mem_auth q m_thread σ0 -∗
  lock_state m ls -∗
  lock_inv sh (Vptr b o) R ==∗
  ∃ (σ : rmap)
    (Hlt : permMapLt newThreadPerm.1 (getMaxPerm m_global')),
    frag_mem_auth q (restrPermMap Hlt) σ ∗
    lock_state m_global' ls ∗
    lock_inv sh (Vptr b o) R ∗ ▷ R.
Proof.
  rewrite /lock_state /lock_inv.
  iIntros
    "Hfrag
   (%I & (%Hdom & %Hldisj) & HI & HRs)
   (%lk & %Haddr & Hlk & Hi)".

  rewrite /val2adr in Haddr.
  rewrite Haddr.

  iDestruct (own_valid_2 with "HI Hi") as "#Heq".
  rewrite gmap_view_both_validI bi.and_elim_r
          lookup_fmap option_equivI.

  destruct
    (invariant_unfold <$> I !! (b, Ptrofs.unsigned o))
    as [Q |] eqn:Hlookup;
    simpl.
  2: {
    by rewrite /invariant_unfold Hlookup.
  }

  rewrite Hlookup later_equivI.
  apply fmap_Some in Hlookup as (R0 & HIR0 & HQ).
  subst Q.

  rewrite
    (big_sepM_delete _ _ (b, Ptrofs.unsigned o));
    last exact HIR0.

  iDestruct "HRs" as "([HR | %Hload0] & HRs)".

  - iDestruct "HR" as "(_ & HR)".

    (* The invariant registered at the lock is R. *)
    iAssert (▷ R)%I with "[Heq HR]" as "HR".
    {
      iNext. iRewrite -"Heq".
      rewrite /invariant_unfold. done.
    }

    (* Perform the lower-level lock/rmap transition. *)
    iAssert
      (|==>
         frag_mem_auth q (restrPermMap Hlt_acq) σacq ∗
         LKspec LKSIZE sh (b, Ptrofs.unsigned o) ∗ ▷ R)%I
      with "[Hfrag Hlk HR]" as "Hupd".
    {
      iApply Hsigma.
      iFrame.
    }
    iMod "Hupd" as "(Hfrag & Hlk & HR)".
    iModIntro.
    iExists σacq, Hlt_acq.
    iFrame "Hfrag HR".
    iSplitL "HI HRs".
    + iExists I.
      iSplit.
      { iPureIntro. split; auto. }
      iSplitL "HI"; iFrame.
      set (lk0 := (b, Ptrofs.unsigned o)).
      rewrite -(insert_delete I lk0 R0); last exact HIR0.
      iApply big_sepM_insert.
      { apply lookup_delete. }
      iSplitR.
      * iRight.
        subst lk0.
        iPureIntro.
        rewrite Hstore /semax_conc_pred.Mem_load_unchecked /Mem_store_unchecked /= /Mem_store_unchecked_contents.
        rewrite Maps.PMap.gss -(encode_val_length Mptr (Vptrofs Ptrofs.zero)) Mem.getN_setN_same //.
      * rewrite delete_insert_delete delete_idemp.
        iApply (big_sepM_mono with "HRs").
        iIntros ((b1 & o1) y Hky) "Hk".
        rewrite lookup_delete_Some in Hky.
        destruct Hky as [Hlk_ne HkI].
        assert (Hin : (b1, o1) ∈ ls /\ (b, Ptrofs.unsigned o) ∈ ls).
        { rewrite <-Hdom. split; eapply elem_of_dom_2; eauto. }
        destruct Hin as [Hin1 Hin2].
        rewrite /lk0 in Hlk_ne.
        apply not_eq_sym in Hlk_ne.
        assert (Hsame : Mem_load_unchecked Mptr m_global' b1 o1 = Mem_load_unchecked Mptr m b1 o1).
        {
          rewrite Hstore.
          eapply Mem_load_unchecked_store_unchecked_lock_addresses_disjoint; eauto.
        }
        iDestruct "Hk" as "[[%Hkload Hy] | %Hkload]".
        ** iLeft.
           iFrame "Hy".
           iPureIntro.
           simpl.
           rewrite /semax_conc_pred.Mem_load_unchecked.
           rewrite /Mem_load_unchecked in Hsame.
           rewrite Hsame.
           done.
        ** iRight.
           iPureIntro.
           rewrite /semax_conc_pred.Mem_load_unchecked.
           rewrite /Mem_load_unchecked in Hsame.
           rewrite Hsame //.
    + iExists (b, Ptrofs.unsigned o).
      iSplit; auto.
  - rewrite /semax_conc_pred.Mem_load_unchecked /Mem_load_unchecked in Hload0, Hload.
    by rewrite Hload0 in Hload.
Qed.


Lemma lock_inv_acquire_transfer (q : Qp) (m m_thread m_global' : mem)
  (ls : gset address) (σ0 : rmap) (newThreadPerm : access_map * access_map) (sh : share)
  (l : val) (R : mpred) :
  frag_mem_auth q m_thread σ0 -∗
  lock_state m ls -∗ lock_inv sh l R ==∗
  ∃ (σacq : rmap) (Hlt_acq : permMapLt newThreadPerm.1 (getMaxPerm m_global')),
  frag_mem_auth q (restrPermMap Hlt_acq) σacq ∗
    lock_state m_global' ls ∗ lock_inv sh l R ∗ ▷ R.
Proof.
Admitted.

Definition no_VAL_range (σ : rmap) (l : address) : Prop :=
  ∀ z,
    (0 <= z < size_chunk_nat Mptr)%Z ->
    ∀ v,
      (σ @ (l.1, (l.2 + z)%Z)).2 <> Some (VAL v).

Lemma frag_mem_auth_acquire
  (q : Qp)
  (m m_thread m_global' : mem)
  (σ0 : rmap)
  (newThreadPerm : access_map * access_map)
  (sh : share) (b : Values.block) (o : ptrofs)
  (Hstore :
    m_global' =
      Mem_store_unchecked Mptr m b (Ptrofs.unsigned o)
        (Vptrofs Ptrofs.zero))
  (Hlt_acq :
    permMapLt newThreadPerm.1 (getMaxPerm m_global')) :
  frag_mem_auth q m_thread σ0 -∗
                                 LKspec LKSIZE sh (b, Ptrofs.unsigned o) ==∗
                                                                             ∃ σacq : rmap,
                                                                               frag_mem_auth q (restrPermMap Hlt_acq) σacq ∗
                                                                                 LKspec LKSIZE sh (b, Ptrofs.unsigned o).
Proof.
Admitted.

Lemma lock_inv_acquire_transfer2
  (q : Qp) (m m_thread m_global' : mem)
  (ls : gset address) (σ0 : rmap)
  (newThreadPerm : access_map * access_map)
  (sh : share) (b : Values.block) (o : ptrofs) (R : mpred)
  (Hload :
    Mem_load_unchecked Mptr m b (Ptrofs.unsigned o) =
      Vptrofs Ptrofs.one)
  (Hstore :
    m_global' =
      Mem_store_unchecked Mptr m b (Ptrofs.unsigned o)
        (Vptrofs Ptrofs.zero))
  (Hlt_acq :
    permMapLt newThreadPerm.1 (getMaxPerm m_global')) :
  frag_mem_auth q m_thread σ0 -∗
                                 lock_state m ls -∗
                                                    lock_inv sh (Vptr b o) R ==∗
                                                                                 ∃ σacq : rmap,
                                                                                   frag_mem_auth q (restrPermMap Hlt_acq) σacq ∗
                                                                                     lock_state m_global' ls ∗
                                                                                     lock_inv sh (Vptr b o) R ∗ ▷ R.
Proof.
  rewrite /lock_state /lock_inv.
  iIntros
    "Hfrag
   (%I & (%Hdom & %Hldisj) & HI & HRs)
   (%lk & %Haddr & Hlk & Hi)".

  rewrite /val2adr in Haddr.
  rewrite Haddr.

  iDestruct (own_valid_2 with "HI Hi") as "#Heq".
  rewrite gmap_view_both_validI bi.and_elim_r
          lookup_fmap option_equivI.

  destruct
    (invariant_unfold <$> I !! (b, Ptrofs.unsigned o))
    as [Q |] eqn:Hlookup;
    simpl.
  2: {
    by rewrite /invariant_unfold Hlookup.
  }

  rewrite Hlookup later_equivI.
  apply fmap_Some in Hlookup as (R0 & HIR0 & HQ).
  subst Q.

  rewrite
    (big_sepM_delete _ _ (b, Ptrofs.unsigned o));
    last exact HIR0.

  iDestruct "HRs" as "([HR | %Hload0] & HRs)".

  - iDestruct "HR" as "(_ & HR)".

    (* The invariant registered at the lock is R. *)
    iAssert (▷ R)%I with "[Heq HR]" as "HR".
    {
      iNext. iRewrite -"Heq".
      rewrite /invariant_unfold. done.
    }
    
    (* Perform the lower-level lock/rmap transition. *)
    iMod
      (frag_mem_auth_acquire
         q m m_thread m_global' σ0 newThreadPerm sh b o
         Hstore Hlt_acq with "Hfrag Hlk")
      as (σacq) "(Hfrag & Hlk)".
    iModIntro.
    iExists σacq.
    iFrame "Hfrag HR".
    iSplitL "HI HRs".
    + iExists I.
      iSplit.
      { iPureIntro. split; auto. }
      iSplitL "HI"; iFrame.
      set (lk0 := (b, Ptrofs.unsigned o)).
      rewrite -(insert_delete I lk0 R0); last exact HIR0.
      iApply big_sepM_insert.
      { apply lookup_delete. }
      iSplitR.
      * iRight.
        subst lk0.
        iPureIntro.
        rewrite Hstore /semax_conc_pred.Mem_load_unchecked /Mem_store_unchecked /= /Mem_store_unchecked_contents.
        rewrite Maps.PMap.gss -(encode_val_length Mptr (Vptrofs Ptrofs.zero)) Mem.getN_setN_same //.
      * rewrite delete_insert_delete delete_idemp.
        iApply (big_sepM_mono with "HRs").
        iIntros ((b1 & o1) y Hky) "Hk".
        rewrite lookup_delete_Some in Hky.
        destruct Hky as [Hlk_ne HkI].
        assert (Hin : (b1, o1) ∈ ls /\ (b, Ptrofs.unsigned o) ∈ ls).
        { rewrite <-Hdom. split; eapply elem_of_dom_2; eauto. }
        destruct Hin as [Hin1 Hin2].
        rewrite /lk0 in Hlk_ne.
        apply not_eq_sym in Hlk_ne.
        assert (Hsame : Mem_load_unchecked Mptr m_global' b1 o1 = Mem_load_unchecked Mptr m b1 o1).
        {
          rewrite Hstore.
          eapply Mem_load_unchecked_store_unchecked_lock_addresses_disjoint; eauto.
        }
        iDestruct "Hk" as "[[%Hkload Hy] | %Hkload]".
        ** iLeft.
           iFrame "Hy".
           iPureIntro.
           simpl.
           rewrite /semax_conc_pred.Mem_load_unchecked.
           rewrite /Mem_load_unchecked in Hsame.
           rewrite Hsame.
           done.
        ** iRight.
           iPureIntro.
           rewrite /semax_conc_pred.Mem_load_unchecked.
           rewrite /Mem_load_unchecked in Hsame.
           rewrite Hsame //.
    + iExists (b, Ptrofs.unsigned o).
      iSplit; auto.
  - rewrite /semax_conc_pred.Mem_load_unchecked /Mem_load_unchecked in Hload0, Hload.
    by rewrite Hload0 in Hload.
  Qed.

  Definition other_threads_safe (tp : dtp) (qs : gmap nat Qp) (m : mem) (i : nat) :=
    ∀ (Ψ : nat → nat → iPropI Σ),
      □ (∀ (k y : nat),
            ⌜seq 0 (pos.n (OrdinalPool.num_threads tp)) !! k = Some y⌝ → ⌜k ≠ i⌝ →
       (∃ (q0 : Qp) (σ : rmap) (cnti0 : containsThread tp y) 
          (Hlt1 : permMapLt (perm_of_rmap σ) (getMaxPerm m)),
           ⌜qs !! y = Some q0 ∧ mem_equiv.access_map_equiv (perm_of_rmap σ) (getThreadR cnti0).1⌝ ∗
              thread_safe tp y q0 ∗ frag_mem_auth q0 (restrPermMap Hlt1) σ) -∗ Ψ k y) -∗
               Ψ i i -∗ [∗ list] k↦y ∈ seq 0 (pos.n (OrdinalPool.num_threads tp)), Ψ k y.
  
  Definition post_safe (q : Qp) (x : Jext_spec_type (concurrent_ext_spec CS ext_link) LOCK)
    (argsty : typelist) (retty : type) (cc : calling_convention) (args : list val) (k : cont) :=
    ∀ (ret : option val) (m' : mem) (σ' : rmap) (z' : unit),
      ⌜Val.has_type_list args (sig_args (ef_sig LOCK)) ∧
        Builtins0.val_opt_has_rettype ret (sig_res (ef_sig LOCK))⌝ →
      |={⊤}=>
      frag_state_interp q m' σ' z' -∗
       Jext_spec_post (concurrent_ext_spec CS ext_link) LOCK x (genv_symb_injective ge)
         (sig_res (ef_sig LOCK)) ret -∗
          ∃ (c' : CC_core) (σ2 : rmap),
              ⌜after_external (cl_core_sem ge) ret
                  (Callstate (Ctypes.External LOCK argsty retty cc) args k) m' = Some c'⌝ ∧
                      frag_state_interp q m' σ2 z' ∗ jsafe_frag q ⊤ z' c'.

  Lemma acquire_safe (tp : dtp) (m : mem) (ls : gset address)
    (qs : gmap nat Qp) (i : nat) (q : Qp) (σ1 σ0 : rmap)
    (Htp_wf : threads_wellformed tp) (Hinvariant : invariant tp)
    (Hcompat : mem_compatible tp m) (Hlocks : locks_coherent tp m ls)
    (cnti : containsThread tp i) (Hlt : permMapLt (perm_of_rmap σ1) (getMaxPerm m))
    (Hq : qs !! i = Some q)
    (Heq1 : mem_equiv.access_map_equiv (perm_of_rmap σ1) (getThreadR cnti).1)
    (argsty : typelist) (retty : type) (cc : calling_convention) (k : cont) (args : list val)
    (Hi : getThreadC cnti = Kblocked (Callstate (Ctypes.External LOCK argsty retty cc) args k))
    (Hcoh : coherent (restrPermMap Hlt) σ1)
    (Hlt0 : permMapLt (perm_of_rmap σ1) (getMaxPerm (restrPermMap Hlt)))
    (x : Jext_spec_type (concurrent_ext_spec CS ext_link) LOCK) :
  ⊢ other_threads_safe tp qs m i -∗
    Jext_spec_pre (concurrent_ext_spec CS ext_link) LOCK x (genv_symb_injective ge) (sig_args (ef_sig LOCK)) args -∗
    ▷ post_safe q x argsty retty cc args k -∗ lock_state m ls -∗ frag_state_interp q (restrPermMap Hlt) σ0 () -∗
    |={⊤}[∅]▷=>
      ∃ (tp' : t) (m' : mem) (ev : Events.sync_event),
        ⌜threads_wellformed tp' ∧ invariant tp' ∧ mem_compatible tp' m' ∧
          locks_coherent tp' m' ls ∧ syncStep true cnti Hcompat tp' m' ev⌝ ∧
          ext_auth () ∗ threads_safe tp' qs m' ∗ lock_state m' ls.
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
    - Check lock_inv_acquire _ m ls σ0.

      set (virtueCur := acquire_virtue_map (getMaxPerm m) l0.1 (getThreadR cnti).1).
      set (virtueMax := acquire_virtue_map (getMaxPerm m) l0.2 (getThreadR cnti).2).
      set (virtueThread := (virtueCur, virtueMax)).
      set (newThreadPerm :=
             (computeMap (getThreadR cnti).1 virtueCur, computeMap (getThreadR cnti).2 virtueMax)).
      set (l1' := (l1.1, Ptrofs.intval (Ptrofs.repr l1.2))).
      set (tp' :=
             updLockSet (updThread cnti (Kresume c Vundef) newThreadPerm) l1' (empty_map, empty_map)).
      
      set (ret := (None : option val)).
      set (m_global' :=
             Mem_store_unchecked Mptr m
               l1.1
               (Ptrofs.intval (Ptrofs.repr l1.2))
               (Vptrofs Ptrofs.zero)).
      assert (Hofs' : Ptrofs.unsigned (Ptrofs.repr l1.2) = l1.2).
      { by change (Ptrofs.Z_mod_modulus l1.2 = l1.2). }
      assert (Hload' : Mem_load_unchecked Mptr m l1.1 (Ptrofs.unsigned (Ptrofs.repr l1.2)) =
                 Vptrofs Ptrofs.one).
      { rewrite Hofs' //. }
      assert (Hstore' : m_global' = Mem_store_unchecked Mptr m l1.1 (Ptrofs.unsigned (Ptrofs.repr l1.2)) (Vptrofs Ptrofs.zero)).
      { done. }

      assert (Hlt_acq :
               permMapLt newThreadPerm.1 (getMaxPerm m_global')).
      {
        unfold newThreadPerm, virtueCur.
        unfold m_global'.

        (* The unchecked store changes contents, not max permissions. *)
        change
          (permMapLt
             (computeMap (getThreadR cnti).1
                (acquire_virtue_map
                   (getMaxPerm m) l0.1 (getThreadR cnti).1))
             (getMaxPerm m)).
        apply acquire_virtue_map_lt. admit. admit. admit. admit. }

      rewrite Hl1.
      iMod (lock_inv_acquire_transfer2 q m (restrPermMap Hlt) m_global' ls σ0 newThreadPerm
              sh l1.1 (Ptrofs.repr l1.2) R Hload' Hstore' Hlt_acq with "Hths Hls Hl") as (σacq) "(Hfrag_acq & Hls_store & Hl & HR)".
      Check lock_inv_acquire_transfer2 q m (restrPermMap Hlt) m_global' ls σ0 newThreadPerm
        sh l1.1 (Ptrofs.repr l1.2) R Hload' Hstore'.
      (*
      iMod (lock_inv_acquire_transfer q m (restrPermMap Hlt) m_global' ls σ0 newThreadPerm sh l R
          with "Hths Hls Hl") as (σacq Hlt_acq) "(Hfrag_acq & Hls_store & Hl & HR)". *)
      
      set (m_thread' := restrPermMap Hlt_acq).
      iAssert (frag_state_interp q m_thread' σacq ()) with "[Hfrag_acq Hext]" as "Hstate".
      { rewrite /frag_state_interp. iFrame. }
      iAssert (∃ (c' : CC_core) (σ2 : rmap),
           ⌜after_external (cl_core_sem ge) ret (Callstate (Ctypes.External LOCK argsty retty cc) [l] k) m_thread' = Some c'⌝ ∧ frag_state_interp q m_thread' σ2 () ∗ jsafe_frag q ⊤ () c')%I
        with "[Hpost Hstate HR]" as "HafterPost".
      {
        admit.
      }
      iDestruct "HafterPost" as (c' σ2) "(%Hafter & Hfrag & Hjsafe)".
      iDestruct "Hfrag" as "(((%Hcoh2 & %Heq2) & Hauth2) & Hext2)".
      assert (Heq2_new: mem_equiv.access_map_equiv (perm_of_rmap σ2) newThreadPerm.1).
      { etransitivity; try apply Heq2. apply mem_equiv.getCur_restr. }
      pose proof Hcoh2 as Hcoh2'.
      apply coherent_restrPermMap_of_coherent in Hcoh2'.
      destruct Hcoh2' as (Hlt2 & Hcoh2').
      iAssert (frag_mem_auth q (restrPermMap Hlt2) σ2) with "[Hauth2]" as "Hfrag2".
      {
        rewrite /frag_mem_auth.
        iFrame.
        iPureIntro.
        do 2 split; auto.
        unfold mem_equiv.access_map_equiv.
        intros b.
        symmetry.
        apply mem_equiv.getCur_restr.
      }
      assert (cnti' : containsThread tp' i).
      { subst tp'; auto. }
      iAssert (thread_safe tp' i q)
        with "[Hjsafe]" as "HcurSafe".
      { rewrite /thread_safe; subst tp'; simpl.
        iExists cnti'.
        assert (Hcnt : cnti' = cnti) by apply proof_irrelevance.
        rewrite Hcnt.
        rewrite eqtype.eq_refl.
        iIntros (c'0) "%Hafter0".
        change (cl_after_external None c = Some c') in Hafter.
        assert (c'0 = c') by congruence.
        subst c'0. iFrame. }      

      set (Ψ := fun (_ y : nat) =>
                  (∃ (q0 : Qp)
                     (σ : rmap)
                     (cnty : containsThread tp' y)
                     (Hlt0 :
                       permMapLt
                         (perm_of_rmap σ)
                         (getMaxPerm m_global')),
                      ⌜qs !! y = Some q0
                      ∧ mem_equiv.access_map_equiv
                          (perm_of_rmap σ)
                          (getThreadR cnty).1⌝
                          ∗ thread_safe tp' y q0
                          ∗ frag_mem_auth q0
                          (restrPermMap Hlt0)
                          σ)%I).
      iAssert
        (∃ Hlt2g :
            permMapLt
              (perm_of_rmap σ2)
              (getMaxPerm m_global'),
            frag_mem_auth q (restrPermMap Hlt2g) σ2)%I
        with "[Hfrag2]" as "Hfrag2g".
      {
        assert (Hlt2g : permMapLt (perm_of_rmap σ2) (getMaxPerm m_global')).
        {
          unfold m_thread' in Hlt2.
          unfold permMapLt in *.
          intros b ofs.
          pose proof Hlt2 as Hlt2'.
          specialize (Hlt2' b ofs).
          unfold m_thread' in Hlt2'.
          rewrite (mem_equiv.getMax_restr newThreadPerm.1 m_global' Hlt_acq b) // in Hlt2'. }
        iExists Hlt2g.
        rewrite /frag_mem_auth.
        iDestruct "Hfrag2" as "((%HcohR & %HeqR) & HauthR)".
        iFrame.
        iPureIntro.
        do 2 split; auto.
        - pose proof
            (@mem_equiv.restrPermMap_idempotent
               newThreadPerm.1
               (perm_of_rmap σ2)
               m_global'
               Hlt_acq
               Hlt2g
               Hlt2) as Hmem. admit.
        - unfold mem_equiv.access_map_equiv.
          intros b.
          symmetry.
          apply mem_equiv.getCur_restr.
      }
      iDestruct "Hfrag2g" as (Hlt2g) "Hfrag2g".
      iAssert (Ψ i i)
        with "[HcurSafe Hfrag2g]" as "Hii".
      {
        rewrite /Ψ.
        iExists q, σ2, cnti', Hlt2g.
        iFrame.
        iPureIntro.
        split.
        - exact Hq.
        - subst tp'.
          assert (Hcnt : cnti' = cnti) by apply proof_irrelevance.
          rewrite Hcnt.
          simpl.
          rewrite eqtype.eq_refl.
          exact Heq2_new.
      }
      iSpecialize ("Hsafe" $! Ψ).
      
      iAssert
        ([∗ list] k0 ↦ y ∈
           seq 0 (pos.n (OrdinalPool.num_threads tp)),
          Ψ k0 y)%I with "[Hsafe Hii]" as "HallSafe".
      {
        iApply ("Hsafe" with "[] Hii").
        iModIntro.
        iIntros (k0 y Hlookup Hneq) "Hy".
        iDestruct "Hy" as
          (q0 σ cnty Hlt1)
            "((%Hqy & %Heqy) & HsafeY & HfragY)".
        
        apply lookup_seq in Hlookup as [Hy _].
        simpl in Hy.
        subst k0.
        iAssert (∃ Hlt1g : permMapLt (perm_of_rmap σ) (getMaxPerm m_global'),
              frag_mem_auth q0 (restrPermMap Hlt1g) σ)%I
          with "[HfragY]" as "HfragYg".
        {
          Print lock_state.
          Print frag_mem_auth.
          Print coherent.
          Print access_cohere .
          Print nonEmptyRangeCur.
          Print contents_cohere.
          Print perm_of_res.

          admit. }
        iDestruct "HfragYg" as (Hlt1g) "HfragYg".

        assert (cnty' : containsThread tp' y).
        { subst tp'; simpl. done. }

        assert (HC : getThreadC cnty' = getThreadC cnty).
        { subst tp'; simpl.
          destruct (eqtype.eq_op _ _) eqn:Heq.
          - admit.
          - admit.
        }

        assert (HR : getThreadR cnty' = getThreadR cnty).
        {
          subst tp'.
          simpl.
          destruct (eqtype.eq_op _ _) eqn:Heq.
          - admit.
          - admit.
        }

        rewrite /Ψ.
        iExists q0, σ, cnty', Hlt1g.
        
        iSplit.
        - iPureIntro.
          split.
          + exact Hqy.
          + rewrite HR.
            exact Heqy.
            
        - iSplitL "HsafeY".
          + iDestruct "HsafeY" as (cnty0) "HsafeY".
            assert (Hcnty0 : cnty0 = cnty) by apply proof_irrelevance.
            subst cnty0.
            iExists cnty'.
            rewrite HC. iExact "HsafeY".
          + iExact "HfragYg".
      }
      iAssert (threads_safe tp' qs m_global') with "[HallSafe]" as "Hthreads".
      {
        rewrite /threads_safe.
        assert (Hnum : pos.n (OrdinalPool.num_threads tp') = pos.n (OrdinalPool.num_threads tp)).
        { unfold tp'; auto. }
        rewrite Hnum.
        iExact "HallSafe".
      }
      iExists tp', m_global', _.
      iFrame.
      
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
          (tp' := updThread cnti (Kresume c Vundef) newThreadPerm) (pmap := l0)
          (virtueThread := virtueThread); try done.
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


      (*
      iAssert (threads_safe tp' qs m') with "[Hsafe]" as "?".
      { iApply "Hsafe".
      
      rewrite /threads_safe.

      iAssert (∃ (c' : CC_core) (σ2 : rmap),
                  ⌜after_external (cl_core_sem ge) ret
                    (Callstate (Ctypes.External LOCK argsty retty cc) [l] k) m'0 = 
                    Some c'⌝ ∧ frag_state_interp q m'0 σ2 z' ∗ jsafe_frag q ⊤ z' c') as "Hpost1".



      iAssert (▷  ∀ (ret : option val) (m'0 : mem) (σ' : rmap) (z' : ()),
                   ⌜Val.has_type_list [l] (sig_args (ef_sig LOCK))
                   ∧ Builtins0.val_opt_has_rettype ret (sig_res (ef_sig LOCK))⌝
                   → |={⊤}=>
                 frag_state_interp q m'0 σ' z' -∗
                                                  match acquire_spec with
                                                  | mk_funspec _ _ A _ _ Q =>
                                                      ∃ x'' : dtfr A,
                 ⌜JMeq.JMeq x x''⌝
                 ∧ funspec2post' A Q x'' (genv_symb_injective ge) (sig_res (ef_sig LOCK)) ret

               end )%I with "[]" as "Hpost1".
      {
        iNext.
        iIntros (ret m1 z1) "%Hty %Hv".
        iIntros "!> Hfrag". 
        unfold acquire_spec.
        simpl.
        iExists (l, sh, R).
        iSplit; auto.
        destruct z1.
        rewrite /PROPx /PARAMSx /GLOBALSx /LOCALx /SEPx /=.
        iSplit; auto.
        iFrame.
        







      
      { rewrite /frag_state_interp.
        rewrite /threads_safe.
      Locate "|={".
      Search fupd.
      apply fupd_intro.
*)
        
  Admitted.
    
  
End conc_heap.

Existing Instance HybridMachine.DryHybridMachine.DryHybridMachineSig.

Theorem dry_safety `{!VSTGpreS unit Σ} `{!inG Σ (gmap_view.gmap_viewR address unitR)}
  `{!inG Σ (gmap_view.gmap_viewR address (laterO (iPropO Σ)))} sch n :
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
       eexists. eexists. split; first done; split; first apply Hinit; done. }
  clear Hinit Hsafe.
  rewrite bi.and_elim_l.
  set (tp := initial_machine _ _).
  assert (invariant tp) as Hinvariant by apply ThreadPoolWF.initial_invariant0.
  assert (HybridMachineSig.mem_compatible tp (`init_mem)) as Hcompat
        by apply ThreadPoolWF.initial_mem_compatible.
  assert (threads_wellformed tp) as Htp_wf by done.
  iPoseProof (state_interp_with_rmap_to_frag with "S") as "S".
  set qs := (<[0 := 1%Qp]> (∅ : gmap nat Qp)).
  rewrite /frag_state_interp.
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
    - iSplit; auto; iPureIntro.
      apply coherent_restrPermMap with (Hlt := Hlt) in Hcoh.
      split; auto.
      apply coherent_access_map_equiv; auto. }
  assert (locks_coherent tp (`init_mem) ∅) as Hlocks by done.
  clear Hcoh_empty.
  iAssert (lock_state (`init_mem) ∅) with "[locks]" as "locks".
  { iApply (lock_state_empty_change with "locks"). }
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
      iApply ("IH" $! U'' tr tp m n ls qs with "[] [] [] [] Hext Hsafe locks"); try done. }
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
        iApply ("IH" $! _ _ _ _ _ _ with "[] [] [] [] Hext Hsafe locks "); try done.
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
                 with "[%] [%] [%] [%] Hext [Hsafe Hfragi Hsafei] locks "); try done.
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
            * iPureIntro; split; auto; rewrite gThreadCR //.
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
      assert (Hmem : restrPermMap (ssrfun.pair_of_and (Hcompat i cnti)).1 = restrPermMap Hlt).
      { erewrite restrPermMap_ext; eauto. }
      assert (corestep (cl_core_sem ge) s
                  (restrPermMap (ssrfun.pair_of_and (Hcompat i cnti)).1) c' m') as Hstep'.
      { rewrite Hmem //. }
      iApply step_fupd_intro; first done; iNext.
      apply (ev_step_ax2 (Clight_evsem.CLC_evsem ge)) in Hstep' as (? & Hstep').
      assert (Hmemstep : mem_step (restrPermMap Hlt) m').
      { eapply (CLC_corestep_mem _ _ (restrPermMap Hlt)); eauto. }
      assert (mem_compatible (updThread cnti (Krun c') (getCurPerm m', (getThreadR cnti).2)) m')
          as Hcompat' by by eapply (CoreLanguageDry.corestep_compatible(Sem := Sem)).
      assert (Hlock_loads : forall l0, l0 ∈ ls ->
                 Mem_load_unchecked Mptr m l0.1 l0.2 = Mem_load_unchecked Mptr m' l0.1 l0.2).
      {
        intros l0 Hl0.
        pose proof (Hlocks l0 Hl0) as Hlock0.
        destruct Hlock0 as (_ & _ & Hne).
        specialize (Hne i cnti (ssrfun.pair_of_and (Hcompat i cnti)).1).
        rewrite Hmem in Hne.
        rewrite <- (Mem_unchecked_restrPermMap m (perm_of_rmap σ1) Hlt l0).
        unfold Mem_load_unchecked.
        f_equal.
        eapply mem_step_preserves_lock_bytes; eauto.
      }
      iAssert (lock_state m' ls) with "[locks]" as "locks".
      { iApply (lock_state_mem_change m m' ls Hlock_loads with "locks"). }
      iDestruct "S" as "(Hfragi & Hext)".
      iSpecialize ("IH" $! _ _ (updThread cnti (Krun c')
                                    (getCurPerm m', (getThreadR cnti).2)) m' n ls qs
                    with "[%] [%] [%] [%] Hext [Hsafe Hsafei Hfragi] locks"); try done.
      * (* threads_wellformed *)
        intros j cntj.
        destruct (eq_dec j i); first by subst; rewrite gssThreadCode.
        pose proof (cntUpdate' _ _ cnti cntj).
        rewrite gsoThreadCode //; apply Htp_wf.
      * (* invariant *)
        eapply (CoreLanguageDry.corestep_invariant(Sem := Sem)); try done.
      * (* locks_coherent *)
        rewrite /locks_coherent in Hlocks |- *.
        intros.
        destruct (Hlocks l0 H0) as (HlockRes & Hload & HnonEmpty).
        rewrite !gsoThreadLPool.
        have Hne : nonEmptyRangeCur (restrPermMap Hlt) l0.
        { have Hne' := HnonEmpty i cnti (ssrfun.pair_of_and (Hcompat i cnti)).1.
            by rewrite Hmem in Hne'.
        }
        have Hbytes := mem_step_preserves_lock_bytes (restrPermMap Hlt) m' l0 Hmemstep Hne.
        split; first exact HlockRes.
        split.
        ** destruct Hload as [(Hload_zero & Hl) | Hload_one].
           ++ left; split; auto.
              rewrite -Hload_zero /Mem_load_unchecked -Hbytes.
              apply Mem_unchecked_restrPermMap.
           ++ right.
              have Hload_one' :
                  Mem_load_unchecked Mptr (restrPermMap Hlt) l0.1 l0.2 =
                    Vptrofs Ptrofs.one.
              { rewrite Mem_unchecked_restrPermMap //. }
              unfold Mem_load_unchecked in *.
              rewrite - Hbytes //.
       ** rewrite /nonEmptyRangeCur.
          intros.
          rewrite restrPermMap_Cur_eq.
          destruct (Nat.eq_dec i i0) as [-> | Hneq].
          ++ rewrite (gssThreadRes cnti (Krun c')
                           (getCurPerm m', (getThreadR cnti).2) cnti0) /=.
             rewrite /getCurPerm PMap.gmap /=.
             eapply mem_step_preserves_nonempty_range; auto. done.
          ++ assert (cnti_old : containsThread tp i0); try done.
             have -> : getThreadR cnti0 = getThreadR cnti_old by apply gsoThreadRes.
             have Hne_old := HnonEmpty i0 cnti_old (ssrfun.pair_of_and (Hcompat i0 cnti_old)).1.
             rewrite /nonEmptyRangeCur in Hne_old.
             specialize (Hne_old i1 H1).
             rewrite restrPermMap_Cur_eq // in Hne_old.
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
                subst cnty'; erewrite gsoThreadRes; eauto.
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
                  threads_safe tp' qs m' ∗ lock_state m' ls )
        with "[Hpost Hsafe locks Hpre S]" as "Hsafe".
      2 : {
        iMod "Hsafe".
        iIntros "!> !>".
        iMod "Hsafe" as (??? (? & ? & ? & ? & ?)) "(Hext & Hth & locks)".
        iAssert (|={⊤}[∅]▷=>^n ∀ U'', ⌜HybridMachineSig.HybridCoarseMachine.csafe (U'', tr ++ [Events.external i ev], tp') m' n⌝) with "[-]" as "H".
        { rewrite step_fupdN_plain_forall //.
          iIntros.
          iApply ("IH" $! x0 (tr ++ [Events.external i ev]) tp' m' n ls qs
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
      destruct (Hlocks l1 H1) as (HlockRes & Hload & HnonEmpty).
      split; auto.
    + iApply "Hsafe".
      * iIntros "!>" (?? (-> & ?)%lookup_seq ?)
            "(%q0 & %σ0 & (%cnty & %Hltσ0 & (%Hqs & %Hqy) & Hsafe_y & Hfrag_y))".
        assert (Hik : i <> 0 + k) by lia.
        pose (cnty' := OrdinalPool.cntUpdateC (Krun (Returnstate Vundef c)) cnti cnty).
        pose proof (@OrdinalPool.gThreadCR _ _ i (0 + k) tp cnti cnty
                        (Krun (Returnstate Vundef c)) cnty') as HR.
        iExists q0, σ0, cnty', Hltσ0.
        iSplit; auto.
        ** iPureIntro.
           split; eauto.
           pose proof (f_equal (fun r => r.1) HR) as HR1; rewrite HR1 //.
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
        split; auto.
        have -> : (getThreadR cnti').1 = (getThreadR cnti).1; try done.
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
    set (m' := restrPermMap (ssrfun.pair_of_and (Hcompat i cnti)).1).
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
      destruct (Hlocks l0 H1) as (HlockRes & Hload & HnonEmpty).
      repeat split; auto.
      unfold nonEmptyRangeCur in *.
      intros.
      subst tp'.
      rewrite restrPermMap_Cur_eq.
      destruct (Nat.eq_dec i i0) as [-> | Hneq].
      * rewrite (gssThreadRes cnti (Krun q_new)
                     (HybridMachineSig.add_block Hcompat cnti m') cnti0).
        rewrite /HybridMachineSig.add_block /= /m' /getCurPerm PMap.gmap /=.
        apply (HnonEmpty i0 cnti (ssrfun.pair_of_and (Hcompat i0 cnti)).1 i1 H2).
      * assert (cnti_old : containsThread tp i0); try done.
        have -> : (getThreadR cnti0).1 = (getThreadR cnti_old).1.
        { f_equal; rewrite gsoThreadRes //. }
        pose proof (HnonEmpty i0 cnti_old (ssrfun.pair_of_and (Hcompat i0 cnti_old)).1 i1 H2) as Hne.
        rewrite restrPermMap_Cur_eq // in Hne.
    + iApply "Hsafe".
      * iIntros "!>" (?? (-> & ?)%lookup_seq ?)
            "(%q0 & %σ0 & (%cnty & %Hltσ0 & (%Hqs & %Hqy) & Hsafe_y & Hfrag_y))".
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
           split; auto.
           rewrite gssThreadRes /HybridMachineSig.add_block /=.
           subst m'.
           pose proof (mem_equiv.getCur_restr (getThreadR cnti).1 m
                  (ssrfun.pair_of_and (Hcompat i cnti)).1) as Hcur.
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
