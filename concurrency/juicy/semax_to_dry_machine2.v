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
Require Import VST.veric.semax_call.
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

(*Added*)

Definition codeN : namespace := nroot .@ "N"%string.
Section funspec_auth_fractional.
  Context {Σ : gFunctors} `{!heapGS Σ}.

  Lemma gmap_view_both_dfrac_validI_local {K : Type} `{Countable K} {V0 : ofe}
    (dp : dfrac) (M : gmap K V0) (k : K) (dq : dfrac) (v : V0) :
    (✓ (gmap_view.gmap_view_auth dp M ⋅ gmap_view.gmap_view_frag k dq v :
         gmap_view.gmap_viewR K V0) : iProp Σ)
    ⊢ ⌜✓ dp⌝ ∧ ⌜✓ dq⌝ ∧ M !! k ≡ Some v.
  Proof.
    rewrite /gmap_view.gmap_view_auth /gmap_view.gmap_view_frag.
    apply algebra.view_both_dfrac_validI_1.
    intros n a.
    ouPred.unseal.
    apply gmap_view.gmap_view_rel_lookup.
  Qed.

  Definition funspec_auth_q (q : Qp) (M : gmap address (@funspecO' Σ)) : iProp Σ :=
    own (inG0 := funspec_inG) funspec_name (gmap_view.gmap_view_auth (dfrac.DfracOwn q) M).

  (* 	Splits fraction q into two halves: one is retained, one is consumed by spawn. *)
  Lemma funspec_auth_q_split (q : Qp) (M : gmap address (@funspecO' Σ)) :
    funspec_auth_q q M ⊣⊢ funspec_auth_q ((1/2) * q)%Qp M ∗ funspec_auth_q ((1/2) * q)%Qp M.
  Proof.
    rewrite /funspec_auth_q -own_op -gmap_view.gmap_view_auth_dfrac_op dfrac.dfrac_op_own.
    f_equiv.
    rewrite -Qp.mul_add_distr_r Qp.half_half Qp.mul_1_l //.
  Qed.
  
  (* 	Converts the original full funspec_auth M into two initial fractional copies. *)
  Lemma funspec_auth_to_two_halves (M : gmap address (@funspecO' Σ)) :
    seplog.funspec_auth M ⊣⊢ funspec_auth_q (1/2)%Qp M ∗ funspec_auth_q (1/2)%Qp M.
  Proof.
    rewrite /seplog.funspec_auth /funspec_auth_q -own_op -gmap_view.gmap_view_auth_dfrac_op
               dfrac.dfrac_op_own Qp.half_half //.
  Qed.

  (* 	Combines fractional authority with func_at fs l to prove M !! l = Some fs. *)
  Lemma funspec_auth_q_lookup (q : Qp) (M : gmap address (@funspecO' Σ))
    (l : address) (fs : funspec) :
    ⊢ funspec_auth_q q M -∗ seplog.func_at fs l -∗ ((M !! l)%stdpp ≡ Some (funspec_unfold fs)).
  Proof.
    rewrite /funspec_auth_q.
    iIntros "Hauth #Hfunc".
    rewrite /seplog.func_at /seplog.know_funspec.
    iDestruct "Hfunc" as "(_ & #Hfrag)".
    iPoseProof (own_valid_2 with "Hauth Hfrag") as "#Hvalid".
    iDestruct (gmap_view_both_dfrac_validI_local with "Hvalid") as "(_ & _ & #Hlookup)". done.
  Qed.

  (* Specializes that lookup to init_funspecs m ge G, producing matchfunspecs ge G. *)
  Lemma init_funspecs_matchfunspecs_q (ge0 : genv) (G0 : funspecs) (q : Qp) (m0 : mem) :
    funspec_auth_q q (init_funspecs m0 ge0 G0) ⊢ matchfunspecs ge0 G0.
  Proof.
    rewrite /matchfunspecs.
    iIntros "Hauth" (b fs) "#Hfunc".
    iPoseProof (funspec_auth_q_lookup q (init_funspecs m0 ge0 G0) (b, 0%Z) fs
                 with "Hauth Hfunc") as "Hlookup".
    rewrite option_equivI init_funspecs_lookup /funspec_of_loc /=.
    destruct (Pos.ltb_spec0 b (Mem.nextblock m0)); last done.
    destruct (Genv.invert_symbol ge0 b) as [id |] eqn:Hinv.
    2: { rewrite Hinv //. }
    rewrite Hinv /=.
    apply Genv.invert_find_symbol in Hinv.
    destruct (find_id id G0) as [fs0 |] eqn:Hfind; try done.
    iExists id, fs0.
    iSplit.
    - iPureIntro. split; done.
    - by iApply seplog.funspec_sub_si_ne.
  Qed.

End funspec_auth_fractional.
  

(*Added*)

Section semax_prog_with_rmap.
  Context `{!VSTGS OK_ty Σ} (OK_spec : Jext_spec Σ).

  Definition state_interp_with_rmap (m : mem) (z : OK_ty) (σ : rmap) : iProp Σ :=
    frag_mem_auth m σ ∗ ext_auth z.
  
  (*
    Before: jsafeN ... ∧ matchfunspecs ge G
    After return: jsafeN ... ∗ funspec_auth_q (1/2)%Qp (...) ∗ initial_core m ge G

    Reason: We cannot separate this into: jsafeN ... ∗ matchfunspecs ge G
    Therefore, after taking jsafeN, no independently owned matchfunspecs remains for spawn.


    In dry_safety, Hsafe : jsafeN ... ∧ matchfunspecs ge G

    It could extract jsafeN, but couldn't also retain reusable code information for spawn.
    After, it receives:
    Hsafe   : jsafeN ...
    Hfcode  : funspec_auth_q (1/2)%Qp (...)
    Hcore   : initial_core mcode ge G

   *)
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
             (jsafeN OK_spec (globalenv prog) ⊤ z q ∗
                funspec_auth_q (1/2)%Qp (init_funspecs m (globalenv prog) G) ∗
                initial_world.initial_core m (F := Clight.function) (globalenv prog) G))
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
      as "((%σ & Hσ & %Hperm) & Hm & Hcore & Hboth)";
      [done.. |].

    iDestruct (bi.and_elim_l with "Hboth") as "Hf".
    (* First half 1/2, Hfmain, is consumed to derive matchfunspecs for initial-main safety.
       Second half 1/2, Hfcode, is stored in code_bank for future spawns.
     *)
    rewrite funspec_auth_to_two_halves.
    iDestruct "Hf" as "(Hfmain & Hfcode)".
    iPoseProof (init_funspecs_matchfunspecs_q (globalenv prog) G (1/2)%Qp m with "Hfmain") as "Hmatch".
    iDestruct "Hcore" as "#Hcore".
    iModIntro.
    iExists σ.
    iSplitL "Hσ Hext".
    { rewrite /state_interp_with_rmap. iFrame. }
    iSplit; try done.
    iSplitL "Hm Hmatch Hz".
    - destruct H4 as [post [H4 H4']].
      unfold main_spec_ext' in H4'.
      injection H4' as -> HP HQ.
      apply inj_pair2 in HP as ->.
      apply inj_pair2 in HQ as ->.
      iApply (Hsafe (initialize.globals_of_genv (filter_genv (globalenv prog)))).
      iCombine "Hcore Hmatch" as "Hcore_main".
      rewrite (initial_core_funassert _ V _ _ (Map.empty _) (Map.empty _)) //.
      iFrame.
      iIntros "!>".
      iSplit; first done.
      iApply global_initializers; eauto.
    - iFrame "Hcore Hfcode".
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

  Definition raw_rmapUR : uora := resource_map.rmapUR share address (leibnizO resource).

  Definition raw_rmapR : cmra := ora_cmraR (uora_oraR raw_rmapUR).

  Definition rmap_authUR : ora := ext_order.inclR (iris.algebra.auth.authUR raw_rmapR).

Section conc_heap.
  Context `{HH: !VSTGS unit Σ} `{!lockGS Σ} `{rmap_inG : inG Σ rmap_authUR}.
  Definition rmap_auth `{rmap_inG : inG Σ rmap_authUR} (γ : gname) (σ : rmap) : iProp Σ :=
    @own Σ rmap_authUR rmap_inG γ (@auth_auth raw_rmapR (DfracOwn 1%Qp) σ).

  Definition rmap_frag `{rmap_inG : inG Σ rmap_authUR} (γ : gname) (σ : rmap) : iProp Σ :=
    @own Σ rmap_authUR rmap_inG γ (@auth_frag raw_rmapR σ).

  (* not useful
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
    rewrite -own_op -auth_auth_dfrac_op dfrac.dfrac_op_own. done.
  Qed.
  
  Lemma rmap_frag_op `{!inG Σ rmap_authUR} γ (σ1 σ2 : raw_rmapR) :
    rmap_frag γ (σ1 ⋅ σ2) ⊣⊢ rmap_frag γ σ1 ∗ rmap_frag γ σ2.
  Proof. by rewrite /rmap_frag -own_op frac_auth_frag_op. Qed.*)

  (* Each thread has a separate γi for its state_interp. *)
  Definition thread_gen_heapGS γi := GenHeapGS share address resource Σ (gen_heap_inG := gen_heap_inG) γi (gen_meta_name _).

  Definition thread_rmap (γ : gname) γi σ := rmap_frag γ σ ∗ resource_map.resource_map_auth
    (H1 := gen_heapGpreS_heap (gen_heapGpreS := gen_heap_inG)) γi 1%Qp σ.

  Definition thread_mem_auth γ γi m σ := ⌜coherent m σ⌝ ∧ thread_rmap γ γi σ.

  Definition conc_state_interp γ σ z := rmap_auth γ σ ∗ ext_auth z.

  (*
    Global invariant ignores Cur:  glob_coherent m σ0 :=
        ∃ Hlt : permMapLt (perm_of_rmap σ0) (getMaxPerm m), coherent (restrPermMap Hlt) σ0
      It only depends on contents / Max / nextblock of m, so it can be
      stated on the thread's restricted memory too.
   *)
  Definition glob_coherent (m : mem) (σ0 : rmap) : Prop :=
    ∃ Hlt : permMapLt (perm_of_rmap σ0) (getMaxPerm m), coherent (restrPermMap Hlt) σ0.
  
  Definition thread_state_interp γ γi m σ z : iProp Σ :=
    ∃ σ0, ⌜glob_coherent m σ0⌝ ∧ conc_state_interp γ σ0 z ∗ thread_mem_auth γ γi m σ.

  Definition lock_rmap_nonempty_on (ls : gset address) (σ : rmap) : Prop :=
    forall l' z, l' ∈ ls -> (0 <= z < Z.of_nat (size_chunk_nat Mptr))%Z ->
      Mem.perm_order'' (Some Nonempty) ((perm_of_rmap σ) # (l'.1) (l'.2 + z)%Z).

  Definition lock_state1 `{!lockGS Σ} `{!inG Σ rmap_authUR} (γ : gname) (m : mem) (ls : gset address) (IR : address -> option access_map) : mpred :=
    ∃ I : gmap address mpred,
      <affine> ⌜dom I = ls ∧ lock_addresses_disjoint ls⌝ ∗
                               own lockGS_gname (gmap_view_auth (DfracOwn 1) (invariant_unfold <$> I)) ∗
                               [∗ map] a ↦ R ∈ I,
    (* unlocked *)
    (∃ (σlock : rmap) (l0 : access_map),
        rmap_frag γ σlock ∗
        <affine>⌜IR a = Some l0 ∧ mem_equiv.access_map_equiv l0 (perm_of_rmap σlock) ∧
          Mem_load_unchecked Mptr m a.1 a.2 = Vptrofs Ptrofs.one ∧
          lock_rmap_nonempty_on ls σlock⌝ ∗ ▷ R) ∨
      (* locked *)
      (<affine>⌜IR a = Some empty_map ∧ Mem_load_unchecked Mptr m a.1 a.2 = Vptrofs Ptrofs.zero⌝).
  
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

  Lemma init_conc_VST_frag `{VSTGpreS0 : !VSTGpreS () Σ} (z : ()) :
    ⊢ |==> ∀ Hinv : invGS_gen HasNoLc Σ,
      ∃ (HG : gen_heapGS share address resource Σ) (FS : funspecGS Σ)
        (ES : externalGS () Σ) (HL : lockGS Σ) (γ : gname),
        @state_interp Σ () HG ES Mem.empty ∅ z ∗ rmap_auth γ ∅ ∗ rmap_frag γ ∅ ∗
          @funspec_auth Σ FS (∅ : gmap address funspecO') ∗ @has_ext () Σ ES z ∗
          @lock_state1 HL _ γ Mem.empty (∅ : gset address) (fun _ => None) ∗ gen_heap_meta_auth HG.
  Proof.
    intros; iIntros.
    iMod gen_heap_init_names_empty as (γh γmeta) "(Hheap & Hmeta)".
    iMod (own_alloc (A := gmap_view.gmap_viewR address (@funspecO' Σ)) (gmap_view.gmap_view_auth
        (dfrac.DfracOwn 1) ∅)) as (γf) "Hfunspec".
    { apply gmap_view.gmap_view_auth_valid. }
    iMod (ext_alloc z) as (ES) "(Hextauth & Hhasext)".
    iMod (own_alloc (A := gmap_view.gmap_viewR address (laterO (iPropO Σ)))
      (gmap_view.gmap_view_auth (dfrac.DfracOwn 1) (∅ : gmap address (laterO (iPropO Σ)))))
      as (γL) "Hlockauth".
    { apply gmap_view.gmap_view_auth_valid. }
    iMod (own_alloc (A := rmap_authUR)
            ((@auth_auth raw_rmapR (DfracOwn 1) (∅ : rmap)) ⋅ (@auth_frag raw_rmapR (∅ : rmap))))
      as (γ) "Hrmap".
    { by apply auth_both_valid. }
    iModIntro.
    iIntros (Hinv).
    pose (HG := {| gen_heap_inG := VSTGpreS_heap; gen_heap_name := γh; gen_meta_name := γmeta |}).
    pose (FS := FunspecG _ _ γf).
    pose (HGS := ({| heapGS_invGS := Hinv; heapGS_gen_heapGS := HG; heapGS_funspecGS := FS |} : heapGS Σ)).
    pose (HHfrag := Build_VSTGS _ _ HGS ES).
    pose (HL := LockGS Σ _ γL).
    iAssert (@lock_state1 HL _ γ Mem.empty (∅ : gset address) (fun _ => None)) with "[Hlockauth]" as "Hlocks".
    { rewrite /lock_state1.
      iExists (∅ : gmap address mpred).
      rewrite fmap_empty big_sepM_empty.
      iFrame "Hlockauth".
      iPureIntro.
      split; try done.
    }
    iExists HG, FS, ES, HL, γ.
    rewrite /gen_heap_meta_auth /= /rmap_auth /rmap_frag.
    iDestruct "Hrmap" as "(Hauth & Hfrag)".
    iFrame.
    iSplit => //.
    iPureIntro.
    by apply (empty_coherent Mem.empty).
  Qed.

  Lemma frag_mem_auth_corestep_other (q : Qp) (m m' : mem) (p : access_map) (σ : rmap)
    (Hp : permMapLt p (getMaxPerm m)) (Hσ : permMapLt (perm_of_rmap σ) (getMaxPerm m))
    (Hσ' : permMapLt (perm_of_rmap σ) (getMaxPerm m')):
    mem_step (restrPermMap Hp) m' -> permMapsDisjoint p (perm_of_rmap σ) ->
    frag_mem_auth (restrPermMap Hσ) σ -∗ frag_mem_auth (restrPermMap Hσ') σ.
  Proof.
(*    intros Hstep Hdisj.
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
    replace (permMapLt_restr Hlt0) with Hσ' by apply ProofIrrelevance.proof_irrelevance.
    done.
  Qed. *) Admitted.

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

  (*(* use map_fold instead of foldr map_to_list *)
  Global Instance perm_of_rmap_proper n : Proper (dist(A := rmap)(Dist := cmra_dist raw_rmapR) n ==> eq) perm_of_rmap.
  Proof. intros ???. rewrite /perm_of_rmap.
    induction x using fin_maps.map_fold_ind.
    - admit.
    -
  Admitted.*)

  (** jsafe_frag_pre **)
  Program Definition jsafe_frag_pre (γ : gname) (γi : gname) (jsafe : coPset -d> unit -d> CC_core -d> iPropO Σ) :
    coPset -d> unit -d> CC_core -d> iPropO Σ := λ E z c,
     |={E}=>
      ∀ (m : mem) σ,
       thread_state_interp γ γi m σ z -∗
      (∃ i, ⌜halted (cl_core_sem ge) c i⌝ ∧ thread_state_interp γ γi m σ z ∗
        Jext_spec_exit (concurrent_ext_spec CS ext_link) (Some (Vint i))) ∨
      
      (|={E}=> ∃ c' m' σ',
          ⌜corestep (cl_core_sem ge) c m c' m'⌝ ∧
          thread_state_interp γ γi m' σ' z ∗ ▷ jsafe E z c') ∨
      
      (∃ e args x, ⌜at_external (cl_core_sem ge) c m = Some (e, args)⌝ ∧
            thread_state_interp γ γi m σ z ∗
          Jext_spec_pre (concurrent_ext_spec CS ext_link) e x
          (genv_symb_injective ge) (sig_args (ef_sig e)) args ∗
        ▷ (∀ ret m' σ' z',
            ⌜Val.has_type_list args (sig_args (ef_sig e)) ∧ Builtins0.val_opt_has_rettype ret (sig_res (ef_sig e))⌝ →
            |={E}=> thread_state_interp γ γi m' σ' z' -∗
              Jext_spec_post (concurrent_ext_spec CS ext_link) e x (genv_symb_injective ge)
              (sig_res (ef_sig e)) ret -∗ (* already added an extra inner fupd *)
                                          |={E}=> ∃ c', ⌜after_external (cl_core_sem ge) ret c m' = Some c'⌝ ∧
                    thread_state_interp γ γi m' σ' z' ∗ jsafe E z' c')).

  Local Instance jsafe_frag_pre_contractive γ γi: Contractive (jsafe_frag_pre γ γi).
  Proof.
    rewrite /jsafe_frag_pre => n jsafe jsafe' Hsafe E z c.
    repeat first [f_contractive | f_equiv]; try apply Hsafe.
  Qed.

  Local Definition jsafe_frag_def γ γi: coPset -> unit -> CC_core -> iProp Σ :=
    fixpoint (jsafe_frag_pre γ γi).
  Local Definition jsafe_frag_aux γ γi: seal (jsafe_frag_def γ γi). Proof. by eexists. Qed.
  Definition jsafe_frag γ γi := (jsafe_frag_aux γ γi).(unseal).
  Local Lemma jsafe_frag_unseal γ γi: jsafe_frag γ γi = jsafe_frag_def γ γi.
  Proof. rewrite -(jsafe_frag_aux γ γi).(seal_eq) //. Qed.

  Lemma jsafe_frag_unfold γ γi E z c:
    jsafe_frag γ γi E z c ⊣⊢ jsafe_frag_pre γ γi (jsafe_frag γ γi) E z c.
  Proof.
    rewrite jsafe_frag_unseal.
    apply (fixpoint_unfold (jsafe_frag_pre γ γi)).
  Qed.

  (*Definition jsafe_frag (γ : gname) γi := jsafe (genv_symb := genv_symb_injective) (cl_core_sem ge) (concurrent_ext_spec CS ext_link) ge
        (gen_heapGS0 := thread_gen_heapGS γi).*)

  (*Lemma rmap_auth_frag_agree `{!inG Σ rmap_authUR} γ (σ0 σ : raw_rmapR) :
    rmap_auth γ σ0 ∗ rmap_frag γ σ ⊢ ⌜σ0 ≡ σ⌝.
  Proof.
    iIntros "(Hauth & Hfrag)".
    rewrite /rmap_auth /rmap_frag.
    iCombine "Hauth Hfrag" as "Hboth".
    rewrite -own_op.
    iPoseProof (own_valid with "Hboth") as "Hvalid".
    iDestruct (frac_auth_agree_fullI σ0 σ with "Hvalid") as "%"; try done.
  Qed.*)

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
      erewrite resR_to_resource_eq; done.
    }
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

  Lemma coherent_restrPermMap_iff m1 m2 σ
    (H1 : permMapLt (perm_of_rmap σ) (getMaxPerm m1))
    (H2 : permMapLt (perm_of_rmap σ) (getMaxPerm m2)) :
    Mem.nextblock m1 = Mem.nextblock m2 → Mem.mem_contents m1 = Mem.mem_contents m2 →
    coherent (restrPermMap H1) σ → coherent (restrPermMap H2) σ.
  Proof.
    intros Hnb Hc Hcoh (b, ofs).
    destruct (Hcoh (b, ofs)) as (Hnext & Hcont & Hacc).
    split3.
    - intros Hge; apply Hnext.
      rewrite restrPermMap_nextblock Hnb //.
    - intros v Hv; specialize (Hcont v Hv).
      rewrite restrPermMap_contents in Hcont |- *.
      rewrite /contents_at -Hc //.
    - rewrite /access_cohere access_at_restrPermMap_perm_res //.
  Qed.

  Lemma glob_coherent_restrPermMap m p (Hp : permMapLt p (getMaxPerm m)) σ0 :
    glob_coherent (restrPermMap Hp) σ0 ↔ glob_coherent m σ0.
  Proof.
    split; intros (Hlt & Hcoh).
    - assert (Hlt' : permMapLt (perm_of_rmap σ0) (getMaxPerm m)).
      { intros b ofs; rewrite -(getMax_restr Hp b); apply Hlt. }
      exists Hlt'.
      apply (coherent_restrPermMap_iff (restrPermMap Hp) m σ0 Hlt Hlt'); done.
    - assert (Hlt' : permMapLt (perm_of_rmap σ0) (getMaxPerm (restrPermMap Hp))).
      { intros b ofs; rewrite (getMax_restr Hp b); apply Hlt. }
      exists Hlt'.
      apply (coherent_restrPermMap_iff m (restrPermMap Hp) σ0 Hlt Hlt'); done.
  Qed.

  Lemma glob_coherent_bound m σ0 : glob_coherent m σ0 → rmap_bound (Mem.nextblock m) σ0.
  Proof. intros (Hlt & Hcoh); apply (coherent_rmap_bound _ _ Hcoh). Qed.
  

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

  (*Lemma rmap_auth_frag_agreeI `{!inG Σ rmap_authUR} γ (σ0 σ : raw_rmapR) :
    rmap_auth γ σ0 ∗ rmap_frag γ 1 σ ⊢ ⌜σ0 ≡ σ⌝.
  Proof.
    iIntros "(Hauth & Hfrag)".
    rewrite /rmap_auth /rmap_frag.
    iCombine "Hauth Hfrag" as "Hboth".
    rewrite -own_op.
    iDestruct (own_valid_r with "Hboth") as "[Hboth Hvalid]".
    by iDestruct (frac_auth_agree_fullI with "Hvalid") as "%Heq".
  Qed.

  Lemma rmap_auth_frag_set `{!inG Σ rmap_authUR} γ (σ0 σ σ1 : raw_rmapR) (Hv : ✓ σ1) :
    rmap_auth γ σ0 ∗ rmap_frag γ 1 σ ==∗ rmap_auth γ σ1 ∗ rmap_frag γ 1 σ1.
  Proof.
    rewrite /rmap_auth /rmap_frag -!own_op.
    iIntros "H".
    iApply (own_update with "H").
    by apply frac_auth_update_1.
  Qed.*)

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

  Lemma rmap_auth_equiv_local γ (σ1 σ2 : rmap) : σ1 ≡ σ2 -> rmap_auth γ σ1 ⊣⊢ rmap_auth γ σ2.
  Proof. intros Heq; rewrite /rmap_auth; apply own_proper; by f_equiv. Qed.

  (** rmap_bound, full_VAL, resource_decay_at, resource_decay, coherent_rmap_bound
      are defined in  juicy_mem.v
   **)
  
  Local Instance resource_shared_unit : Unit (shared.shared (leibnizO resource)) :=
    shared.NO (V := leibnizO resource) (share_alg.Share share_bot) unreadable_bot.

  (** resource_decay_at nextb l r r' : describes the resource changes allowed
    at one address l during an ordinary Clight step.
(nextb :next block before the step, r and r' are the old and new lookups at l).

- In old rmap representation, an empty cell was represented by NO Share.bot ...,
while an owned cell had the form YES sh Psh k pp.

- In current representation, an empty cell is represented by None before allocation
  or by Some ε after deletion, and an owned cell has the form 
  Some (shared.YES (DfracOwn (Share sh)) rsh (to_agree k))

- Predicate payloads such as pp are no longer stored in heap resources;
    funspecs and lock invariants are maintained separately in ghost state and invariants.

- decay_same leaves the resource unchanged.

- decay_store corresponds to the writable VAL case.
It preserves the ownership and readable and changes only VAL v to VAL v'.

- decay_alloc corresponds to allocation of a fully owned VAL in a fresh block.
The old relation obtained empty of the source cell from its global bound; this constructor records it as None.

- decay_free corresponds to replacing a fully owned VAL by the empty resource.
The current resource-map deletion operation leaves Some ε at the address, corresponding to the old NO Share.bot ... resource.

   *)

  (** Correspondence between the old and current resource representations:
  - Old: phi @ l ; New: σ !! l
  - Old: NO Share.bot ...  ; New: None, or the unit cell Some ε
  - Old: YES sh Psh k pp  ;  New: Some (shared.YES dq rsh (to_agree k))
  - Old: the ownership share sh  ; New: dshare.DfracOwn (share_alg.Share sh)
  - Old: the readability proof Psh ; New: rsh of type dshare.readable_dfrac dq
  - Old: a resource kind such as VAL v ; New: the agreement value to_agree (VAL v)
  - Old: the predicate payload pp
      New: no corresponding heap component; funspecs and lock invariants
           are stored separately in ghost state and invariants
  - Old: equality after resource_fmap and approximation at level n
      New: direct equality of resource-map entries *)

  Lemma rmap_bound_mono b b' σ : (b <= b')%positive → rmap_bound b σ → rmap_bound b' σ.
  Proof. intros Hbb Hb l Hl; apply Hb; lia. Qed.

  Lemma rmap_bound_op (b : Values.block)
    (σ1 σ2 : resource_map.rmapUR share address (leibnizO resource)) :
    rmap_bound b σ1 → rmap_bound b σ2 → rmap_bound b (σ1 ⋅ σ2).
  Proof.
    intros H1 H2 l Hl.
    unfold rmap_bound in *.
    specialize (H1 l Hl).
    specialize (H2 l Hl).
    assert (Hop : (σ1 ⋅ σ2) !! l ≡ None).
    { apply equiv_dist; intros n; by rewrite gmap.lookup_op H1 H2. }
    destruct ((σ1 ⋅ σ2) !! l) as [r |] eqn:Hr; last done. inv Hop.
  Qed.

  Lemma rmap_bound_frame (b : Values.block)
    (σ0 σ frame : resource_map.rmapUR share address (leibnizO resource)) :
    rmap_bound b σ0 → σ0 ≡ σ ⋅ frame → rmap_bound b frame.
  Proof.
    intros Hb Heq l Hl.
    pose proof (proj1 (@equiv_dist (resource_map.rmapUR share address (leibnizO resource)) σ0 (σ ⋅ frame)) Heq) as Heqdist.
    assert (Hlookup : σ0 !! l ≡{0}≡ (σ ⋅ frame) !! l).
    { eapply (@gmap.lookup_ne address _ _ (shared.sharedR (leibnizO resource)) l 0); eauto. }
    rewrite (Hb l Hl) in Hlookup.
    rewrite gmap.lookup_op in Hlookup.
    destruct (σ !! l) as [x |] eqn:Hx; destruct (frame !! l) as [y |] eqn:Hy;
      rewrite Hx Hy in Hlookup |- *; simpl in Hlookup |- *; auto.
    inv Hlookup. inv Hlookup.
  Qed.

  (** A writable local VAL fragment permits updating the value stored in both the global cell and the local fragment from v to v'

   (Gv, Lv) ~l~> (Gv', Lv')
   Gv: aggregate resource of the cell in global rmap
   Lv: fragment of the cell in the current thread
   *)
  Lemma resource_decay_store_cell_local_update (sh : share) (dqG : dshare.dfrac)
    (rshG : dshare.readable_dfrac dqG) (rshL : dshare.readable_dfrac (dshare.DfracOwn (share_alg.Share sh))) (v v' : memval) (Hsh : share_writable sh) :
    @local_update (shared.sharedR (leibnizO resource))
      ( shared.YES (V := leibnizO resource) dqG rshG (to_agree (VAL v)),
        shared.YES (V := leibnizO resource) (dshare.DfracOwn (share_alg.Share sh)) rshL
          (to_agree (VAL v)) )
      (shared.YES (V := leibnizO resource) dqG rshG (to_agree (VAL v')),
        shared.YES (V := leibnizO resource) (dshare.DfracOwn (share_alg.Share sh)) rshL
          (to_agree (VAL v'))).
  Proof.
    intros n mz Hvalid Heq.
    split; first done.
    destruct mz as [c|].
    - rewrite !shared.shared_dist' /= !shared.dfrac_of_op' !shared.val_of_op' in Heq |- *.
      destruct Heq as [-> Hval].
      destruct (shared.dfrac_error _) eqn:Herr; try done.
      destruct c; try done.
      simpl in *.
      exfalso.
      destruct Hvalid as [Hdq_valid _].
      rewrite comm in Hdq_valid.
      destruct (dshare.dfrac_valid_own_readable _ _ rsh Hdq_valid) as (? & Hshare & ?).
      by inv Hshare.
    - by destruct Heq as [-> ?].
  Qed.

  Local Definition resource_shared_opM (x : shared.shared (leibnizO resource))
    (mx : option (shared.shared (leibnizO resource))) : shared.shared (leibnizO resource) :=
    @OraopM (shared.sharedR (leibnizO resource)) x mx.

  Lemma resource_decay_store_shared_frame_local_update sh
    (rsh : dshare.readable_dfrac (dshare.DfracOwn (share_alg.Share sh))) (v v' : memval)
    (frame : option (shared.shared (leibnizO resource))) (Hsh : share_writable sh) :
    @local_update (shared.sharedR (leibnizO resource))
      (resource_shared_opM (shared.YES (V := leibnizO resource)
         (dshare.DfracOwn (share_alg.Share sh)) rsh (to_agree (VAL v))) frame,
       shared.YES (V := leibnizO resource) (dshare.DfracOwn (share_alg.Share sh)) rsh (to_agree (VAL v)))
      (resource_shared_opM (shared.YES (V := leibnizO resource) (dshare.DfracOwn (share_alg.Share sh)) rsh (to_agree (VAL v'))) frame,
       shared.YES (V := leibnizO resource) (dshare.DfracOwn (share_alg.Share sh)) rsh (to_agree (VAL v'))).
  Proof.
    destruct frame as [fr |].
    - destruct fr as [dqf rshf vf | shf nrshf].
      + intros n mz Hvalid _.
        exfalso.
        simpl in Hvalid.
        rewrite shared.YES_op' in Hvalid.
        destruct (shared.readable_dfrac_dec (dshare.DfracOwn (share_alg.Share sh) ⋅ dqf))
          as [rshG | Hnot_readable] eqn:Hdec; auto.
        destruct Hvalid as [Hdq_valid _].
        rewrite comm in Hdq_valid.
        destruct (dshare.dfrac_valid_own_readable _ _ rshf Hdq_valid) as (? & Hshare & ?).
        by inv Hshare.
      + simpl.
        rewrite /op /shared.shared_op_instance /=.
        destruct (shared.readable_dfrac_dec (dshare.DfracOwn (share_alg.Share sh) ⋅ dshare.DfracOwn shf)) as [rshG | Hnot_readable]; simpl.
        * setoid_rewrite (comm op (shared.YES (V := leibnizO resource) (dshare.DfracOwn (share_alg.Share sh)) rsh (to_agree (VAL v)) : shared.sharedR (leibnizO resource)) _).
          setoid_rewrite (comm op (shared.YES (V := leibnizO resource) (dshare.DfracOwn (share_alg.Share sh)) rsh (to_agree (VAL v')) : shared.sharedR (leibnizO resource)) _).
          rewrite !shared.NO_YES_op'.
          destruct (shared.readable_dfrac_dec _) as [rshG' | Hnot_readable'] eqn:Hdec'.
          ++ by apply resource_decay_store_cell_local_update.
          ++ exfalso.
             apply Hnot_readable'.
             by rewrite (comm op (dshare.DfracOwn shf) _).
        * assert (Herr : shared.dfrac_error (dshare.DfracOwn (share_alg.Share sh) ⋅ dshare.DfracOwn shf) = true).
          { apply shared.dfrac_op_readable; auto. }
          intros n mz Hvalid _.
          simpl in *.
          destruct (shared.readable_dfrac_dec (dshare.DfracOwn (share_alg.Share sh) ⋅
                dshare.DfracOwn shf)) as [rshG | Hnot_readable'].
          ++ by exfalso.
          ++ simpl in *.
             exfalso.
             pose proof (shared.dfrac_error_fail (leibnizO resource) (shared.YES (V := leibnizO resource) (dshare.DfracOwn (share_alg.Share sh)) rsh (to_agree (VAL v))) (shared.NO (V := leibnizO resource) shf nrshf) Herr) as Hop.
             setoid_rewrite Hop in Hvalid.
             unfold shared.err in Hvalid. done.
    - simpl.
      apply resource_decay_store_cell_local_update; auto.
  Qed.
  
  Local Definition resource_option_frame (r frame : option (shared.shared (leibnizO resource))) : option (shared.shared (leibnizO resource)) :=
    match r with
    | None => frame
    | Some x => Some (resource_shared_opM x frame)
    end.

  Lemma resource_option_frame_op r frame :
    resource_option_frame r frame =
      @op (cmra.optionR (shared.sharedR (leibnizO resource))) _ r frame.
  Proof. destruct r, frame; reflexivity. Qed.
  
  Lemma resource_decay_at_frame_local_update nextb l r r' (frame : option (shared.shared (leibnizO resource))) :
    ((l.1 >= nextb)%positive → frame = None) → resource_decay_at nextb l r r' →
    @local_update (cmra.optionR (shared.sharedR (leibnizO resource)))
      (resource_option_frame r frame, r) (resource_option_frame r' frame, r').
  Proof.
    intros Hframe Hdecay.
    induction Hdecay as [r | sh rsh v v' Hw | v Hl | rsh v | r1 r1' r2' r2 E1 Hd IH E2]; simpl.
    - intros n mz Hvalid Heq; split; auto.
    - simpl.
      apply (option_local_update (A := ora_cmraR (shared.sharedR (leibnizO resource)))
               (resource_shared_opM (shared.YES (V := leibnizO resource) (dshare.DfracOwn (share_alg.Share sh)) rsh (to_agree (VAL v))) frame)
               (shared.YES (V := leibnizO resource) (dshare.DfracOwn (share_alg.Share sh)) rsh (to_agree (VAL v))) (resource_shared_opM (shared.YES (V := leibnizO resource) (dshare.DfracOwn (share_alg.Share sh)) rsh (to_agree (VAL v'))) frame)
               (shared.YES (V := leibnizO resource) (dshare.DfracOwn (share_alg.Share sh)) rsh (to_agree (VAL v'))) (resource_decay_store_shared_frame_local_update sh rsh v v' frame Hw)).
    - specialize (Hframe Hl).
      subst frame.
      apply (alloc_option_local_update (A := ora_cmraR (shared.sharedR (leibnizO resource)))).
      rewrite /full_VAL.
      split; done.
    - apply (option_local_update (A := ora_cmraR (shared.sharedR (leibnizO resource)))).
      destruct frame as [fr |].
      + setoid_rewrite (@ucmra_unit_left_id (shared.sharedUC (leibnizO resource)) fr).
        apply (cancel_local_update_unit (A := shared.sharedUC (leibnizO resource))), _.
      + simpl.
        rewrite -{1}(@ucmra_unit_right_id (shared.sharedUC (leibnizO resource)) (shared.YES (V := leibnizO resource)(dshare.DfracOwn (share_alg.Share share_top)) rsh (to_agree (VAL v)))).
        apply (cancel_local_update_unit (A := shared.sharedUC (leibnizO resource))), _.
    - (* decay_equiv *)
      rewrite !resource_option_frame_op in IH |- *.
      rewrite -E1 E2 in IH; exact IH.
  Qed.

  Lemma rmap_pointwise_local_update
    (m1 m2 m1' m2' : resource_map.rmapUR share address (leibnizO resource)) :
    (∀ l, @local_update (cmra.optionR (shared.sharedR (leibnizO resource)))
       (m1 !! l, m2 !! l) (m1' !! l, m2' !! l)) →
    @local_update (resource_map.rmapUR share address (leibnizO resource)) (m1, m2) (m1', m2').
  Proof.
    intros Hpoint n mf Hvalid Heq.
    destruct mf as [mf |].
    - split.
      + intros l.
        simpl in *.
        eapply (proj1 (Hpoint l n (Some (mf !! l)) (Hvalid l) _)).
        Unshelve. simpl.
        specialize (Heq l).
        by rewrite lookup_op in Heq.
      + intros l.
        rewrite lookup_op.
        eapply (proj2 (Hpoint l n (Some (mf !! l)) (Hvalid l) _)).
        Unshelve. simpl.
        specialize (Heq l).
        by rewrite lookup_op in Heq.
    - split.
      + intros l.
        simpl in *.
        eapply (proj1 (Hpoint l n None (Hvalid l) _)); eauto.
        Unshelve. simpl.
        by specialize (Heq l).
      + intros l.
        eapply (proj2 (Hpoint l n None (Hvalid l) _)).
        Unshelve. simpl.
        by specialize (Heq l).
  Qed.

  Lemma resource_decay_join_local_update (nextb : Values.block)
    (σ σ' frame σ0 : resource_map.rmapUR share address (leibnizO resource)) :
    rmap_bound nextb frame → σ0 ≡ σ ⋅ frame →
    resource_decay nextb σ σ' → rmap_local_update σ0 σ (σ' ⋅ frame) σ'.
  Proof.
    intros Hframe Hdecomp [_ Hdecay].
    unfold rmap_local_update.
    assert (Hupd : @local_update (resource_map.rmapUR share _ _) (σ ⋅ frame, σ) (σ' ⋅ frame, σ')).
    { apply rmap_pointwise_local_update.
      intros l.
      rewrite !lookup_op -!resource_option_frame_op.
      apply (resource_decay_at_frame_local_update nextb l).
      - intros Hl; by apply Hframe.
      - apply Hdecay.
    }
    intros n mz Hvalid Heq.
    simpl in *.
    pose proof (proj1 (@equiv_dist (resource_map.rmapUR _ _ _) σ0 (σ ⋅ frame)) Hdecomp n) as Hdecomp_n.
    eapply (Hupd n mz).
    - apply (ora_validN_ne' n _ (σ ⋅ frame, σ).1); rewrite -Hdecomp_n //.
    - etransitivity; try symmetry; try apply Hdecomp_n; done.
  Qed.
  
  (* This almost follows from what we've already proved about mem steps. But in theory,
     since jsafe knows that it has full ownership of the state interp, it could change the
     contents of a FUN or LK cell. We might need to restrict this somehow in jsafe. *)

  Local Notation shresR := (cmra.optionR (shared.sharedR (leibnizO resource))) (only parsing).
  Local Notation shUC := (shared.sharedUC (leibnizO resource)) (only parsing).

  Definition acc_kept (m m' : mem) (l : address) : Prop :=
    (∀ k, access_at m' l k = access_at m l k) ∨
    (access_at m l Cur = Some Freeable ∧ access_at m' l Max = None).
 
  Lemma acc_kept_trans m1 m2 m3 l :
    acc_kept m1 m2 l → acc_kept m2 m3 l → acc_kept m1 m3 l.
  Proof.
    intros [H1 | (F1 & N1)] [H2 | (F2 & N2)].
    - left; intros k; rewrite H2 H1 //.
    - right; split; [rewrite -H1 // | done].
    - right; split; [done | rewrite H2 //].
    - right; split; done.
  Qed.

  Locate alloc_access_inv.

  Lemma alloc_access_old m lo hi m' b l k :
    Mem.alloc m lo hi = (m', b) → Mem.valid_block m l.1 →
    access_at m' l k = access_at m l k.
  Proof.
    destruct l as [b' ofs]; simpl. intros Halloc Hv.
    pose proof (Mem.alloc_result _ _ _ _ _ Halloc) as Hb; subst b.
    unfold access_at; simpl.
    destruct (PMap.get b' (Mem.mem_access m') ofs k) as [p|] eqn:E.
    - apply (semantics_lemmas.alloc_access_inv _ _ _ _ _ Halloc) in E as [(-> & _) | (_ & E)].
      + exfalso; exact (Plt_strict _ Hv).
      + by rewrite E.
    - apply (semantics_lemmas.alloc_access_inv_None _ _ _ _ _ Halloc) in E. by rewrite E.
  Qed.
  
  Lemma free_acc_kept m b lo hi m' l :
    Mem.free m b lo hi = Some m' → acc_kept m m' l.
  Proof.
    intros Hfree; destruct l as [b' ofs].
    destruct (peq b' b) as [-> | Hb].
    - destruct (zle lo ofs); [destruct (zlt ofs hi)|].
      + right. apply (free_access _ _ _ _ _ Hfree). lia.
      + left; intros k; symmetry.
        apply (free_access_other _ _ _ _ _ Hfree). right; right; lia.
      + left; intros k; symmetry.
        apply (free_access_other _ _ _ _ _ Hfree). right; left; lia.
    - left; intros k; symmetry.
      apply (free_access_other _ _ _ _ _ Hfree). left; exact Hb.
  Qed.
 
  Lemma free_list_acc_kept : ∀ bl m m' l,
    Mem.free_list m bl = Some m' → acc_kept m m' l.
  Proof.
    induction bl as [| [[b lo] hi] bl IH]; intros m m' l Hf; simpl in Hf.
    - inv Hf. left; intros k; done.
    - destruct (Mem.free m b lo hi) as [m1|] eqn:Hfree; [|discriminate].
      eapply acc_kept_trans; [eapply free_acc_kept; eassumption | eapply IH; eassumption].
  Qed.
 
  Lemma mem_step_acc_kept m m' :
    mem_step m m' → ∀ loc, Mem.valid_block m loc.1 → acc_kept m m' loc.
  Proof.
    induction 1 as [? ? b0 ofs0 bytes Hs | ? ? lo hi b' Ha | ? ? bl Hf | ? ? m'' H1 IH1 H2 IH2];
      intros loc Hv.
    - left; intros k.
      rewrite /access_at (Mem.storebytes_access _ _ _ _ _ Hs) //.
    - left; intros k. eapply alloc_access_old; eassumption.
    - eapply free_list_acc_kept; eassumption.
    - eapply acc_kept_trans; [by apply IH1 |].
      apply IH2.
      eapply Plt_Ple_trans; [exact Hv | exact (semantics_lemmas.mem_step_nextblock' _ _ H1)].
  Qed.
 
  Lemma mem_step_contents_nonwritable m m' l :
    mem_step m m' → Mem.valid_block m l.1 → ¬ Mem.perm m l.1 l.2 Cur Writable →
    contents_at m' l = contents_at m l.
  Proof.
    intros Hstep Hv Hw. symmetry.
    exact (semantics_lemmas.mem_step_obeys_cur_write m l.1 l.2 m' Hv Hw Hstep).
  Qed.

  Lemma perm_of_res_unit : perm_of_res ((ε : dshare.dfracUC), None) = None.
  Proof. rewrite /= if_true //. Qed.
 
  Lemma perm_of_res_VAL_eq d v v' :
    perm_of_res (d, Some (VAL v)) = perm_of_res (d, Some (VAL v')).
  Proof. destruct d as [[|]|[|]]; reflexivity. Qed.
 
  Lemma perm_of_res_noVAL_not_writable (x : dshare.dfrac * option resource) :
    (∀ v, x.2 ≠ Some (VAL v)) → ¬ Mem.perm_order' (perm_of_res x) Writable.
  Proof.
    destruct x as [dq o]; intros Hno; simpl in Hno.
    destruct (perm_of_res_cases dq o) as [(v & Ho & _) | (_ & ->)].
    - by contradiction (Hno v).
    - repeat match goal with |- context [decide ?P] => destruct (decide P) end;
        simpl; first [done | intros H; inversion H].
  Qed.
 
  Lemma resR_YES dq (rsh : dshare.readable_dfrac dq) (r : resource) :
    resR_to_resource (Some (shared.YES (V := leibnizO resource) dq rsh (to_agree r))) = (dq, Some r).
  Proof. rewrite /= elem_of_to_agree //. Qed.
 
  Lemma resR_YES_VAL_op_snd dq (rsh : dshare.readable_dfrac dq) v (f : shresR) :
    ✓ ((Some (shared.YES (V := leibnizO resource) dq rsh (to_agree (VAL v))) : shresR) ⋅ f) →
    (resR_to_resource ((Some (shared.YES (V := leibnizO resource) dq rsh (to_agree (VAL v))) : shresR) ⋅ f)).2
      = Some (VAL v).
  Proof.
    intros Hv.
    pose proof (resR_le (Some (shared.YES (V := leibnizO resource) dq rsh (to_agree (VAL v))) : shresR) _ Hv (cmra_included_l _ f)) as [_ Hle].
    destruct Hle as [Hn | Heq].
    - rewrite resR_YES in Hn. discriminate.
    - rewrite resR_YES in Heq; auto.
  Qed.
 
  Lemma resR_YES_op_fst dq (rsh : dshare.readable_dfrac dq) a a' (f : shresR) :
    (resR_to_resource ((Some (shared.YES (V := leibnizO resource) dq rsh a') : shresR) ⋅ f)).1 =
    (resR_to_resource ((Some (shared.YES (V := leibnizO resource) dq rsh a) : shresR) ⋅ f)).1.
  Proof.
    destruct f as [fs|]; last reflexivity.
    change (shared.dfrac_of ((shared.YES (V := leibnizO resource) dq rsh a' : shared.sharedR (leibnizO resource)) ⋅ fs) = shared.dfrac_of ((shared.YES (V := leibnizO resource) dq rsh a : shared.sharedR (leibnizO resource)) ⋅ fs)).
    rewrite !shared.dfrac_of_op' //.
  Qed.
 
  (* storing a new value does not change the permission of the joined cell *)
  Lemma resR_store_perm dq (rsh : dshare.readable_dfrac dq) v v' (f : shresR) :
    ✓ ((Some (shared.YES (V := leibnizO resource) dq rsh (to_agree (VAL v))) : shresR) ⋅ f) →
    ✓ ((Some (shared.YES (V := leibnizO resource) dq rsh (to_agree (VAL v'))) : shresR) ⋅ f) →
    perm_of_res (resR_to_resource ((Some (shared.YES (V := leibnizO resource) dq rsh (to_agree (VAL v'))) : shresR) ⋅ f)) =
    perm_of_res (resR_to_resource ((Some (shared.YES (V := leibnizO resource) dq rsh (to_agree (VAL v))) : shresR) ⋅ f)).
  Proof.
    intros Hv Hv'.
    pose proof (resR_YES_VAL_op_snd dq rsh v f Hv) as H1.
    pose proof (resR_YES_VAL_op_snd dq rsh v' f Hv') as H2.
    pose proof (resR_YES_op_fst dq rsh (to_agree (VAL v)) (to_agree (VAL v')) f) as H3.
    revert H1 H2 H3.
    destruct (resR_to_resource ((Some (shared.YES (V := leibnizO resource) dq rsh (to_agree (VAL v))) : shresR) ⋅ f)) as [d1 o1].
    destruct (resR_to_resource ((Some (shared.YES (V := leibnizO resource) dq rsh (to_agree (VAL v'))) : shresR) ⋅ f)) as [d2 o2].
    simpl; intros -> -> ->.
    eapply perm_of_res_VAL_eq; eauto.
    Unshelve. done. Unshelve. done.
  Qed.
 
  (* a full cell leaves nothing (no permission, no value) to its frame *)
  Lemma resR_free_op rsh v (f : shresR) :
    ✓ ((Some (shared.YES (V := leibnizO resource) (dshare.DfracOwn (share_alg.Share share_top)) rsh (to_agree (VAL v))) : shresR) ⋅ f) →
    ✓ ((Some (ε : shUC) : shresR) ⋅ f) →
    perm_of_res (resR_to_resource ((Some (ε : shUC) : shresR) ⋅ f)) = None ∧ (resR_to_resource ((Some (ε : shUC) : shresR) ⋅ f)).2 = None.
  Proof.
    intros Hv Hvε.
    destruct f as [fs|].
    - assert (Hfs : shared.dfrac_of fs = (ε : dshare.dfracUC)).
      { assert (Hv2 : ✓ (shared.YES (V := leibnizO resource) (dshare.DfracOwn (share_alg.Share share_top)) rsh (to_agree (VAL v)) ⋅ fs)) by apply Hv.
        apply shared.shared_valid in Hv2 as [Hd _].
        destruct (shared.dfrac_of_op _ (shared.YES (V := leibnizO resource)
                    (dshare.DfracOwn (share_alg.Share share_top)) rsh (to_agree (VAL v))) fs)
          as [(_ & Hop) | Hop]; rewrite Hop in Hd.
        + exfalso.
          apply (shared.dfrac_error_invalid (dshare.DfracOwn share_alg.ShareBot) eq_refl Hd).
        + apply (dshare.dfrac_full_exclusive _ Hd).
      }
      assert (Heq : resR_to_resource ((Some (ε : shUC) : shresR) ⋅ Some fs) = resR_to_resource (Some fs)).
      { apply resR_to_resource_eq; first done.
        change ((Some ((ε : shUC) ⋅ fs) : shresR) ≡ Some fs).
        f_equiv.
        apply (ucmra_unit_left_id (A := shared.sharedUC (leibnizO resource))).
      }
      rewrite Heq.
      destruct fs as [dq' rsh' a' | sh' rsh'].
      + exfalso. simpl in Hfs. subst dq'.
        apply (@unreadable_bot _ share_instance rsh').
      + assert (sh' = share_alg.Share share_bot) as ->.
        { change (dshare.DfracOwn sh' = dshare.DfracOwn (share_alg.Share share_bot)) in Hfs.
          injection Hfs as Hsh; done. }
        assert (E : resR_to_resource (Some (shared.NO (V := leibnizO resource) (share_alg.Share share_bot) rsh'))
                    = ((ε : dshare.dfracUC), None)) by done.
        rewrite E perm_of_res_unit. split; done.
    - assert (E : resR_to_resource ((Some (ε : shUC) : shresR) ⋅ None) = ((ε : dshare.dfracUC), None)) by done.
      rewrite E perm_of_res_unit. split; done.
  Qed.
 
  (* resource_decay_at, up to ≡ (this removes decay_equiv) *)
  Lemma resource_decay_at_inv nextb l (r r' : shresR) :
    (resource_decay_at nextb l r r' →
     r' ≡ r ∨
       (∃ dq (rsh : dshare.readable_dfrac dq) v v',
           r ≡ Some (shared.YES (V := leibnizO resource) dq rsh (to_agree (VAL v))) ∧
             r' ≡ Some (shared.YES (V := leibnizO resource) dq rsh (to_agree (VAL v')))) ∨
       (l.1 >= nextb)%positive ∨
       (∃ (rsh : dshare.readable_dfrac (dshare.DfracOwn (share_alg.Share share_top))) v,
           r ≡ Some (shared.YES (V := leibnizO resource) (dshare.DfracOwn (share_alg.Share share_top)) rsh
                       (to_agree (VAL v))) ∧
             r' ≡ Some (ε : shUC)))%type.
  Proof.
    induction 1 as [r | sh rsh v v' Hw | v Hl | rsh v | r1 r1' r2' r2 E1 Hd IH E2]; auto.
    - right; left. by eexists _, _, v, v'.
    - right; right; right. by eexists _, v.
    - destruct IH as [H | [(dq & rsh & v & v' & H1 & H2) | [Hl | (rsh & v & H1 & H2)]]]; auto.
      + left. rewrite -E2 E1 //.
      + right; left. exists dq, rsh, v, v'.
        split; [rewrite E1; done | rewrite -E2; done].
      + right; right; right. exists rsh, v.
        split; [rewrite E1; done | rewrite -E2; done].
  Qed.
 
  Lemma glob_step_store dq (rsh : dshare.readable_dfrac dq) v v' (r r' f : shresR) :
    ✓ (r ⋅ f) → ✓ (r' ⋅ f) →
    r ≡ Some (shared.YES (V := leibnizO resource) dq rsh (to_agree (VAL v))) →
    r' ≡ Some (shared.YES (V := leibnizO resource) dq rsh (to_agree (VAL v'))) →
    perm_of_res (resR_to_resource r') = perm_of_res (resR_to_resource r) ∧
    perm_of_res (resR_to_resource (r' ⋅ f)) = perm_of_res (resR_to_resource (r ⋅ f)) ∧
    (resR_to_resource r').2 = Some (VAL v') ∧
    (resR_to_resource (r' ⋅ f)).2 = Some (VAL v').
  Proof.
    intros Hv0 Hv' Hr Hr'.
    assert (Hvr : ✓ r) by (eapply cmra_valid_op_l; eauto).
    assert (Hvr' : ✓ r') by (eapply cmra_valid_op_l; eauto).
    assert (HvY : ✓ ((Some (shared.YES (V := leibnizO resource) dq rsh (to_agree (VAL v))) : shresR) ⋅ f)) by rewrite -Hr //.
    assert (HvY' : ✓ ((Some (shared.YES (V := leibnizO resource) dq rsh (to_agree (VAL v'))) : shresR) ⋅ f)) by rewrite -Hr' //.
    assert (E0 : resR_to_resource (r ⋅ f) =
                 resR_to_resource ((Some (shared.YES (V := leibnizO resource) dq rsh (to_agree (VAL v))) : shresR) ⋅ f)).
    { apply resR_to_resource_eq; try done. by rewrite Hr. }
    assert (E0' : resR_to_resource (r' ⋅ f) =
                  resR_to_resource ((Some (shared.YES (V := leibnizO resource) dq rsh (to_agree (VAL v'))) : shresR) ⋅ f)).
    { apply resR_to_resource_eq; try done. by rewrite Hr'. }
    rewrite E0 E0' (resR_to_resource_eq r _ Hvr Hr) (resR_to_resource_eq r' _ Hvr' Hr').
    split; [|split; [|split]].
    - rewrite !resR_YES. apply perm_of_res_VAL_eq.
    - apply (resR_store_perm dq rsh v v' f HvY HvY').
    - rewrite resR_YES //.
    - apply (resR_YES_VAL_op_snd dq rsh v' f HvY').
  Qed.
 
  Lemma glob_step_free rsh v (r r' f : shresR) :
    ✓ (r ⋅ f) → ✓ (r' ⋅ f) →
    r ≡ Some (shared.YES (V := leibnizO resource) (dshare.DfracOwn (share_alg.Share share_top)) rsh (to_agree (VAL v))) → r' ≡ Some (ε : shUC) →
    perm_of_res (resR_to_resource (r' ⋅ f)) = None ∧ (resR_to_resource (r' ⋅ f)).2 = None.
  Proof.
    intros Hv0 Hv' Hr Hr'.
    assert (HvY : ✓ ((Some (shared.YES (V := leibnizO resource) (dshare.DfracOwn (share_alg.Share share_top)) rsh (to_agree (VAL v))) : shresR) ⋅ f)) by rewrite -Hr //.
    assert (Hvε : ✓ ((Some (ε : shUC) : shresR) ⋅ f)) by rewrite -Hr' //.
    assert (E : resR_to_resource (r' ⋅ f) = resR_to_resource ((Some (ε : shUC) : shresR) ⋅ f)).
    { apply resR_to_resource_eq; try done. by rewrite Hr'. }
    rewrite E. apply (resR_free_op rsh v f HvY Hvε).
  Qed.
 
  (* ---------- 1c. One old location ---------- *)
  (* r = σ l, r' = σ' l, f = frame l, s0 = σ0 l, t = (σ' ⋅ frame) l *)
  Lemma glob_coherent_step_at (m m' : mem) (l : address) (r r' f s0 t : shresR) :
    ✓ s0 → s0 ≡ r ⋅ f → ✓ t → t ≡ r' ⋅ f →
    (l.1 < Mem.nextblock m)%positive →
    resource_decay_at (Mem.nextblock m) l r r' →
    access_at m l Cur = perm_of_res (resR_to_resource r) →
    access_at m' l Cur = perm_of_res (resR_to_resource r') →
    contents_cohere m' l (resR_to_resource r') →
    Mem.perm_order'' (access_at m l Max) (perm_of_res (resR_to_resource s0)) →
    contents_cohere m l (resR_to_resource s0) →
    acc_kept m m' l →
    (¬ Mem.perm m l.1 l.2 Cur Writable → contents_at m' l = contents_at m l) →
    Mem.perm_order'' (access_at m' l Max) (perm_of_res (resR_to_resource t)) ∧
    contents_cohere m' l (resR_to_resource t).
  Proof.
    intros Hvs0 Hs0 Hvt Ht Hl Hdecay Hcur Hcur' Hcont' Hmax0 Hcont0 Hacc Hcontents.
    assert (Hv0 : ✓ (r ⋅ f)) by rewrite -Hs0 //.
    assert (Hv' : ✓ (r' ⋅ f)) by rewrite -Ht //.
    rewrite (resR_to_resource_eq s0 (r ⋅ f) Hvs0 Hs0) in Hmax0 Hcont0.
    rewrite (resR_to_resource_eq t (r' ⋅ f) Hvt Ht).
    (* Cur ≤ Max in m' *)
    assert (HmaxN : access_at m' l Max = None → access_at m' l Cur = None).
    { intros HN. pose proof (Mem.access_max m' l.1 l.2) as Hmx.
      change (Mem.perm_order'' (access_at m' l Max) (access_at m' l Cur)) in Hmx.
      rewrite HN in Hmx. revert Hmx.
      destruct (access_at m' l Cur); simpl; [intros [] | auto]. }
    destruct (resource_decay_at_inv _ _ _ _ Hdecay)
      as [Hsame | [(dq & rsh & v & v' & Hr & Hr') | [Hge | (rsh & v & Hr & Hr')]]].
    - (* the cell is unchanged *)
      assert (Hvr' : ✓ r') by (eapply cmra_valid_op_l; eauto).
      assert (E1 : resR_to_resource r' = resR_to_resource r).
      { apply resR_to_resource_eq; done. }
      assert (E2 : resR_to_resource (r' ⋅ f) = resR_to_resource (r ⋅ f)).
      { apply resR_to_resource_eq; try done. by rewrite Hsame. }
      rewrite E2. split.
      + destruct Hacc as [Hk | (Hfr & HN)]; first by rewrite Hk.
        exfalso. pose proof (HmaxN HN) as HC.
        rewrite Hcur' E1 -Hcur Hfr in HC. discriminate.
      + intros v Hv.
        destruct (classic (∃ v1, (resR_to_resource r).2 = Some (VAL v1))) as [(v1 & Hv1) | Hnv].
        * (* this thread sees the value: it is the joined value *)
          destruct (resR_le r (r ⋅ f) Hv0 (cmra_included_l r f)) as [_ [Hn | Heq]].
          { rewrite Hv1 in Hn; discriminate. }
          assert (Some (VAL v1) = Some (VAL v)) as [= ->].
          { rewrite -Hv1 -Hv //. }
          apply (Hcont' v). rewrite E1 //.
        * (* no value here, so no write permission: the step cannot touch it *)
          assert (Hnw : ¬ Mem.perm m l.1 l.2 Cur Writable).
          { change (¬ Mem.perm_order' (access_at m l Cur) Writable).
            rewrite Hcur. apply perm_of_res_noVAL_not_writable.
            intros v1 Hv1; apply Hnv; by exists v1. }
          rewrite (Hcontents Hnw). apply (Hcont0 v). done.
    - (* store *)
      destruct (glob_step_store dq rsh v v' r r' f Hv0 Hv' Hr Hr') as (Hp1 & Hp2 & Hs1 & Hs2).
      split.
      + destruct Hacc as [Hk | (Hfr & HN)].
        * rewrite Hk Hp2 //.
        * exfalso. pose proof (HmaxN HN) as HC.
          rewrite Hcur' Hp1 -Hcur Hfr in HC. discriminate.
      + intros v'' Hv''. rewrite Hs2 in Hv''.
        injection Hv'' as Heqv; subst v''.
        apply (Hcont' v'). done.
    - (* alloc: impossible on an old block *)
      exfalso; lia.
    - (* free *)
      destruct (glob_step_free rsh v r r' f Hv0 Hv' Hr Hr') as [Hp Hs].
      split.
      + rewrite Hp. apply perm_order''_None.
      + intros v'' Hv''. rewrite Hs in Hv''. discriminate.
  Qed.

  Lemma resR_op_None (x : shresR) : resR_to_resource (x ⋅ None) = resR_to_resource x.
  Proof. destruct x; reflexivity. Qed.

  Lemma resource_at_op_None_r (σ1 σ2 : resource_map.rmapUR share address (leibnizO resource)) l :
    σ2 !! l = None → (σ1 ⋅ σ2) @ l = σ1 @ l.
  Proof.
    intros H. rewrite /resource_at gmap.lookup_op H.
    apply resR_op_None.
  Qed.

  Check coherent.
  Check resource_decay.
  Check glob_coherent.
  Check corestep.
  Locate rmap.
  Locate coherent.

  Lemma corestep_glob_coherent (c c' : CC_core) (m m' : mem)
    (σ σ' σ0 frame : resource_map.rmapUR share address (leibnizO resource)) :
    coherent m σ → corestep (cl_core_sem ge) c m c' m' → coherent m' σ' →
    resource_decay (Mem.nextblock m) σ σ' →
    ✓ σ0 → ✓ (σ' ⋅ frame) → σ0 ≡ σ ⋅ frame → glob_coherent m σ0 →
    glob_coherent m' (σ' ⋅ frame).
  Proof.
    intros Hcoh Hstep Hcoh' [_ Hdecay] Hv0 Hv' Hdecomp Hglob0.
    pose proof (CLC_corestep_mem ge c m c' m' Hstep) as Hmem.
    pose proof (semantics_lemmas.mem_step_nextblock' _ _ Hmem) as Hnb.
    assert (Hbf : rmap_bound (Mem.nextblock m) frame).
    { apply (rmap_bound_frame _ σ0 σ frame (glob_coherent_bound _ _ Hglob0) Hdecomp). }
    assert (Hbound' : rmap_bound (Mem.nextblock m') (σ' ⋅ frame)).
    { apply rmap_bound_op.
      - apply (coherent_rmap_bound _ _ Hcoh').
      - apply (rmap_bound_mono _ _ _ Hnb Hbf).
    }
    destruct Hglob0 as (Hlt & Hglob).
    (* old blocks *)
    assert (Hpt : ∀ b ofs, (b < Mem.nextblock m)%positive →
      Mem.perm_order'' (access_at m' (b, ofs) Max) (perm_of_res ((σ' ⋅ frame) @ (b, ofs))) ∧
      contents_cohere m' (b, ofs) ((σ' ⋅ frame) @ (b, ofs))).
    { intros b ofs Hb.
      destruct (Hcoh (b, ofs)) as (_ & _ & Hcur).
      destruct (Hcoh' (b, ofs)) as (_ & Hcont' & Hcur').
      destruct (Hglob (b, ofs)) as (_ & Hcont0 & _).
      pose proof (Hlt b ofs) as Hmax0.
      rewrite getMaxPerm_correct perm_of_rmap_lookup in Hmax0.
      assert (Hs0 : (σ0 !! (b, ofs) : shresR) ≡ (σ !! (b, ofs) : shresR) ⋅ frame !! (b, ofs)).
      { pose proof (Hdecomp (b, ofs)) as Hd. rewrite gmap.lookup_op // in Hd. }
      apply (glob_coherent_step_at m m' (b, ofs) (σ !! (b, ofs)) (σ' !! (b, ofs))
               (frame !! (b, ofs)) (σ0 !! (b, ofs)) ((σ' ⋅ frame) !! (b, ofs))); auto.
      - by rewrite gmap.lookup_op.
      - apply mem_step_acc_kept; done.
      - intros Hw. apply mem_step_contents_nonwritable; done. }
    (* Max of the new memory bounds the joined rmap *)
    assert (Hlt' : permMapLt (perm_of_rmap (σ' ⋅ frame)) (getMaxPerm m')).
    { intros b ofs. rewrite getMaxPerm_correct perm_of_rmap_lookup.
      destruct (plt b (Mem.nextblock m)) as [Hb | Hb].
      - apply (proj1 (Hpt b ofs Hb)).
      - rewrite resource_at_op_None_r; last (apply Hbf; simpl; unfold Plt in Hb; lia).
        destruct (Hcoh' (b, ofs)) as (_ & _ & Hcur').
        rewrite /access_cohere in Hcur'.
        rewrite -Hcur'.
        apply (Mem.access_max m' b ofs).
    }
    exists Hlt'.
    intros (b, ofs). split; [|split].
    - intros Hge; auto.
    - intros v Hv.
      change (contents_at m' (b, ofs) = v).
      destruct (plt b (Mem.nextblock m)) as [Hb | Hb].
      + apply (proj2 (Hpt b ofs Hb) v Hv).
      + rewrite resource_at_op_None_r in Hv; last (apply Hbf; simpl; unfold Plt in Hb; lia).
        destruct (Hcoh' (b, ofs)) as (_ & Hcont' & _).
        apply (Hcont' v Hv).
    - rewrite /access_cohere access_at_restrPermMap_perm_res //.
  Qed.

  Lemma corestep_local : forall (c : CC_core) (m : mem) (σ : resource_map.rmapUR share address (leibnizO resource)) c' m'
                           (σ' : resource_map.rmapUR share address (leibnizO resource)),
      coherent m σ → corestep (cl_core_sem ge) c m c' m' → coherent m' σ' →
      resource_decay (Mem.nextblock m) σ σ' →
      ∀ σ0 : resource_map.rmapUR share address (leibnizO resource),
        ✓ σ0 → glob_coherent m σ0 → rmap_included σ σ0 →
        ∃ (σ0' : resource_map.rmapUR share address (leibnizO resource)),
          rmap_local_update σ0 σ σ0' σ' /\ glob_coherent m' σ0'.
  Proof.
    intros c m σ c' m' σ' Hcoh Hstep Hcoh' Hdecay σ0 Hv0 Hglob Hincl.
    destruct Hincl as (frame & Hdecomp).
    assert (Hbf : rmap_bound (Mem.nextblock m) frame).
    { apply (rmap_bound_frame _ σ0 σ frame (glob_coherent_bound _ _ Hglob) Hdecomp). }
    assert (Hupd : rmap_local_update σ0 σ (σ' ⋅ frame) σ').
    { apply (resource_decay_join_local_update _ σ σ' frame σ0 Hbf Hdecomp Hdecay). }
    assert (Hv' : ✓ (σ' ⋅ frame)).
    { apply cmra_valid_validN; intros n.
      assert (Hvn : ✓{n} σ0) by (by apply cmra_valid_validN).
      assert (Hdn : σ0 ≡{n}≡ σ ⋅? Some frame) by (by apply equiv_dist).
      apply (proj1 (Hupd n (Some frame) Hvn Hdn)). }
    exists (σ' ⋅ frame); split; first done.
    apply (corestep_glob_coherent c c' m m' σ σ' σ0 frame Hcoh Hstep Hcoh' Hdecay Hv0 Hv' Hdecomp Hglob).
  Qed.

  Print Assumptions corestep_local.

  Local Instance raw_rmapUR_ora_discrete : OraDiscrete (uora_oraR raw_rmapUR).
  Proof.
    unfold raw_rmapUR, resource_map.rmapUR.
    apply gmap_ora_discrete, shared.shared_discrete, _.
  Qed.

  Local Instance raw_rmapR_discrete : CmraDiscrete raw_rmapR.
  Proof.
    unfold raw_rmapR.
    apply (ora_cmra_discrete (A := uora_oraR raw_rmapUR)).
  Qed.

  Lemma rmap_auth_frag_included γ σ0 σ :
    rmap_auth γ σ0 ∗ rmap_frag γ σ ⊢ ⌜rmap_included σ σ0⌝.
  Proof.
    rewrite /rmap_auth /rmap_frag.
    iIntros "(Ha & Hf)".
    iDestruct (own_valid_2 with "Ha Hf") as %Hv.
    apply (auth_both_valid_discrete (A := raw_rmapR)) in Hv as [Hincl _].
    iPureIntro; done.
  Qed.

  Lemma rmap_auth_valid γ σ0 :
    rmap_auth γ σ0 ⊢ ⌜✓ (σ0 : resource_map.rmapUR share address (leibnizO resource))⌝.
  Proof.
    rewrite /rmap_auth; iIntros "H".
    iDestruct (own_valid with "H") as %Hv.
    iPureIntro.
    apply (auth_auth_valid (A := raw_rmapR)) in Hv; auto.
  Qed.

  

  (* jsafe runs with permissions that are lower-bounded by resource_map_auth. In general, this
     means the combined permissions of all the threads, not the permissions of a single thread.
     But in the initial condition we happen to know that there is only one thread.
     However, this is not preserved by induction: what is the inductive property? *)
  (* Thought 1: jsafe always insists that the memory has at least as many permissions as
     the authoritative rmap. So it doesn't make sense to have a single authoritative rmap
     across all threads. We need to go back to conc_rmap. *)
  (* Thought 2: when we call spawn, it returns a new memory and rmap that have given up
     some resources. This no longer represents the true global memory. So the auth rmap
     doesn't represent the full memory even in sequential safety. *)
  (* Maybe the rmap in resource_map_auth isn't really the logical rmap of the thread at all?
     Rather, it's an upper bound on it, where the rmap itself is provided by the assertions. *)
  (* Maybe rmap_auth is the real full rmap, and the auth used in jsafe is a subsidiary one? *)
  Lemma jsafe_jsafe_frag: forall γ γi E z c,
      jsafe (genv_symb := genv_symb_injective) (cl_core_sem ge) (concurrent_ext_spec CS ext_link) ge
        (gen_heapGS0 := thread_gen_heapGS γi) E z c
        ⊢ jsafe_frag γ γi E z c.
  Proof.
    intros.
    iLöb as "IH" forall (z c).
    rewrite jsafe_unfold jsafe_frag_unfold /jsafe_pre /jsafe_frag_pre.
    iIntros ">H !>" (m σ) "S".
    rewrite /thread_state_interp /thread_mem_auth /thread_rmap.
    iDestruct "S" as (σ0) "(%Hbound & (Hauth & E) & %Hcoh & Hfrag & M)".
    iDestruct ("H" with "[$M $E]") as "[Hhalt | [Hstep | Hextcase]]"; first done.
    - (* halted *)
      iLeft; iDestruct "Hhalt" as (i) "(%Hhalt & ((_ & M) & E) & Hexit)".
      iExists i; iSplit; first done.
      iFrame "Hexit".
      iSplitL; last done.
      iExists σ0; iSplit; first done.
      iSplitL "Hauth E".
      { rewrite /conc_state_interp; iFrame. }
      iSplit; first done.
      iFrame.
    - (* core step *)
      iRight; iLeft; iMod "Hstep" as (c' m' σ' [Hstep Hdecay]) "(S & H)".
      iDestruct "S" as "((%Hcoh' & M) & E)".
      iDestruct (rmap_auth_valid with "Hauth") as %Hv0.
      iDestruct (rmap_auth_frag_included with "[$Hauth $Hfrag]") as %Hincl.
      destruct (corestep_local c m σ c' m' σ' Hcoh Hstep Hcoh' Hdecay σ0 Hv0 Hbound Hincl)
        as (σ0' & Hupd & Hglob').
      iMod (own_update_2 with "Hauth Hfrag") as "(Hauth & Hfrag)"; first by apply auth_update.
      iModIntro; iExists c', m', σ'.
      iSplit; first done.
      iSplitR "H".
      { iExists σ0'; iSplit; [done | iFrame; try done]. }
      by iApply "IH".
    - (* external call *)
      iRight; iRight.
      iDestruct "Hextcase" as (e args x) "(%Hat & S & Hpre & Hk)".
      iDestruct "S" as "((_ & M) & E)".
      iExists e, args, x; iSplit; first done.
      iFrame "Hpre".
      iSplitR "Hk".
      { iExists σ0; iSplit; [done | iFrame; try done]. }
      iIntros "!>" (ret m' σ' z') "%Htypes".
      iMod ("Hk" $! ret m' σ' z' with "[//]") as "Hk".
      iIntros "!> S Hpost".
      iDestruct "S" as (σ1) "(%Hb1 & (Hauth & E) & %Hc1 & Hfrag & M)".
      iDestruct ("Hk" with "[$M $E] Hpost") as (c') "(%Hafter & S & H)"; first done.
      iDestruct "S" as "((_ & M) & E)".
      iModIntro; iExists c'; iSplit; first done.
      iSplitR "H".
      { iExists σ1; iSplit; [done | iFrame; try done]. }
      by iApply "IH".
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
    forall l, (l ∈ ls -> lockRes tp l <> None /\
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

  Lemma mem_step_preserves_lock_bytes : forall m m' (l : address),
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
      { unfold Mem.perm.
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

  Lemma lock_state_empty_change m1 m2 : lock_state m1 ∅ ⊢ lock_state m2 ∅.
  Proof.
    iIntros "H".
    iDestruct "H" as (I) "((%Hdom & %Hdisjoint) & Hauth & HI)".
    apply dom_empty_inv_L in Hdom.
    subst I.
    iExists ∅.
    iFrame.
    iSplit; auto.
  Qed.

  Lemma lock_state_mem_change (m m' : mem) (ls : gset address)
    (Hload : forall l, l ∈ ls ->
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

  (*Lemma rmap_frag_lock_transfer `{!inG Σ rmap_authUR} (γ : gname) (σ σlock : raw_rmapR) : rmap_frag γ σ ∗ rmap_frag γ σlock ⊣⊢
      rmap_frag γ (σ ⋅ σlock) ∗ rmap_frag γ (∅ : raw_rmapR).
  Proof.
    rewrite /rmap_frag -!own_op.
    apply own_proper.
    rewrite -!frac_auth_frag_op.
    by rewrite right_id.
  Qed.*)

  Definition rmapAuthT : ora := resource_map.rmap_authR share address (leibnizO resource).

  Definition rmapOwnInG : inG Σ rmapAuthT := @resource_map.resource_map_inG Σ share _ address _ _ resource (gen_heapGpreS_heap (gen_heapGpreS := gen_heap_inG)).

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
  
  Lemma perm_of_sh_writable0_not_top sh (Hw : shares.writable0_share sh)
    (Htop : sh <> Share.top) : perm_of_sh sh = Some Writable.
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

  Definition thread_safe (tp : dtp) i γ γi :=
    ∃ (cnti : containsThread tp i),
      match getThreadC cnti with
      | Krun c | Kblocked c => jsafe_frag γ γi ⊤ tt c
      | Kresume c v =>
          ∀ c',
            (* [v] is not used here. The problem is probably coming from
           the definition of JuicyMachine.resume_thread'. *)
            ⌜cl_after_external None c = Some c'⌝ →
            jsafe_frag γ γi ⊤ tt c'
      | Kinit v1 v2 =>
          ∃ q_new,
    ⌜cl_initial_core ge v1 (v2 :: nil) = Some q_new⌝ ∧
      ▷ jsafe_frag γ γi ⊤ tt q_new
  end%I.

  Definition threads_safe `{rmap_inG : inG Σ rmap_authUR}
    (tp : dtp) (γ : gname): iProp Σ :=
    [∗ list] _ ↦ i ∈ seq 0 (pos.n (OrdinalPool.num_threads tp)),
      ∃ γi (σ : rmap) (cnti : containsThread tp i),
        <affine>⌜mem_equiv.access_map_equiv (perm_of_rmap σ) (getThreadR cnti)⌝ ∗
                  thread_safe tp i γ γi ∗ thread_rmap γ γi σ.

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
            (∃ γi (σ : rmap) (cnti : containsThread tp y),
                <affine>⌜mem_equiv.access_map_equiv (perm_of_rmap σ) (getThreadR cnti)⌝ ∗
                          thread_safe tp y γ γi ∗ thread_rmap γ γi σ) -∗ Ψ k y) -∗ Ψ i i -∗ [∗ list] k↦y ∈ seq 0 (pos.n (OrdinalPool.num_threads tp)), Ψ k y.
  
  Definition post_safe (γ : gname) γi {e}
    (x : Jext_spec_type (concurrent_ext_spec CS ext_link) e)
    (argsty : typelist) (retty : type) (cc : calling_convention) (args : list val) (k : cont) :=
    ∀ (ret : option val) (m' : mem) (σ' : rmap) (z' : unit),
      ⌜Val.has_type_list args (sig_args (ef_sig e)) ∧
        Builtins0.val_opt_has_rettype ret (sig_res (ef_sig e))⌝ →
      |={⊤}=> thread_state_interp γ γi m' σ' z' -∗ Jext_spec_post (concurrent_ext_spec CS ext_link) e x (genv_symb_injective ge) (sig_res (ef_sig e)) ret ={⊤}=∗
   ∃ (c' : CC_core),⌜after_external (cl_core_sem ge) ret (Callstate (Ctypes.External e argsty retty cc) args k) m' = Some c'⌝ ∧ thread_state_interp γ γi m' σ' z' ∗ jsafe_frag γ γi ⊤ z' c'.

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

  (*Lemma rmap_auth_frag_acquire_update `{!inG Σ rmap_authUR} (γ : gname) (q : Qp)
    (σcur σ1 σlock : raw_rmapR) : ✓ (σcur ⋅ σlock) →
    rmap_auth γ σcur ∗ rmap_frag γ σ1 ==∗
    rmap_auth γ (σcur ⋅ σlock) ∗ rmap_frag γ q (σ1 ⋅ σlock).
  Proof.
    intros Hvalid.
    rewrite /rmap_auth /rmap_frag.
    iIntros "(Hauth & Hfrag)".
    iMod (own_update_2 with "Hauth Hfrag") as "(Hauth & Hfrag)".
    { apply frac_auth_update.
      by apply rmap_add_local_update. }
    iFrame. done.
  Qed.*)
  
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
    ✓ σcur -> rmap_auth γ σcur ∗ rmap_frag γ σ ⊢
               ⌜✓ σ ∧ permMapLt (perm_of_rmap σ) (perm_of_rmap σcur)⌝.
  Proof.
    intros Hvcur.
    rewrite /rmap_auth /rmap_frag.
    iIntros "(Ha & Hf)".
    iPoseProof (own_valid_2 with "Ha Hf") as "Hvalid".
    Locate auth_both_validI.
    (*iPoseProof (base_logic.algebra.auth_both_validI (A := raw_rmapR) σcur σ with "Hvalid") as "Hrel".
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
  Qed.*) Abort.

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
(*    iDestruct "Hmem" as (Hlt0) "(%Hcoh & Hm)".
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
  Qed.*) Admitted.
    
  Lemma lock_acquire_rmap_update `{!VSTGS () Σ} `{!lockGS Σ} `{!inG Σ rmap_authUR}
    (γ : gname) (q : Qp) (m : mem) (ls : gset address) (IR : address -> option access_map)
    (l : val) (l1 : address) (sh : share)
    (R : oFunctor_car (dependent_type_functor_rec Mpred) (iProp Σ) (iProp Σ))
    (σcur σ1 : rmap) (Hval : val2adr l l1)
    (Hload : Mem_load_unchecked Mptr m l1.1 l1.2 = Vptrofs Ptrofs.one)
    (Hofs : Ptrofs.Z_mod_modulus l1.2 = l1.2)
    (Hltσcur : permMapLt (perm_of_rmap σcur) (getMaxPerm m))
    (Hσcur : coherent (restrPermMap Hltσcur) σcur) :
    let σ1R := (σ1 : resource_map.rmapUR share address (leibnizO resource)) in
    let m_global' := Mem_store_unchecked Mptr m l1.1 (Ptrofs.intval (Ptrofs.repr l1.2)) (Vptrofs Ptrofs.zero) in
    let IR' : address -> option access_map :=
      fun a => if decide (a = l1) then Some empty_map else IR a in
    lock_inv sh l R -∗ lock_state1 γ m ls IR -∗
    resource_map.resource_map_auth (H1 := gen_heapGpreS_heap (gen_heapGpreS := gen_heap_inG)) (gen_heap_name heapGS_gen_heapGS) 1 σcur -∗ rmap_auth γ σcur -∗ rmap_frag γ σ1 ==∗
    ∃ σlock σnew : rmap, ⌜✓ (σ1R ⋅ σlock) ∧
                           exists l0 : access_map, IR l1 = Some l0 ∧ mem_equiv.access_map_equiv l0 (perm_of_rmap σlock) ∧ lock_rmap_nonempty_on ls σlock⌝ ∧
    ∃ Hlt_store : permMapLt (perm_of_rmap (σ1R ⋅ σlock)) (getMaxPerm m_global'),
      frag_mem_auth (restrPermMap Hlt_store) σnew ∗ rmap_auth γ σnew ∗ rmap_frag γ (σ1R ⋅ σlock)
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
    - iDestruct "Hhere" as (σlock l0) "(Hlockfrag & (%HIRl1 & %Heq_lock & %Hload0 & %Hσlock_locks) & HR)".
      subst Q.
      simpl.
      iAssert (▷ R)%I with "[Heq HR]" as "HR".
      { iNext. by iRewrite "Heq" in "HR". }
      iCombine "Hfrag Hlockfrag" as "Hfrag".
      iAssert (lock_state1 γ m_global' ls IR')%I with "[HI Hrest]" as "Hls".
      { rewrite /lock_state1.
        iExists I.
        iFrame "HI".
        iSplit.
        { iPureIntro. split; auto. }
        rewrite {1} (big_sepM_delete _ _ l1 R0 HIR0).
        iSplitR.
        + iRight.
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
        - iDestruct "Hk" as (σlock0 l00)
                              "(Hf & (%HIR0_lock & %Heq0 & %Hone & %Hnonempty0) & Hy)".
            iLeft.
            iExists σlock0, l00.
            iFrame.
            iPureIntro.
            repeat split; auto.
            { by rewrite HIR_same. }
            by rewrite Hsame.
          - iDestruct "Hk" as "(%HIR0_empty & %Hzero)".
            iRight.
            iFrame.
            iPureIntro.
            split. by rewrite HIR_same.
            by rewrite Hsame.
      }
      iAssert (lock_inv sh l R)%I with "[Hlk Hi]" as "Hl".
      { rewrite /lock_inv. iExists l1. by iFrame. }
      iDestruct (resource_map.resource_map_auth_valid with "Hrs") as %(_ & Hvcur).
      (*iDestruct (rmap_auth_frag_permMapLt_valid γ q σcur (σ1 ⋅ σlock) Hvcur
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
(*        iExists Hlt_pre.
        iFrame "Hrs".
        by iPureIntro. *) admit.
      }
      (* Store 0 into the lock and preserve frag_mem_auth. *)
      iMod (frag_mem_auth_store_unchecked_lock_zero_restr m σcur Hltσcur sh l1.1 l1.2 (Vptrofs Ptrofs.zero) with "Hmem_pre HLK") as (Hlt_post_local) "[Hmem_post_local HLK]".
      (* Extract post-store coherence from that frag_mem_auth. *)
      rewrite /frag_mem_auth.
(*      iDestruct "Hmem_post_local" as (Hlt_inner) "(%Hcoh_inner & Hrs)".
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
  Qed. *)*) Admitted.

  Lemma frag_mem_auth_restr_to_global `{!VSTGS () Σ} (m : mem) (p : access_map)
    (Hlt : permMapLt p (getMaxPerm m)) (σ : rmap) :
    frag_mem_auth (restrPermMap Hlt) σ ⊢ frag_mem_auth m σ.
  Proof.
    rewrite /frag_mem_auth.
    iIntros "H".
(*    iDestruct "H" as (Hlt') "(%Hcoh & Hauth)".
    pose proof (permMapLt_restr Hlt') as Hlt_global.
    iExists Hlt_global.
    iFrame.
    iPureIntro.
    split; auto.
    replace (restrPermMap Hlt_global) with (restrPermMap (permMapLt_restr Hlt')).
    - by rewrite <- (restrPermMap_idem Hlt').
    - apply restr_proof_irr.
  Qed. *) Admitted.

  Lemma permjoin_perm_union_exists_no_WR
    (p q r : option permission) :
    permjoin_def.permjoin p q r ->
    ~ (p = Some Writable /\ q = Some Readable) ->
    ~ (p = Some Readable /\ q = Some Writable) ->
    exists u, perm_union p q = Some u.
  Proof.
    intros Hj HWR HRW.
    destruct p as [p |];
      destruct q as [q |].
    - destruct p; destruct q;
        simpl in *;
        try solve [eexists; reflexivity];
        try solve [inversion Hj];
        try solve [
            exfalso; apply HWR; split; reflexivity
          ];
        try solve [
            exfalso; apply HRW; split; reflexivity
          ].
    - eexists; reflexivity.
    - eexists; reflexivity.
    - eexists; reflexivity.
  Qed.

  Definition writable_dfrac (dq : dshare.dfrac) : Prop :=
    match dq with
    | dshare.DfracOwn (Share sh) => writable0_share sh
    | _ => False
    end.

  Lemma lookup_Some_VAL_from_perm_Writable σ loc :
    ✓ (σ : resource_map.rmapUR _ _ _) -> perm_of_res (σ @ loc) = Some Writable ->
    exists (dq : dshare.dfrac) (rsh : readable_dfrac dq) (v0 : agree (leibnizO resource)),
    σ !! loc = Some (shared.YES dq rsh v0) /\ writable_dfrac dq.
 Proof.
   intros Hv HW.
   rewrite /resource_at /resR_to_resource in HW.

   destruct (σ !! loc) as [s |] eqn:Hlk.
   - destruct s as [dq rsh v0 | sh0 rsh0].
    + (* YES *)
      exists dq, rsh, v0.
      split; auto.
      destruct dq as [sc | sc].
      * (* DfracOwn *)
        destruct sc as [sh |].
        -- (* DfracOwn (Share sh) *)
           rewrite Hlk in HW.
           simpl in HW.
           destruct (resource_map.elem_of_agree (A := leibnizO resource) v0) as [x Hx] eqn:He.
           rewrite He in HW.
           destruct x; simpl in HW.
           ++ rewrite /perm_of_sh in HW.
              repeat if_tac in HW;
                try contradiction;
                try discriminate;
                assumption.
           ++ destruct (eq_dec sh Share.bot);
                discriminate.
           ++ destruct (eq_dec sh Share.bot);
                discriminate.
        -- (* DfracOwn ShareBot *)
           simpl in rsh.
           contradiction.
      * (* DfracBoth *)
        destruct sc as [sh |].
        -- (* DfracBoth (Share sh) *)
           exfalso.
           pose proof Hv as Hv1.
           specialize (Hv1 loc).
           rewrite Hlk Some_valid in Hv1.
           apply shared.shared_valid in Hv1 as [Hdq _].
           change (✓ dshare.DfracBoth (Share sh)) in Hdq.
           destruct Hdq as (sh' & Hsh' & Hnw).
           inversion Hsh'; subst sh'; clear Hsh'.
           change (~ writable0_share sh) in Hnw.
           simpl in HW.
           destruct (resource_map.elem_of_agree (A := leibnizO resource) v0) as [x Hx] eqn:He.
           rewrite Hlk in HW.
           simpl in HW.
           rewrite He in HW.
           destruct x; simpl in HW.
           ++ rewrite (perm_of_sh_clamped_readable sh Hnw) in HW.
              discriminate.
           ++ discriminate.
           ++ discriminate.
        -- (* DfracBoth ShareBot *)
           simpl in rsh.
           contradiction.
    + (* NO *)
      destruct sh0 as [sh |].
      * simpl in HW.
        rewrite Hlk in HW.
        cbn [resR_to_resource shared.dfrac_of shared.val_of option_map] in HW.
        rewrite /perm_of_res /perm_of_sh' /perm_of_sh in HW.
        destruct (writable0_share_dec sh) as [Hw | Hnw].
        ++ exfalso.
           apply rsh0.
           change (readable_share sh).
           by apply writable0_readable.
        ++ repeat if_tac in HW;
             try contradiction;
             discriminate.
      * simpl in HW.
        rewrite Hlk in HW.
        simpl in HW. inv HW.
  - (* lookup = None *)
    simpl in HW.
    destruct (eq_dec Share.bot Share.bot) as [_ | Hneq].
    + rewrite Hlk in HW. simpl in HW. if_tac in HW. inv HW. inv HW.
    + contradiction.
 Qed.
 

  Lemma lookup_Some_VAL_from_perm_Readable σ loc :
    perm_of_res (σ @ loc) = Some Readable ->
    exists (dq : dshare.dfrac)
           (rsh : readable_dfrac dq)
           (v0 : agree (leibnizO resource)),
      σ !! loc = Some (shared.YES dq rsh v0).
  Proof.
    rewrite /resource_at /resR_to_resource.
    destruct (σ !! loc) as [s |] eqn:Hlk; simpl.
    - destruct s as [dq rsh v0 | sh rsh].
      + intros _.
        exists dq, rsh, v0. done.
      + intros H.
        rewrite /perm_of_res in H.
        destruct sh as [sh |]; simpl in H;
          repeat if_tac in H; try discriminate.
    - intros H.
      rewrite /perm_of_res in H.
      repeat if_tac in H; try discriminate.
  Qed.

  Lemma writable_readable_dfrac_excl dq1 dq :
    writable_dfrac dq1 -> readable_dfrac dq -> ~ ✓ (dq1 ⋅ dq).
  Proof.
    intros Hw Hr.
    assert (Hwdf : forall dq, writable_dfrac dq ->
                         exists sh, dq = dshare.DfracOwn (Share sh) /\ writable0_share sh).
    { intros dq0 Hw0.
      destruct dq0; destruct s; try done.
      by exists sh.
    }
    apply Hwdf in Hw.
    destruct Hw as (sh & Heq & Hw).
    intros Hcontra.
    subst dq1.
    rewrite ora_comm in Hcontra.
    apply dfrac_valid_own_readable in Hcontra; auto.
    destruct Hcontra as (sh' & Hsh & Hnw).
    by inv Hsh.
  Qed.

  Lemma valid_rmap_op_not_WR (σ1 σ2 : resource_map.rmapUR share address (leibnizO resource))
    (b : positive) (ofs : Z) (Hvalid : ✓ (σ1 ⋅ σ2)) :
    ~ ((perm_of_rmap σ1) # b ofs = Some Writable /\ (perm_of_rmap σ2) # b ofs = Some Readable).
  Proof.
    intros [HW HR].
    rewrite perm_of_rmap_lookup in HW.
    rewrite perm_of_rmap_lookup in HR.
    assert (Hv1 : ✓ σ1).
    { eapply cmra_valid_op_l; exact Hvalid. }
    assert (Hv2 : ✓ σ2).
    { eapply cmra_valid_op_r; exact Hvalid. }
    destruct (lookup_Some_VAL_from_perm_Writable σ1 (b, ofs) Hv1 HW)
      as (dq1 & rsh1 & v1 & Hlk1 & Hw1).
    destruct (lookup_Some_VAL_from_perm_Readable σ2 (b, ofs) HR)
      as (dq2 & rsh2 & v2 & Hlk2).
    pose proof Hvalid as Hv.
    specialize (Hv (b, ofs)).
    rewrite gmap.lookup_op in Hv.
    rewrite Hlk1 Hlk2 in Hv.
    rewrite -Some_op in Hv.
    rewrite shared.YES_op' in Hv.
    destruct (shared.readable_dfrac_dec (dq1 ⋅ dq2)) as [rsh12 | Hnread] eqn:Hdec.
    - rewrite Some_valid in Hv.
      apply shared.shared_valid in Hv as [Hdq _].
      eapply (writable_readable_dfrac_excl dq1 dq2); auto.
    - rewrite Some_valid in Hv; done.
  Qed.

  Lemma perm_of_rmap_op_permMapsDisjoint
    (σ0R σlock : resource_map.rmapUR share address (leibnizO resource))
    (Hvalid : ✓ (σ0R ⋅ σlock)) :
    permMapsDisjoint (perm_of_rmap σlock) (perm_of_rmap σ0R).
  Proof.
    unfold permMapsDisjoint.
    intros b ofs.
    pose proof ((perm_of_rmap_op_permMapJoin σ0R σlock Hvalid) b ofs) as Hj.
    eapply permjoin_perm_union_exists_no_WR; auto.
    - apply Hj.
    - intros [HW HR].
      eapply (valid_rmap_op_not_WR σlock σ0R b ofs); auto.
      rewrite comm; done.
    - intros [HR HW].
      eapply (valid_rmap_op_not_WR σ0R σlock b ofs); auto.
  Qed.

  Lemma two_rmap_frags_disjoint `{!inG Σ rmap_authUR} (γ : gname)
    (σcur σ1 σ2 : resource_map.rmapUR share address (leibnizO resource))
    (p1 p2 : access_map) (Hcur : ✓ σcur)
    (Heq1 : mem_equiv.access_map_equiv (perm_of_rmap σ1) p1)
    (Heq2 : mem_equiv.access_map_equiv (perm_of_rmap σ2) p2) :
    rmap_frag γ σ1 ∗ rmap_frag γ σ2 ⊢ ⌜permMapsDisjoint p1 p2⌝.
  Proof.
    (*iIntros "H".
    iPoseProof (rmap_auth_two_frags_valid γ σcur σ1 σ2 q1 q2 Hcur with "H") as "%Hv".
    iPureIntro.
    assert (Hv' : ✓ (σ2 ⋅ σ1)).
    { by rewrite comm. }
    pose proof (perm_of_rmap_op_permMapsDisjoint σ2 σ1 Hv') as Hd.
    unfold permMapsDisjoint in Hd |- *.
    intros b ofs.
    specialize (Hd b ofs).
    destruct Hd as [pu Hpu].
    exists pu.
    rewrite <- (Heq1 b).
    by rewrite <- (Heq2 b).
  Qed.*) Admitted.

  (* Lemma other_threads_post_disjoint (γ : gname) (tp : dtp) (i : nat)
    (σcur σpost : resource_map.rmapUR share address (leibnizO resource))
    (pnew : access_map) (Hcur : ✓ σcur)
    (Heqpost : mem_equiv.access_map_equiv (perm_of_rmap σpost) pnew) :
    rmap_auth γ σcur ∗ rmap_frag γ σpost ∗ other_threads_safe γ tp i ⊢
      ⌜∀ (j : nat) (cntj : containsThread tp j),
        i ≠ j -> permMapsDisjoint pnew (getThreadR cntj)⌝.
  Proof.
    iIntros "(Hauth & Hpost & Hsafe)".
    rewrite bi.pure_forall.
    iIntros (j).
    rewrite bi.pure_forall.
    iIntros (cntj).
    rewrite bi.pure_impl.
    iIntros "%Hneq".
    set (Ψ := fun (k y : nat) =>
                if decide (k = j) then (rmap_auth γ σcur -∗ rmap_frag γ σpost -∗ ⌜permMapsDisjoint pnew (getThreadR cntj)⌝)%I else True%I).
    iAssert ([∗ list] k↦y ∈ seq 0 (pos.n (OrdinalPool.num_threads tp)), Ψ k y)%I
      with "[Hsafe]" as "Hall".
    { iApply ("Hsafe" $! Ψ).
      - iIntros "!>" (k y (-> & Hk)%lookup_seq Hki) "Hy".
        rewrite /Ψ.
        destruct (decide (k = j)) as [Hkj | Hkj]; auto.
        subst k.
        iIntros "Ha Hp".
        iDestruct "Hy" as (γ0 σ0 cnt0) "(%Heq0 & Hsafe0 & Hfrag0)".
        replace cnt0 with cntj by apply proof_irrelevance.
        replace (0 + j) with j in cnt0 by lia.
        assert (Hcnt : cnt0 = cntj) by apply proof_irrelevance.
        subst cnt0.
        iDestruct (two_rmap_frags_disjoint γ σcur σpost σ0 pnew (getThreadR cntj)
                      with "[$Hp $Hfrag0]") as "$"; auto.
     - rewrite /Ψ.
       rewrite decide_False; done.
    }
    iDestruct (big_sepL_lookup_acc Ψ (seq 0 (pos.n (OrdinalPool.num_threads tp))) j j
              with "Hall") as "[Hj _]".
    { apply lookup_seq.
      pose proof cntj as Hjlt.
      rewrite /containsThread /= /OrdinalPool.containsThread in Hjlt.
      split; auto.
      pose proof (@ssrnat.leP (S j) (pos.n (OrdinalPool.num_threads tp))) as Hle.
      inv Hle; [lia | congruence].
    }
   rewrite /Ψ decide_True; last done.
   iApply ("Hj" with "Hauth Hpost").
  Qed.

  Lemma lock_resources_post_disjoint (γ : gname) (m : mem) (ls : gset address)
    (IR : address -> option access_map)
    (σcur σpost : resource_map.rmapUR share address (leibnizO resource))
    (q : Qp) (pnew : access_map)
    (Hcur : ✓ σcur)
    (Heqpost : mem_equiv.access_map_equiv (perm_of_rmap σpost) pnew)
    (HIRdom : forall a r, IR a = Some r -> a ∈ ls):
  rmap_auth γ σcur ∗ rmap_frag γ q σpost ∗ lock_state1 γ m ls IR ⊢
  ⌜ forall a r, IR a = Some r -> permMapsDisjoint pnew r⌝.
 Proof.
  iIntros "(Hauth & Hpost & Hls)".
  rewrite /lock_state1.
  iDestruct "Hls" as (I) "((%Hdom & %Hdisj) & Hown & Hmap)".
  (* modify later lock_state1 *)
  destruct (classic (forall a r, IR a = Some r -> permMapsDisjoint pnew r)) as [Hall | Hbad].
  - by iPureIntro.
  - apply Classical_Pred_Type.not_all_ex_not in Hbad.
    destruct Hbad as [a Hbad].
    apply Classical_Pred_Type.not_all_ex_not in Hbad.
    destruct Hbad as [r Hbad].
    assert (HIR : IR a = Some r).
    { destruct (classic (IR a = Some r)) as [HIR | HIR]; auto.
      exfalso. apply Hbad. intros H. done. }
    assert (Hnd : ~ permMapsDisjoint pnew r).
    { intro HD. apply Hbad. intros _. apply HD. }
    assert (Ha : a ∈ dom I).
    { rewrite Hdom. apply (HIRdom a r HIR). }
    rewrite elem_of_dom in Ha.
    destruct Ha as (R0 & HR0).
    iDestruct (big_sepM_lookup_acc _ I a R0 HR0 with "Hmap") as "[Ha Hclose]".
    iDestruct "Ha" as "[Hunlocked | Hlocked]".
    + iDestruct "Hunlocked" as (qL σlock l0) "(HfragL & (%HIR0 & %HeqL & %Hload) & HR)".
      assert (Hl0 : l0 = r) by congruence.
      subst l0.
      assert (HeqL' : mem_equiv.access_map_equiv (perm_of_rmap σlock) r).
      { intros b.
        symmetry.
        apply (HeqL b).
      }
      iDestruct (two_rmap_frags_disjoint γ σcur σpost σlock q qL pnew r
           with "[$Hauth $Hpost $HfragL]") as "%HD"; auto.
    + iDestruct "Hlocked" as (qL) "(HfragL & (%HIR0 & %Hload))".
      assert (Hr : r = empty_map) by congruence.
      subst r.
      assert (HeqEmpty : mem_equiv.access_map_equiv (perm_of_rmap (∅ : raw_rmapR)) empty_map).
      { intros b; done. }
      iDestruct (two_rmap_frags_disjoint γ σcur σpost (∅ : raw_rmapR) q qL pnew empty_map
           with "[$Hauth $Hpost $HfragL]") as "%HD"; auto.
  Qed.

  Lemma permjoin_nonempty_bound : forall p q r,
    permjoin_def.permjoin p q r -> Mem.perm_order'' (Some Nonempty) p ->
    Mem.perm_order'' (Some Nonempty) q -> Mem.perm_order'' (Some Nonempty) r.
  Proof.
    intros p q r Hj.
    induction Hj; intros Hp Hq; try assumption; try inversion Hp; try inversion Hq.
  Qed.

  Lemma getMaxPerm_store_unchecked : forall chunk (m : mem) b ofs v,
      getMaxPerm (Mem_store_unchecked chunk m b ofs v) = getMaxPerm m.
  Proof. intros. reflexivity. Qed.

  Lemma mem_compatible_acquire_update (tp : dtp) (m : mem)
    (i : nat) (cnti : containsThread tp i) (c : @semC Sem)
    (newThreadPerm : access_map) (l : address) (old : lock_info)
    (Hcompat : mem_compatible tp m)
    (Hnew : permMapLt newThreadPerm (getMaxPerm (Mem_store_unchecked Mptr m l.1 l.2 (Vptrofs Ptrofs.zero)))) (Hlock : lockRes tp l = Some old) :
  mem_compatible (updLockSet (updThread cnti (Kresume c Vundef) newThreadPerm) l empty_map)
    (Mem_store_unchecked Mptr m l.1 l.2 (Vptrofs Ptrofs.zero)).
  Proof.
    eapply Build_mem_compatible.
    - (* threads *)
      intros j cntj.
      pose proof (cntUpdateL' _  _ cntj) as cntj_upd.
      rewrite (gLockSetRes _ _ cntj_upd cntj).
      destruct (Nat.eq_dec j i) as [-> | Hneq].
      + by rewrite (gssThreadRes cnti (Kresume c Vundef) newThreadPerm cntj_upd).
      + assert (cntj_old : containsThread tp j).
        { by eapply cntUpdate'. }
        erewrite @gsoThreadRes with (cntj := cntj_old); eauto.
        rewrite getMaxPerm_store_unchecked.
        apply (compat_th tp m Hcompat cntj_old).
    - (* lock resources *)
      intros l' rmap Hres.
      destruct (eq_dec l' l) as [-> | Hneq].
      + rewrite gssLockRes in Hres.
        inversion Hres; subst.
        apply empty_LT.
      + rewrite gsoLockRes in Hres; auto.
        rewrite gsoThreadLPool in Hres.
        rewrite getMaxPerm_store_unchecked.
        eapply compat_lp; eauto.
    - (* valid blocks *)
      intros l' rmap Hres.
      destruct (eq_dec l' l) as [-> | Hneq].
      + pose proof (lockRes_blocks tp m Hcompat l old Hlock) as Hv.
        unfold Mem.valid_block in *.
        simpl; done.
      + rewrite gsoLockRes in Hres; auto.
        rewrite gsoThreadLPool in Hres.
        pose proof (lockRes_blocks tp m Hcompat l' rmap Hres) as Hv.
        unfold Mem.valid_block in *.
        simpl. done.
  Qed. *)

  (*
    Each time spawn needs matchfunspecs. code_bank doesn't store matchfunspecs directly.
    It stores a splittable fractional auth. 
    Each spawn can:
    - Open the invariant and obtain funspec_auth_q q M, the split it into
       funspec_auth_q (q/2) M ∗ funspec_auth_q (q/2) M
    - Push back into the invariant
    - Convert the other half using: funspec_auth_q q M ⊢ matchfunspecs ge G
    - Therefore, every call to code_ctx_take_matchfunspecs produces a fresh linear matchfunspecs,
      while keeping a smaller positive fraction for future calls.
    Idea is
    code_bank -> repeatedly produces matchfunspecs
    initial_core -> helps construct the child fungassert
    code_ctx -> persistent package available through iLöb
   *)

  (* 	Stores ∃ q, funspec_auth_q q M in an invariant.
     It is necessary because q becomes smaller after each spawn. *)
  Definition code_bank (m0 : mem) : iProp Σ :=
    inv codeN (∃ q : Qp, funspec_auth_q q (init_funspecs m0 ge G)).

  (* 	Packages code_bank with initial_core, which is needed to build the child’s fungassert. *)
  Definition code_ctx (m0 : mem) : iProp Σ :=
    code_bank m0 ∗ initial_world.initial_core m0 (F := Clight.function) ge G.

  (* Creates persistent invariant from initial half-auth. *)
  Lemma code_ctx_alloc (m0 : mem) :
    funspec_auth_q (1/2)%Qp (init_funspecs m0 ge G) ∗
      initial_world.initial_core m0 (F := Clight.function) ge G ={⊤}=∗ code_ctx m0.
  Proof.
    iIntros "(Hauth & #Hcore)".
    iMod (inv_alloc codeN ⊤ (∃ q : Qp, funspec_auth_q q (init_funspecs m0 ge G))
           with "[Hauth]") as "#Hbank".
    { iNext; by iExists (1/2)%Qp. }
    rewrite /code_ctx /code_bank.
    iFrame "#"; done.
  Qed.
  
  Global Instance code_ctx_persistent m0 : Persistent (code_ctx m0) := _.
  Global Instance code_ctx_affine m0 : Affine (code_ctx m0) := _.

  (* Opens the bank, splits q, returns half, and converts other half into fresh matchfunspecs. *)
  Lemma code_ctx_take_matchfunspecs (m0 : mem) : code_ctx m0 -∗ |={⊤}=> ▷ matchfunspecs ge G.
  Proof.
    iIntros "#Hctx".
    rewrite /code_ctx /code_bank.
    iDestruct "Hctx" as "(#Hbank & #Hcore)".
    iInv codeN as "Hbody" "Hclose".
    iAssert (▷ ((∃ q : Qp, funspec_auth_q q (init_funspecs m0 ge G)) ∗
                  (∃ q : Qp, funspec_auth_q q (init_funspecs m0 ge G))))%I
      with "[Hbody]" as "Hsplit".
    { iNext.
      iDestruct "Hbody" as (q) "Hauth".
      rewrite funspec_auth_q_split.
      iDestruct "Hauth" as "(Hkeep & Htake)".
      iSplitL "Hkeep".
      - by iExists (((1/2) * q)%Qp).
      - by iExists (((1/2) * q)%Qp).
    }
    rewrite bi.later_sep.
    iDestruct "Hsplit" as "(Hkeep & Htake)".
    iMod ("Hclose" with "Hkeep") as "_".
    iModIntro.
    iNext.
    iDestruct "Htake" as (q) "Hauth".
    iApply (init_funspecs_matchfunspecs_q with "Hauth").
  Qed.


  (* SPAWN *)

  (* Global context:
     no function-specific locals;
     individual function contexts are added by func_tycontext'. *)
  Lemma spawn_safe (mcode : mem) (Hinitcode : Genv.init_mem prog = Some mcode)
    (γ : gname) (tp : dtp) (m : mem) (ls : gset address)
    (i : nat) (q : gname) (σ1 : rmap)
    (Htp_wf : threads_wellformed tp) (Hinvariant : invariant tp)
    (Hcompat : mem_compatible tp m) (Hlocks : locks_coherent tp m ls)
    (Hlockdom : forall a r, lockRes tp a = Some r -> a ∈ ls)
    (cnti : containsThread tp i)
    (Heq1 : mem_equiv.access_map_equiv (perm_of_rmap σ1) (getThreadR cnti))
    (argsty : typelist) (retty : type) (cc : calling_convention) (k : cont) (args : list val)
    (Hi : getThreadC cnti = Kblocked (Callstate (Ctypes.External CREATE argsty retty cc) args k))
    (x : Jext_spec_type (concurrent_ext_spec CS ext_link) CREATE) :
    ⊢ □ believe (CS := CS) (concurrent_ext_spec CS ext_link) (nofunc_tycontext V G) ge (nofunc_tycontext V G) -∗
      code_ctx mcode -∗ other_threads_safe γ tp i -∗
      Jext_spec_pre (concurrent_ext_spec CS ext_link) CREATE x (genv_symb_injective ge) (sig_args (ef_sig CREATE)) args -∗
      ▷ post_safe γ q x argsty retty cc args k -∗
      lock_state1 γ m ls (lockRes tp) -∗
      thread_state_interp γ q (restrPermMap (Hcompat i cnti)) σ1 () -∗
      |={⊤}[∅]▷=>
        ∃ (tp' : t) (m' : mem) (ev : Events.sync_event) (σnew : rmap),
          ⌜threads_wellformed tp' ∧ invariant tp' ∧ mem_compatible tp' m' ∧
           locks_coherent tp' m' ls ∧ (forall a r, lockRes tp' a = Some r -> a ∈ ls) ∧
           glob_coherent m' σnew ∧ syncStep true cnti Hcompat tp' m' ev⌝ ∧
          ext_auth () ∗ rmap_auth γ σnew ∗ threads_safe tp' γ ∗ lock_state1 γ m' ls (lockRes tp').
  Proof.
    iIntros "#Hbelieve #Hcode Hsafe Hpre Hpost locks S".
    rewrite CEspec_spawn_pre /=.
    iDestruct "Hpre" as (x' Heqx) "Hpre".
    destruct x' as ((f, b), (A, ((gv, w), pre))); rewrite /funspec2pre' /=.
    iDestruct "Hpre" as (Hty (Hb & _) Hargs) "Hpre"; simpl in Hargs; subst.
    rewrite /SEPx /GLOBALSx /LOCALx; monPred.unseal.
    iDestruct "Hpre" as "(%Hglobals & Hfun & Harg & _)".
    iDestruct (bi.and_elim_r with "Harg") as "Hchild".
    rewrite /thread_state_interp /conc_state_interp /thread_mem_auth /thread_rmap.
    iDestruct "S" as (σ0) "(%Hglob0 & (Hauth & Hext) & %Hcoh1 & Hfrag1 & Hmem1)".
    apply glob_coherent_restrPermMap in Hglob0.
    














    
    iIntros "#Hbelieve #Hcode Hsafe Hpre Hpost Hls S".
    iDestruct "S" as (σcur) "(%Heq & Hmem & Hauth & Hfrag & Hext)".
    rewrite /locks_coherent in Hlocks.
    rewrite CEspec_spawn_pre /=.
    iDestruct "Hpre" as (x' Heqx) "Hpre".
    destruct x' as ((f, b), (A, ((gv, w), pre))); rewrite /funspec2pre' /=.
    set (c := Callstate (Ctypes.External CREATE argsty retty cc) args k).
    iDestruct "Hpre" as (Hty (Hb & _) Hargs) "Hpre"; simpl in Hargs; subst.
    rewrite /SEPx /GLOBALSx /LOCALx; monPred.unseal.
    iDestruct "Hpre" as "(%Hglobals & Hfun & Harg & _)".
    iDestruct (bi.and_elim_r with "Harg") as "Hchild".
    (*
      - Hfun : func_ptr child_spec f
      Proves f points to executable code satisfying the expected child-thread specification.
      - Hchild : pre w b
      Resource transferred to the new child thread. It establishes the child function's precondition for b.
     *)
    clear Hty.
    rewrite /post_safe /other_threads_safe.
    setoid_rewrite CEspec_spawn_post.
    iUnfold SeparationLogic.func_ptr, seplog.func_ptr_si in "Hfun".
    iDestruct "Hfun" as (fblock Hf) "Hfun".
    subst f.
    iDestruct "Hfun" as (fs_actual) "(Hsub & #Hfunc)".
    
    
    (*
      f = Vptr fblock Ptrofs.zero
      Hfunc : func_at fs_actual (fblock, 0), which actual function specification is stored at that code address.
      Hsub : funspec_sub_si fs_actual child_spec.
      Actual function can be called using the spawn-required spec
     *)
    
    (* At spawn, we have: Hfun: func_at fs_actual (fblock, 0) and Hsub  : funspec_sub_si fs_actual child_spec
       But Hfun only says some spec exists at the addr, but doesn't prove that fblock coresponds to a function declared in G. So we need
       ∃ id fs_child, Genv.find_symbol ge id = Some fblock ∧
         find_id id G = Some fs_child ∧ funspec_sub_si fs_child fs_actual.

       That bridge requires matchfunspecs ge G.
       But matchfunspecs is not sufficient.
       One copy resolves Hfunc to the func in G. another copy is combined with initial_core by initial_core_funassert to build the child's fungassert.
       Later recursive spawn steps need it again.
       But matchfunspecs is linear, not Persistent, so it cannot be duplicated through the Löb induction.
       Solution: code_bank stores splittable funspec_auth_q inside an invariant and
                 generates a fresh matchfunspecs whenever spawn needs one.
      
     *)
    destruct fs_actual as [fsig0 cc0 A0 E0 P0 Q0].
    iUnfold seplog.funspec_sub_si in "Hsub".
    iUnfold NDmk_funspec in "Hsub".
    iDestruct "Hsub" as "(%Hsigcc & Hsub)".
    destruct Hsigcc as [Hsig Hcc].
    subst fsig0 cc0.
    rewrite step_fupd_fupd.
    iMod (code_ctx_take_matchfunspecs mcode with "Hcode") as "Hmatch_fun".
    iMod (code_ctx_take_matchfunspecs mcode with "Hcode") as "Hmatch_child".
    rewrite /code_ctx.
    iDestruct "Hcode" as "(#Hbank & #Hcore)".
    iApply step_fupd_intro; first done.
    iNext.
    iSpecialize ("Hsub" $! (b, w) (filter_genv (symb2genv (genv_symb_injective ge)), [b])).
    iMod (fupd_plainly_elim with "Hsub") as "Hsub".
    iSpecialize ("Hsub" with "[Hchild]").
    { iSplit.
      - iPureIntro.
        rewrite /seplog.argsHaveTyps /=.
        constructor; last constructor.
        intros _.
        destruct b; simpl in Hb |- *; unfold AST.Tptr; destruct Archi.ptr64; simpl in *; auto.
      - rewrite /PROPx /PARAMSx /GLOBALSx /LOCALx /SEPx /=.
        monPred.unseal.
        repeat iSplit; try iPureIntro; try done.
        unfold_lift in Hglobals. tauto.
    }
    iMod "Hsub" as (xchild F Hmask) "Hsubout".
    iDestruct "Hsubout" as "((HF & HP0) & HQ0)".
    (*
      xchild: existential witness for actual child spec.
      HP0: actual precondition required to start the child.
      HQ0: converts actual child postcondition back to the empty spawn postcondition.
     *)
    
    iSpecialize ("Hmatch_fun" $! fblock (mk_funspec ([Ctypesdefs.tptr Ctypesdefs.tvoid], Ctypesdefs.tptr Ctypesdefs.tvoid) cc_default A0 E0 P0 Q0) with "Hfunc").
    iDestruct "Hmatch_fun" as (id_child fs_child) "(%Hchild_find & Hsub_child)".
    destruct Hchild_find as [Hchild_symbol Hchild_spec].
    iMod "Hsub_child" as "Hsub_child".
    destruct fs_child as [fsig_child cc_child Achild Echild Pchild Qchild].
    iUnfold seplog.funspec_sub_si in "Hsub_child".
    iDestruct "Hsub_child" as "(%Hsig_child & Hsub_child)".
    destruct Hsig_child as [Hfsig_child Hcc_child].
    subst fsig_child cc_child.
    iPoseProof ("Hbelieve" $! (Vptr fblock Ptrofs.zero)
                  ([Ctypesdefs.tptr Ctypesdefs.tvoid], Ctypesdefs.tptr Ctypesdefs.tvoid)
                  cc_default Achild Echild Pchild Qchild with "[]") as "Hbelieve_child".
    { iPureIntro.
      exists id_child.
      split.
      - rewrite /= find_id_maketycontext_s //.
      - exists fblock; split; [done | done].
    }
    set (gargsC := (filter_genv (symb2genv (genv_symb_injective ge)), [b])).
    assert (HargsC : seplog.argsHaveTyps [b] ([Ctypesdefs.tptr Ctypesdefs.tvoid], Ctypesdefs.tptr Ctypesdefs.tvoid).1).
    { rewrite /seplog.argsHaveTyps /=.
      constructor; last constructor.
      intros _.
      destruct b; simpl in Hb |- *; unfold Tptr; destruct Archi.ptr64; simpl in *; auto.
    }
    Check believe.
    iAssert (▷ |={E0 xchild}=> ∃ (xC : dtfr Achild) (FC : iPropI Σ),
               ⌜Echild xC ⊆ E0 xchild⌝ ∧ (FC ∗ Pchild xC gargsC) ∧
           ∀ rho' : environ, ■ (⌜ve_of rho' = Map.empty (Values.block * type)⌝ ∧
                                  FC ∗ Qchild xC rho' -∗ Q0 xchild rho'))%I
      with "[Hsub_child HP0]" as "Hpre_child".
    {
      iNext.
      iMod (fupd_plainly_elim with "Hsub_child") as "Hsub_child".
      iSpecialize ("Hsub_child" $! xchild gargsC with "[HP0]").
      { iSplit; try iPureIntro; try done. }
      iFrame.
    }
(*    iDestruct "Hmem" as (Hlt0) "(%Hcoh0 & Hrs)".
    set (m_parent := restrPermMap Hlt).
    pose proof (mem_equiv.useful_permMapLt_trans Hlt Hlt0) as Hlt_inner.
    iAssert (frag_mem_auth m_parent σcur) with "[Hrs]" as "Hmem_parent".
    { rewrite /frag_mem_auth.
      iExists Hlt_inner.
      iFrame.
      iPureIntro.
      rewrite (restrPermMap_idem Hlt_inner).
      replace (restrPermMap (permMapLt_restr Hlt_inner)) with (restrPermMap Hlt0); auto.
      apply restr_proof_irr.
    }
    iAssert (thread_state_interp γ (getCurPerm m_parent) q m_parent σ1 ())
      with "[Hmem_parent Hauth Hfrag Hext]" as "Hstate".
    { rewrite /thread_state_interp.
      iExists σcur.
      iSplit; iFrame.
      iPureIntro.
      pose proof (mem_equiv.getCur_restr (perm_of_rmap σ1) m Hlt) as Hcur. done.
    }

    (* CREATE returns void. *)
    iSpecialize ("Hpost" $! (None : option val) m_parent σ1 () with "[]").
    { iPureIntro; repeat split; simpl.
      destruct b; simpl in Hb |- *; unfold Tptr; destruct Archi.ptr64; auto. }
    iMod "Hpost" as "Hpost".
    iDestruct ("Hpost" with "Hstate []") as (c') "(%Hafter & Hstate & Hjsafe_parent)".
    { simpl.
      iExists (Vptr fblock Ptrofs.zero, b, existT A (gv, w, pre)).
      iSplit; auto.
      rewrite /funspec2post' /PROPx /LOCALx /SEPx /=.
      monPred.unseal.
      iSplit; first done.
      iSplit; done. 
    }
    (* Recover the parent resources returned by Hpost. *)
    iUnfold thread_state_interp in "Hstate".
    iDestruct "Hstate" as (σnew) "(%Heq_parent & Hmem_parent & Hauth & Hfrag & Hext)".
    (* Return from the restricted parent memory to global memory m. *)
    iPoseProof (frag_mem_auth_restr_to_global m (perm_of_rmap σ1) Hlt σnew
                 with "Hmem_parent") as "Hmem".
    set (tp_upd_test := updThread cnti (Kresume c Vundef) (getThreadR cnti)).
    set (tp_test := addThread tp_upd_test (Vptr fblock Ptrofs.zero) b (empty_map : access_map)).
    set (child_id := pos.n (OrdinalPool.num_threads tp_upd_test)).

    set (qh := ((1/2) * q)%Qp).

    iAssert (rmap_frag γ qh σ1 ∗ rmap_frag γ qh (ε : raw_rmapR))%I
      with "[Hfrag]" as "[Hfrag_parent Hfrag_child]".
    { rewrite -rmap_frag_op /qh -Qp.mul_add_distr_r Qp.half_half Qp.mul_1_l right_id. iFrame. }

    assert (Hchild_spec_ctx :
             (make_tycontext_s G !! id_child)%maps =
               Some (mk_funspec ([Ctypesdefs.tptr Ctypesdefs.tvoid], Ctypesdefs.tptr Ctypesdefs.tvoid) cc_default Achild Echild Pchild Qchild)).
    { rewrite find_id_maketycontext_s //. }

    assert (Hchild_spec_delta :
             (seplog.glob_specs (nofunc_tycontext V G) !! id_child)%maps =
               Some (mk_funspec ([Ctypesdefs.tptr Ctypesdefs.tvoid], Ctypesdefs.tptr Ctypesdefs.tvoid) cc_default Achild Echild Pchild Qchild)) by auto.

    iPoseProof (believe_exists_fundef (CS := CS) (psi := ge) (Delta := nofunc_tycontext V G)
         Hchild_symbol Hchild_spec_delta with "Hbelieve") as "%Hfundef_child".

    destruct Hfundef_child as (ff_child & Hff_child & Hff_type_child).

    set (q_new := Callstate ff_child [b] Kstop).

    assert (Hinit_child : cl_initial_core ge (Vptr fblock Ptrofs.zero) [b] = Some q_new).
    {
      unfold q_new, cl_initial_core.
      destruct (Ptrofs.eq_dec Ptrofs.zero Ptrofs.zero) as [_ | Hneq]; try contradiction.
      rewrite Hff_child //.
    }

    iAssert ((jsafe_frag γ qh ⊤ () c') ∗
               ∃ q_child : CC_core,
                 ⌜cl_initial_core ge (Vptr fblock Ptrofs.zero) [b] = Some q_child⌝ ∧
                   ▷ jsafe_frag γ qh ⊤ () q_child)%I
      with "[Hjsafe_parent Hpre_child Hmatch_child HF HQ0]" as "Hsafety_pair".
    {
      iSplitL "Hjsafe_parent".
      - (* Parent q -> qh *)
        admit.

      - iExists q_new.
        iSplit; try iPureIntro; try done.
        iDestruct "Hbelieve_child" as "[HBE_child | HBI_child]".
        + (* External child. *)
          iUnfold believe_external in "HBE_child".
          rewrite Genv.find_funct_find_funct_ptr Hff_child.
          destruct ff_child as [fchild | ef sigargs sigret cc_child].
          { simpl; iDestruct "HBE_child" as "[]". }
          simpl.
          iDestruct "HBE_child" as "(%Hext_info & Hsemext_child & #Htc_child)".
          destruct Hext_info as (Hsig_child & Hcc_child & Hef_child & Hinline_child).
          (* Move the forall across the later,
so the same iNext opens both the child precondition and semax_external. *)    
          iSpecialize ("Hsemext_child" $! ge).
          rewrite -bi.later_forall.
          iNext.
          rewrite jsafe_frag_unfold /jsafe_frag_pre.
          iMod (fupd_mask_subseteq (E0 xchild)) as "Hclose0". set_solver.
          iMod "Hpre_child" as (xC FC) "(%HmaskC & (HFC & HPC) & HQC)".
          iSpecialize ("Hsemext_child" $! xC).
          iMod (fupd_mask_subseteq (Echild xC)) as "HcloseC". done.
          iMod ("Hsemext_child" $! FC (sig_args (ef_sig ef)) [b] with "[HPC HFC]") as "Hrun_ext".
          { iSplit; iFrame.
            iPureIntro.
            rewrite Hef_child /=.
            destruct b; simpl in Hb |- *; unfold AST.Tptr; destruct Archi.ptr64; auto.
          }
          iMod "HcloseC" as "_".
          iMod "Hclose0" as "_".
          assert (Hinline0 : ef_inline ef = false).
          { destruct Hinline_child as [Hinline0 | Hempty]; auto; exfalso; done. }
          iModIntro.
          iIntros (mC σC pC) "HstateC".
          iUnfold thread_state_interp in "HstateC".
          iDestruct "HstateC" as (σglob) "(%HeqC & HmemC & HauthC & HfragC & HextC)".
          iDestruct "HmemC" as (HltGlob) "(%HcohGlob & HheapC)".
          iDestruct (resource_map.resource_map_auth_valid with "HheapC") as %HvGlob.
          destruct HvGlob as (_ & Hvσglob).
          iDestruct (rmap_auth_frag_permMapLt_valid γ qh σglob σC Hvσglob
                      with "[$HauthC $HfragC]") as %(HvσC & HltLocal).
          assert (HltChild : permMapLt (perm_of_rmap σC) (getMaxPerm mC)).
          { etransitivity; eauto. }
          iDestruct ("Hrun_ext" $! (restrPermMap HltGlob) σglob ()
                      with "[HheapC HextC]") as (xext) "(HstdC & HpreC & HpostC)".
          { rewrite /state_interp /mem_rmap_auth. iFrame. iPureIntro. auto. }
          iDestruct "HstdC" as "((%HcohStd & HheapC) & HextC)".
          iExists HltChild.
          iRight; iRight.
          iExists ef, [b], xext.
          iSplit.
          { iPureIntro.
            change (cl_at_external q_new = Some (ef, [b])).
            rewrite /q_new /cl_at_external Hinline0 //.
          }
          iSplitL "HheapC HauthC HfragC HextC".
          { rewrite /thread_state_interp.
            iExists σglob.
            iSplit; first done.
            iSplitL "HheapC"; iFrame.
            rewrite /frag_mem_auth.
            iExists HltGlob.
            iPureIntro. done.
          }
          iSplitL "HpreC". iFrame.
          iNext.
          iIntros (ret m' σC' z') "%Htypes".
          iIntros "!> HstateC' HpostC'".
          iUnfold thread_state_interp in "HstateC'".
          iDestruct "HstateC'" as (σglob') "(%HeqC' & HmemC' & HauthC' & HfragC' & HextC')".
          iDestruct "HmemC'" as (HltGlob') "(%HcohGlob' & HheapC')".
          iSpecialize ("HpostC" $! (sig_res (ef_sig ef)) ret (restrPermMap HltGlob') σglob' z').
          iAssert (|={⊤}=> state_interp (restrPermMap HltGlob') σglob' z' ∗
                  Qchild xC (make_ext_rval (filter_genv ge) (sig_res (ef_sig ef)) ret) ∗ FC)%I
            with "[HpostC HheapC' HextC' HpostC']" as "Hpost_inner".
          {
            iMod (fupd_mask_subseteq (Echild xC)) as "HclosePost". clear. set_solver.
            iMod "HpostC" as "HpostC".
            iDestruct ("HpostC" with "[HheapC' HextC'] HpostC'") as "(HstdC' & HQchild & HFC')".
            { rewrite /state_interp /mem_rmap_auth. iFrame. done. }
            iMod "HclosePost" as "_".
            iModIntro.
            iFrame.
          }
          iMod "Hpost_inner" as "(HstdC' & HQchild & HFC')".
          iDestruct "HstdC'" as "((%HcohStd' & HheapC') & HextC')".
          set (rhoC := make_ext_rval (filter_genv ge) (sig_res (ef_sig ef)) ret).
          assert (HveC : ve_of rhoC = Map.empty (Values.block * type)).
          { subst rhoC. rewrite Hef_child /=. destruct ret; auto. }
          rewrite bi.affinely_elim.
          iSpecialize ("HQC" $! rhoC).
          iMod (fupd_plainly_elim with "HQC") as "HQC".
          iAssert (Q0 xchild rhoC) with "[HQC HFC' HQchild]" as "HQ0ret".
          { iApply "HQC". iSplit; first done. iFrame. }
          rewrite bi.affinely_elim.
          iSpecialize ("HQ0" $! rhoC).
          iMod (fupd_plainly_elim with "HQ0") as "HQ0".
          iAssert ((PROP ( ) (monpred.monPred_defs.monPred_and_def (seplog.local (liftx True%type))
                   (monpred.monPred_defs.monPred_embed_def emp))) rhoC)%I
            with "[HQ0 HF HQ0ret]" as "Hdone".
          { iApply "HQ0". iSplit; iFrame; iPureIntro; done. }
          rewrite /PROPx.
          iDestruct "Hdone" as "(_ & (_ & _))".
          iAssert (thread_state_interp γ (getCurPerm m') qh m' σC' z')%I
            with "[HheapC' HauthC' HfragC' HextC']" as "Hstate_final".
          { rewrite /thread_state_interp.
            iExists σglob'. iSplit; auto. iFrame.
            iExists HltGlob'; iSplit; done.
          }
          set (vret := match ret with | Some v => v | None => Vundef end).
          iModIntro.
          iExists (Returnstate vret Kstop).
          iSplit.
          { iPureIntro; rewrite /q_new /vret /= //. }
          iFrame.
          rewrite jsafe_frag_unfold /jsafe_frag_pre.
          iModIntro.
          iIntros (mR σR pR) "HstateR".
          iUnfold thread_state_interp in "HstateR".
          iDestruct "HstateR" as (σglobR) "(%HeqR & HmemR & HauthR & HfragR & HextR)".
          iDestruct "HmemR" as (HltGlobR) "(%HcohR & HheapR)".
          iDestruct (resource_map.resource_map_auth_valid with "HheapR") as %(_ & HvGlobR).
          iDestruct (rmap_auth_frag_permMapLt_valid γ qh σglobR σR HvGlobR
                      with "[$HauthR $HfragR]") as "%HvalidR".
          destruct HvalidR as (_ & HltLocalR).
          assert (HltR : permMapLt (perm_of_rmap σR) (getMaxPerm mR)).
          { etransitivity; eauto. }
          iExists HltR.
          iLeft.
          iExists Int.zero.
          iSplit; iPureIntro; try done.
        + (* Internal child. *)
          (* By definition, only Returnstate _ Kstop is halted, and only Callstate (External ...) _ _ is at_external.
Since q_new is Callstate (Internal fI) [b] Kstop, both cases are impossible;
we therefore prove its safety via step_internal_function.

           *)
          iUnfold believe_internal in "HBI_child".
          iDestruct "HBI_child" as (bI fI (HvI & HfindI & HcompleteI & HnorepI & HnorepVarsI & HvarsI & HparamsI & HretI & HccI)) "HbodyI".
          injection HvI as <-.
          assert (HffI : ff_child = Ctypes.Internal fI) by congruence.
          subst ff_child.
          iSpecialize ("HbodyI" $! (nofunc_tycontext V G) CS with "[%] [%]").
          { intros f0. apply expr.tycontext_sub_refl. }
          { apply expr.cenv_sub_refl. }
          (*
            HbodyI + Hpre_child can establish standard safety:

            jsafe
              (genv_symb := genv_symb_injective)
              (cl_core_sem ge)
              (concurrent_ext_spec CS ext_link)
              ge ⊤ () q_new

            But the required goal is:

            jsafe_frag γ qh ⊤ () q_new
          *)

          iAssert (▷ jsafe (genv_symb := genv_symb_injective) (cl_core_sem ge) (concurrent_ext_spec CS ext_link) ge ⊤ () q_new)%I with "[-]" as "Hsafe_standard".
          { rewrite -bi.later_forall.
            iNext.
            iApply fupd_jsafe.
            iMod (fupd_mask_subseteq (E0 xchild)) as "Hclose0". set_solver.
            iMod "Hpre_child" as (xC FC HmaskC) "((HFC & HPC) & HQC)".
            iMod "Hclose0" as "_".
            iSpecialize ("HbodyI" $! xC).
            pose proof (CSL_all_safe CPROOF HH lockGS0) as Hprog.
            destruct Hprog as [HnrB [HAL [HGG [[HmatchF [HGC HBelieveProg]] [HGV Hmain]]]]].
            apply compute_list_norepet_e in HnrB.
            assert (HCSUB : expr.cenv_sub (@cenv_cs CS) (genv_cenv ge)).
            { change (genv_cenv ge) with (prog_comp_env prog).
              clear -HGG.
              hnf; intros id; hnf.
              destruct (cenv_cs !! id)%maps eqn:Hid; auto.
              apply Maps.PTree.elements_complete.
              rewrite /prog -HGG.
              by apply Maps.PTree.elements_correct.
            }
            iModIntro.
            rewrite semax_fold_unfold.
            iSpecialize("HbodyI" $! ge (func_tycontext' fI (nofunc_tycontext V G)) CS
                         with "[%] [Hbelieve]").
            { split3; auto; try by apply expr.tycontext_sub_refl. apply expr.cenv_sub_refl. }
            { iFrame "Hbelieve". }
            assert (HtcI : Cop2.tc_vals [Ctypesdefs.tptr Ctypesdefs.tvoid] [b]) by done.
            pose proof (tc_vals_length _ _ HtcI) as HlenI.
            change ([Ctypesdefs.tptr Ctypesdefs.tvoid] = map snd (fn_params fI)) in HparamsI.
            rewrite HparamsI map_length in HlenI.
            destruct (build_call_temp_env fI [b] HlenI) as (teI & HteI).
            rewrite /q_new.
            iApply jsafe_step.
            rewrite /jstep_ex.
            iIntros (mI σI) "(HmI & HextI)".
            (* Allocate the child's local variables and obtain the stack-frame resource required to enter its body.

             step_internal_function :
             function_entry2 ge f vargs m e le m1 ->
                step ge (Callstate (Internal f) vargs k) m (State f (fn_body f) k e le) m1

               Callstate (Internal fI) [b] Kstop --> State fI (fn_body fI) Kstop veI teI
               Clight requires function_entry2

             *)
            iMod (alloc_stackframe mI fI ge teI with "[$HmI]") as (mI' veI [HallocI HvenvI]) "((%HcohI & HmI') & HstackI)"; [try done.. |].
            { unfold var_sizes_ok in HvarsI.
              rewrite !Forall_forall in HvarsI, HcompleteI |- *.
              intros v Hv.
              specialize (HcompleteI v Hv).
              specialize (HvarsI v Hv).
              rewrite (veric.expr_lemmas4.cenv_sub_sizeof HCSUB); auto.
            }
            iModIntro.
            (* The child has no caller; returning from its entry function terminates the thread. *)
            iExists (State fI (fn_body fI) Kstop veI teI), mI', HcohI.
            iSplit.
            { apply list_norepet_append_inv in HnorepI as (Hnr_params & Hnr_temps & Hdisjoint).
              iPureIntro.
              constructor. constructor; done.
            }
            iSplitL "HmI' HextI".
            { rewrite /state_interp. iFrame. }
            iNext.
            set (f0 := mkfunction Ctypesdefs.tvoid cc_default nil nil nil Sskip).
            set (Fouter := (⎡(F ∗ FC)%I⎤ : assert)).
            set (rho0 := construct_rho (filter_genv ge) Clight.empty_env (Maps.PTree.empty val)).
            set (Finner := (emp : assert)).
            set (Fkeep := (⎡Fouter rho0 ∗ Finner rho0⎤ : assert)).
            set (R0 := Clight_seplog.normal_ret_assert (maybe_retval (assert_of (Qchild xC)) (Ctypesdefs.tptr Ctypesdefs.tvoid) None)).
            assert (Hglob0 : seplog.typecheck_glob_environ (filter_genv ge) (seplog.glob_types (nofunc_tycontext V G))).
            { eapply tc_ge_denote_initial; eauto. }
            assert (Hguard0 : guard_environ (nofunc_tycontext V G) f0 rho0).
            { subst rho0 f0.
              split3; first split3; simpl; auto.
              - intros ??; by setoid_rewrite Maps.PTree.gempty.
              - intros ??; rewrite /make_venv /Map.get.
                setoid_rewrite Maps.PTree.gempty.
                split; first done; by intros (? & ?).
              - intros ?; done.
            }
            assert (HclosedCall : semax.closed_wrt_modvars (Scall None (Econst_int Int.zero Ctypesdefs.tint) nil) Fouter).
            { rewrite closed_wrt_modvars_Scall. subst Fouter.
              intros rho te' Hmodified. monPred.unseal. done.
            }
            assert (Hctl0 : ∀ ret0 z',
               assert_safe (concurrent_ext_spec CS ext_link) ge ⊤ f0 Clight.empty_env
                 (set_opttemp None (val_lemmas.force_val ret0) (Maps.PTree.empty val))
                 (exit_cont EK_normal None Kstop)
                 (construct_rho (filter_genv ge) Clight.empty_env (set_opttemp None (val_lemmas.force_val ret0) (Maps.PTree.empty val))) ⊢ jsafeN (concurrent_ext_spec CS ext_link) ge ⊤ z' (Returnstate (val_lemmas.force_val ret0) Kstop)).
            { intros ret0 z'; iIntros "?"; by iApply return_stop_safe; try iPureIntro. }
            assert (Hpost0 : ⊢ ∀ rho' : environ,
                   ■ ((∃ old : val, substopt None (liftx old) Finner rho' ∗
                      maybe_retval (assert_of (Qchild xC)) (Ctypesdefs.tptr Ctypesdefs.tvoid) None rho') -∗ RA_normal R0 rho')).
            { iIntros (rho') "!> H"; by iDestruct "H" as (old) "(_ & Hret)". }
            iPoseProof Hpost0 as "#Hpost0".
            assert (Hrguard0 : ⊢ rguard (concurrent_ext_spec CS ext_link) ge ⊤
                 (nofunc_tycontext V G) f0 (Clight_seplog.frame_ret_assert R0 Fouter) Kstop).
            {
              rewrite /rguard /_guard.
              iIntros (ek vl tx vx).
              try iModIntro.
              rewrite Clight_seplog.proj_frame.
              iIntros "(%Henv0 & (? & Q) & ?)".
              destruct ek; simpl Clight_seplog.proj_ret_assert; monPred.unseal;
                try iDestruct "Q" as (->) "Q"; try iDestruct "Q" as "[]".
              iIntros (??).
              iApply jsafe_step.
              rewrite /jstep_ex.
              iIntros (??) "(Hm & ?)".
              iMod (free_stackframe _ f0 _ _ vx tx with "[$Hm]") as (???) "?"; try eassumption; try solve [constructor].
              {
                destruct Henv0 as (? & Hmatch & ?).
                split3; auto.
                split3; simpl; eauto.
                - intros ??.
                  by setoid_rewrite Maps.PTree.gempty.
                - intros ??.
                  setoid_rewrite Maps.PTree.gempty.
                  simpl in *.
                  split; first done.
                  rewrite /Map.get.
                  intros (? & Hid).
                  specialize (Hmatch id).
                  rewrite Hid // in Hmatch.
              }
              { by rewrite /Clight_seplog.stackframe_of /f0 /=. }
              iIntros "!>".
              iExists _, _, _.
              iSplit. iPureIntro; econstructor; eauto.
              iFrame.
              by iApply return_stop_safe; try iPureIntro.
            }
            iPoseProof Hrguard0 as "#Hrguard0".
            iAssert (▷ rguard (concurrent_ext_spec CS ext_link) ge ⊤ (nofunc_tycontext V G) f0 (Clight_seplog.frame_ret_assert R0 Fouter) Kstop)%I with "[]" as "#Hrguard0_later"; try done.
            iPoseProof (semax_call_aux2 (CS' := CS) ⊤ (nofunc_tycontext V G) Achild Qchild xC Finner Fouter None f0 ([Ctypesdefs.tptr Ctypesdefs.tvoid], Ctypesdefs.tptr Ctypesdefs.tvoid) (Econst_int Int.zero Ctypesdefs.tint) nil R0 ge fI I (fun _ => eq_refl) HclosedCall HCSUB HcompleteI HnorepI HnorepVarsI (conj HparamsI HretI) Clight.empty_env (Maps.PTree.empty val) Kstop rho0 eq_refl Hguard0 Kstop eq_refl Hctl0 with "Hpost0 Hrguard0_later") as "#Haux".
            iDestruct "Haux" as "(%HclosedBody & #HrguardBody)".
            iAssert (guard' (concurrent_ext_spec CS ext_link) ge ⊤ (func_tycontext' fI (nofunc_tycontext V G)) fI (Fkeep ∗ Clight_seplog.bind_args (fn_params fI) (argsassert_of (Pchild xC)) ∗ stackframe_of' cenv_cs fI) (Kseq (fn_body fI) Kstop))%I with "[]" as "#HguardI".
            {
              iApply ("HbodyI" $! Kstop Fkeep fI ⊤).
              iIntros "!>".
              iSplit.
              - iPureIntro.
                split; auto.
              - iFrame "HrguardBody".
            }
            set (rhoI := construct_rho (filter_genv ge) veI teI).
            iAssert (stackframe_of' cenv_cs fI rhoI)%I with "[HstackI]" as "HstackI".
            { simpl. done. }
            assert (HtcParamsI : Cop2.tc_vals (snd (split (fn_params fI))) [b]).
            { by rewrite snd_split -HparamsI. }
            assert (HnrParamsI : list_norepet (map fst (fn_params fI))).
            { by apply list_norepet_app in HnorepI as [Hparams_nr [_ _]]. }
            assert (HevalParamsI : map (fun xt => eval_id (fst xt) rhoI) (fn_params fI) = [b]).
            { subst rhoI.
              clear -HnrParamsI HteI.
              remember [b] as args eqn:Hargs in HteI |- *.
              clear Hargs.
              remember (create_undef_temps (fn_temps fI)) as te0 eqn:Hte0 in HteI.
              clear Hte0.
              revert args te0 teI HteI HnrParamsI.
              induction (fn_params fI) as [|a l IH]; destruct args;
                intros; auto; try discriminate.
              - destruct a.
                inv HteI.
              - destruct a as [id ty].
                simpl in HteI.
                inv HnrParamsI.
                rewrite <- (IH _ _ _ HteI); auto.
                simpl.
                f_equal.
                unfold eval_id, construct_rho.
                simpl.
                erewrite pass_params_ni; try eassumption.
                rewrite Maps.PTree.gss. done.
            }
            assert (HguardEnvI : guard_environ (func_tycontext' fI (nofunc_tycontext V G)) fI rhoI).
            { unfold guard_environ.
              split3; try done. subst rhoI. eapply semax_call_typecheck_environ; eauto. }
            iPoseProof (initial_core_funassert (CSL_prog CPROOF) V G mcode (make_venv veI) (make_tenv teI) HnrB HmatchF Hinitcode
                with "[$Hcore $Hmatch_child]") as "HfunN".
            assert (HsameGlobI : ∀ id,
                       (seplog.glob_specs (nofunc_tycontext V G) !! id)%maps =
                         (seplog.glob_specs
                            (func_tycontext' fI (nofunc_tycontext V G)) !! id)%maps).
            { intros id; done. }
            assert (HsameEnvI : ge_of (mkEnviron (filter_genv (globalenv (CSL_prog CPROOF)))
                                         (make_venv veI) (make_tenv teI)) = ge_of rhoI).
            { subst rhoI; done. }
            iPoseProof (same_glob_funassert'
                 (nofunc_tycontext V G) (func_tycontext' fI (nofunc_tycontext V G))
                 (mkEnviron (filter_genv (globalenv (CSL_prog CPROOF)))
                    (make_venv veI) (make_tenv teI)) rhoI HsameGlobI HsameEnvI
                         with "HfunN") as "HfunI".
            iAssert (Clight_seplog.funassert (func_tycontext' fI (nofunc_tycontext V G)) rhoI)%I with "[HfunI]" as "HfunI'".
            { rewrite -same_glob_funassert'; auto. }
            assert (HfilterGenv : filter_genv (symb2genv (genv_symb_injective ge)) = filter_genv ge).
            { by apply functional_extensionality. }
            rewrite /gargsC HfilterGenv.
            unfold guard', _guard .
            iApply ("HguardI" with "[-]"); last first; try done.
            iSplit; try done.
            iFrame "HstackI HfunI'".
            iSplitL "HF HFC".
            + rewrite /Fkeep /Fouter /Finner.
              monPred.unseal. iFrame.
            + rewrite /Clight_seplog.bind_args.
              monPred.unseal.
              iSplit.
              * iPureIntro.
                rewrite /Clight_seplog.tc_formals.
                by rewrite -HparamsI HevalParamsI.
              * iApply (make_args_close_precondition (fn_params fI) [b] ge (create_undef_temps (fn_temps fI)) veI teI (argsassert_of (Pchild xC)) with "HPC"); auto.
                apply (tc_vals_Vundef HtcI).
          }
          (* Child: standard jsafe → fraction 1 → qh *)
          admit.
    }
    iDestruct "Hsafety_pair" as "[Hjsafe_parent_half Hspawn_child]".
    iAssert (threads_safe tp_test γ)%I with "[Hsafe Hfrag_parent Hfrag_child Hjsafe_parent_half Hspawn_child]" as "Hthreads_test".
    { rewrite /threads_safe /tp_test /tp_upd_test.
      rewrite seq_S big_sepL_app big_sepL_singleton.
      iSplitL "Hsafe Hfrag_parent Hjsafe_parent_half".
      - iApply "Hsafe".
        + iIntros "!>" (k0 y (-> & Hk)%lookup_seq Hki) "Hy".
          replace (0 + k0) with k0 in * by lia.
          assert (Hik : i ≠ k0) by lia.
          iDestruct "Hy" as (q0 σ0 cnty) "(%Hperm & Hsafe_y & Hfrag_y)".
          set (cnty_u := @cntUpdate _ _ _ i k0 tp (Kresume c Vundef) (getThreadR cnti) cnti cnty).
          set (cnty_n := @cntAdd dryResources Sem (@OrdinalPool.OrdinalThreadPool dryResources Sem) k0 _ (Vptr fblock Ptrofs.zero) b (empty_map : access_map) cnty_u).
          iExists q0, σ0, cnty_n.
          iSplit.
          { assert (Hres : getThreadR cnty_n = getThreadR cnty).
            { subst cnty_n cnty_u. rewrite gsoAddRes gsoThreadRes; auto. }
            by rewrite Hres.
          }
          iSplitL "Hsafe_y"; iFrame.
          rewrite /thread_safe.
          iDestruct "Hsafe_y" as (cnty0) "Hsafe_y".
          set (cnty0_u := @cntUpdate _ _ _ i k0 tp (Kresume c Vundef) (getThreadR cnti) cnti cnty0).
          set (cnty0_n := @cntAdd dryResources Sem (@OrdinalPool.OrdinalThreadPool dryResources Sem) k0 _ (Vptr fblock Ptrofs.zero) b (empty_map : access_map) cnty0_u).
          iExists cnty0_n.
          assert (Hcode : getThreadC cnty0_n = getThreadC cnty0).
          { subst cnty0_n cnty0_u. rewrite gsoAddCode gsoThreadCode; auto. }
          rewrite Hcode. iFrame.
        + set (cnti_u := @cntUpdate _ _ _ i i tp (Kresume c Vundef) (getThreadR cnti) cnti cnti).
          set (cnti_n := @cntAdd dryResources Sem (@OrdinalPool.OrdinalThreadPool dryResources Sem) i _ (Vptr fblock Ptrofs.zero) b (empty_map : access_map) cnti_u).
          iExists qh, σ1, cnti_n.
          iSplit.
          { assert (Hres : getThreadR cnti_n = getThreadR cnti).
            { subst cnti_n cnti_u. rewrite gsoAddRes gssThreadRes //. }
            by rewrite Hres.
          }
          iFrame.
          rewrite /thread_safe.
          iExists cnti_n.
          assert (Hcode : getThreadC cnti_n = Kresume c Vundef).
          { subst cnti_n cnti_u. rewrite gsoAddCode gssThreadCode //. }
          rewrite Hcode /=.
          iIntros (c0) "%Hafter0".
          replace c0 with c'. iFrame.
          simpl in Hafter0, Hafter. congruence.
      - assert (Hchild_latest : 0 + pos.n (OrdinalPool.num_threads tp_upd_test) =
                                  OrdinalPool.latestThread tp_upd_test).
        { rewrite /OrdinalPool.latestThread. lia. }
        assert (cntC : containsThread tp_test (0 + pos.n (OrdinalPool.num_threads tp_upd_test))).
        { subst tp_test. rewrite Hchild_latest. apply OrdinalPool.cntAddLatest. }
        iExists qh, (ε : raw_rmapR), cntC.
        iSplit.
        { iPureIntro. rewrite gssAddRes. done. done. }
        iDestruct "Hspawn_child" as (q_child) "(%Hinit_child1 & Hsafe_child1)".
        iSplitL "Hsafe_child1"; iFrame.
        rewrite /thread_safe.
        iExists cntC.
        rewrite gssAddCode.
        iExists q_child.
        iSplit; try iFrame; try done. done.
    }
*)
  Admitted.

  Lemma acquire_safe (γ : gname) (tp : dtp) (m : mem) (ls : gset address) (i : nat) (q : Qp) (σ1 : rmap) (Htp_wf : threads_wellformed tp) (Hinvariant : invariant tp) (Hcompat : mem_compatible tp m)
    (Hlocks : locks_coherent tp m ls)
    (Hlockdom : forall a r, lockRes tp a = Some r -> a ∈ ls)
    (cnti : containsThread tp i)
    (Hlt : permMapLt (perm_of_rmap σ1) (getMaxPerm m))
    (Heq1 : mem_equiv.access_map_equiv (perm_of_rmap σ1) (getThreadR cnti))
    (argsty : typelist) (retty : type) (cc : calling_convention) (k : cont) (args : list val)
    (Hi : getThreadC cnti = Kblocked (Callstate (Ctypes.External LOCK argsty retty cc) args k))
    (* (Hcoh : coherent (restrPermMap Hlt) σ1) *)
    (* (Hlt0 : permMapLt (perm_of_rmap σ1) (getMaxPerm (restrPermMap Hlt))) *)
    (x : Jext_spec_type (concurrent_ext_spec CS ext_link) LOCK):
  ⊢ other_threads_safe γ tp i -∗
    Jext_spec_pre (concurrent_ext_spec CS ext_link) LOCK x (genv_symb_injective ge) (sig_args (ef_sig LOCK)) args -∗
    ▷ post_safe γ q x argsty retty cc args k -∗ lock_state1 γ m ls (lockRes tp) -∗
    thread_state_interp γ (getThreadR cnti) q m σ1 () -∗
    |={⊤}[∅]▷=>
      ∃ (tp' : t) (m' : mem) (ev : Events.sync_event) (σnew : rmap),
        ⌜threads_wellformed tp' ∧ invariant tp' ∧ mem_compatible tp' m' ∧
          locks_coherent tp' m' ls ∧ (forall a r, lockRes tp' a = Some r -> a ∈ ls) ∧
          syncStep true cnti Hcompat tp' m' ev⌝ ∧
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
      assert (Hstep_fail :
               syncStep true cnti Hcompat tp m
                 (Events.failacq (l1.1, Ptrofs.intval (Ptrofs.repr l1.2)))).
      {
        eapply step_acqfail with (c := c) (b := l1.1) (ofs := Ptrofs.repr l1.2)
          (marg := restrPermMap (Hcompat i cnti)); try done.
        - subst c. rewrite Hl1 //.
        - unfold unchecked_load; simpl.
          rewrite Hofs. by f_equal.
      }
      iAssert (jsafe_frag γ q ⊤ () c) with "[Hl Hpost]" as "Hjsafe".
      { rewrite jsafe_frag_unfold /jsafe_frag_pre.
        iModIntro.
        (* external-call case again *)
        iIntros (m0 σ0 p0) "S0".
        (* keep the state unchanged *)
        iDestruct "S0" as (σcur0) "(%Heq0 & Hmem0 & Hauth0 & Hfrag0 & Hext0)".
        iAssert (frag_mem_auth m0 σcur0 ∧
                   ⌜✓ (σcur0 : resource_map.rmapUR share address (leibnizO resource))⌝)%I
          with "[Hmem0]" as "[Hmem0 %Hvalid_cur0]".
        {
          iSplit; first done.
          rewrite /frag_mem_auth.
(*          iDestruct "Hmem0" as (?) "(_ & Hrs0)".
          by iDestruct (resource_map.resource_map_auth_valid with "Hrs0") as "(_ & %Hv)".*) admit.
        }
(*        iDestruct "Hmem0" as "(%Hltσcur0 & %Hσcur0 & Hrs0)".
        iAssert ((rmap_auth γ σcur0 ∗ rmap_frag γ q σ0) ∧
                   ⌜✓ σ0 ∧ permMapLt (perm_of_rmap σ0) (perm_of_rmap σcur0)⌝)%I
          with "[Hauth0 Hfrag0]" as "[(Hauth0 & Hfrag0) %Hfrag_valid]".
        { iSplit; iFrame.
          iApply (rmap_auth_frag_permMapLt_valid γ q σcur0 σ0); auto. iFrame. }
        destruct Hfrag_valid as (Hvalidσ0 & Hσ0_cur0).
        assert (Hlt1 : permMapLt (perm_of_rmap σ0) (getMaxPerm m0)).
        { etransitivity; eauto. }
        iExists Hlt1.
        iRight; iRight.
        iExists LOCK, [l], x.
        iSplit.
        { iPureIntro. rewrite /c /= //. }
        (* rebuild thread_state_interp *)
        iAssert (frag_mem_auth m0 σcur0) with "[Hrs0]" as "Hmem0".
        { rewrite /frag_mem_auth. iExists Hltσcur0; iSplit; try done. }
        rewrite /thread_state_interp.
        iSplitL "Hmem0 Hauth0 Hfrag0 Hext0".
        { iExists σcur0; iSplit; try done. iFrame. }
        iSplitL "Hl".
        - rewrite CEspec_acquire_pre /=.
          iExists (l, sh, R).
          iSplit; try done.
          rewrite /funspec2pre' /=.
          iSplit; try iPureIntro; rewrite Hl1 //.
          rewrite /PROPx /PARAMSx /GLOBALSx /LOCALx /SEPx /=.
          monPred.unseal.
          repeat iSplit; try iPureIntro; try done.
        - iNext.
          rewrite /c.
          setoid_rewrite CEspec_acquire_post. iFrame.
      }
      iAssert (threads_safe tp γ) with "[Hsafe Hjsafe Hfrag]" as "Hthreads".
      { rewrite /threads_safe.
        iApply "Hsafe".
        - (* every non-selected thread: unchanged *)
          iIntros "!>" (k0 y) "%Hlookup %Hneq Hy". iFrame.
        - (* selected thread i: still blocked at c *)
          iExists q, σ1, cnti.
          iFrame.
          iSplitR "Hjsafe"; try iPureIntro; try done.
          rewrite /thread_safe.
          iExists cnti.
          rewrite Hi. done.
      }
      rewrite step_fupd_fupd.
      iApply step_fupd_intro; first done.
      iNext.
      iExists tp, m, (Events.failacq (l1.1, Ptrofs.intval (Ptrofs.repr l1.2))), σcur.
      iModIntro.
      iSplit; try iFrame.
      + iPureIntro.
        split; [apply Htp_wf|].
        split; [apply Hinvariant|].
        split; [apply Hcompat|].
        split; try done.
     + rewrite /lock_state1.
       iDestruct "Hls" as (I) "(Hdom & Hown & Hmap)".
       iExists I.
       iFrame.
       iApply (big_sepM_mono with "Hmap").
       iIntros (a R0 Hlookup) "Ha".
       iDestruct "Ha" as "[Ha | Ha]".
       * iLeft.
         iDestruct "Ha" as (qL σlock l2) "(HfragL & Hpure & HR)".
         iExists qL, σlock, l2.
         iFrame. done.
       * iRight; try done.
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
      destruct Hσlock as (Hvalid_join & Hlock_holds & Hσlock_locks).
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
            done.
      }
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
      iAssert (frag_mem_auth m_global' σnew2 ∧
                 ⌜✓ (σnew2 : resource_map.rmapUR share address (leibnizO resource))⌝)%I
        with "[Hmem_global]" as "[Hmem_global %Hvalid_new]".
      {
        iSplit; first done.
        rewrite /frag_mem_auth.
        iDestruct "Hmem_global" as (?) "(_ & Hrs)".
        by iDestruct (resource_map.resource_map_auth_valid with "Hrs") as "(_ & %Hv)".
      }

      iAssert ((rmap_auth γ σnew2 ∗ rmap_frag γ q σpost ∗ other_threads_safe γ tp i) ∧
           ⌜ forall j (cntj : containsThread tp j),
               i <> j -> permMapsDisjoint newThreadPerm (getThreadR cntj)⌝)%I
        with "[Hauth_post Hfrag_post Hsafe]" as "[Hkeep %Hnr_threads]".
      {
        iSplit; try iFrame.
        iApply (other_threads_post_disjoint γ tp i
               (σnew2 : resource_map.rmapUR share address (leibnizO resource))
               σpost q newThreadPerm
               Hvalid_new Heq_acq).
        iFrame.
      }
      iDestruct "Hkeep" as "(Hauth_post & Hfrag_post & Hsafe)".
      set (IRpost := fun a => if decide (a = l1) then Some empty_map else lockRes tp a).
      iAssert (⌜lock_addresses_disjoint ls⌝ ∧ lock_state1 γ m_global' ls IRpost)
        with "[Hls_store]" as "(%Hdisj & Hls_store)".
      {
        unfold IRpost, m_global'.
        rewrite /lock_state1.
        iDestruct "Hls_store" as (I) "((%Hdom & %Hdisj) & Hown & Hmap)".
        iSplit; auto.
        iExists I.
        iSplit.
        { iPureIntro. split; done. }
        iFrame "Hown".
        iApply (big_sepM_mono with "Hmap").
        iIntros (a R0 Hlookup) "Ha".
        iDestruct "Ha" as "[Ha | Ha]".
        - iLeft.
          iDestruct "Ha" as (qL σlock0 l0') "(HfragL & (%HIR0 & %Heq0 & %Hload0 & %Hnonempty0) & HR0)".
          iExists qL, σlock0, l0'.
          iFrame "HfragL".
          iSplit.
          { iPureIntro. repeat split; done. }
          iNext.
          iExact "HR0".
        - iRight.
          iExact "Ha".
      }
      iPoseProof (lock_resources_post_disjoint γ m_global' ls IRpost σnew2 σpost q newThreadPerm
           Hvalid_new Heq_acq with "[$Hauth_post $Hfrag_post $Hls_store]") as "%Hnr_locks".
      {
        intros a r HIR.
        unfold IRpost in HIR.
        destruct (decide (a = l1)) as [Heq2 | Hneq2].
        - subst a. done.
        - eapply Hlockdom. apply HIR.
      }
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
          rewrite H //.
      }
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
          iDestruct "Hlocked" as (qL σlock0 l2) "(Hfrag & (%HIR & %Heq_lock & %Hload & %Hnonempty) & HR)".
          iExists qL, σlock0, l2.
          iFrame.
          iPureIntro; auto.
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
                 ∧ locks_coherent tp' m_global' ls ∧
                (forall a r, lockRes tp' a = Some r -> a ∈ ls)) as Hstep.
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
          destruct Hσlock_locks as (Hlock_eq & Heq_lock & Hσlock_locks).
          assert (Hl0eq : Hlock_holds = l0) by congruence.
          subst Hlock_holds.
          assert (Hlock :
                   forall b ofs,
                     l0 # b ofs = (perm_of_rmap σlock) # b ofs).
          {
            intros b0 ofs0.
            unfold mem_equiv.access_map_equiv in Heq_lock.
            specialize (Heq_lock b0).
            exact (f_equal (fun f => f ofs0) Heq_lock).
          }
          rewrite (Hlock b ofs).
          assert (Hthread : (getThreadR cnti) # b ofs = (perm_of_rmap σ1R) # b ofs).
          {
            unfold σ1R.
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
          + assert (Hjoin_rmap:
                     permMapJoin (perm_of_rmap σlock) (perm_of_rmap σ1) (perm_of_rmap σpost)).
            {
              unfold σpost, σ1R.
              apply perm_of_rmap_op_permMapJoin.
              exact Hvalid_join.
            }
            destruct Hσlock_locks as
              [Hlock_eq [Heq_lock Hσlock_nonempty]].
            assert (Hl0eq : Hlock_holds = l0) by congruence.
            subst Hlock_holds.
            unfold lock_rmap_nonempty_on in Hσlock_nonempty.
            split.
            assert (Hjoin_acq : permMapJoin l0 (getThreadR cnti) newThreadPerm).
            { unfold permMapJoin in *.
              intros b ofs.
              specialize (Hjoin_rmap b ofs).
              unfold mem_equiv.access_map_equiv in Heq_lock, Heq_acq.
              specialize (Heq_lock b).
              specialize (Heq_acq b).
              rewrite (f_equal (fun f => f ofs) Heq_lock).
              rewrite <- (f_equal (fun f => f ofs) (Heq1 b)).
              rewrite <- (f_equal (fun f => f ofs) Heq_acq).
              apply Hjoin_rmap.
            }
            assert (HinvL : invariant (updLockSet tp l1' empty_map)).
            { unfold l1'.
              eapply ThreadPoolWF.updLock_inv.
              - apply Hinvariant.
              (* empty_map disjoint with every other lock *)
              - intros laddr rmap' Hneq Hres.
                unfold permMapsDisjoint.
                intros b ofs.
                exists (rmap' # b ofs).
                simpl.
                reflexivity.
              (* every thread disjoint with empty_map *)
              - intros j cntj.
                unfold permMapsDisjoint.
                intros b ofs.
                exists ((getThreadR cntj) # b ofs).
                change (perm_union ((getThreadR cntj) # b ofs) None = Some ((getThreadR cntj) # b ofs)).
                destruct ((getThreadR cntj) # b ofs); reflexivity.
              (* coherence with other locks *)
              - intros laddr rmap' Hneq Hres.
                split; try done.
                pose proof
                    (locks_data_lock_coh tp Hinvariant
                       (l1.1, Ptrofs.intval (Ptrofs.repr l1.2)) l0 HlR) as HcohL.
                destruct HcohL as (_ & Hlocks).
                apply (Hlocks laddr rmap' Hres).
              (* empty_map itself at lock address *)
              - simpl. done.
              (* every thread has Nonempty at l1' *)
              - intros j cntj.
                pose proof (locks_data_lock_coh tp Hinvariant
                              (l1.1, Ptrofs.intval (Ptrofs.repr l1.2)) l0 HlR) as HcohL.
                destruct HcohL as [Hthreads _].
                exact (Hthreads j cntj).
              - intros ofs0 Hofs0.
                pose proof (lockRes_valid tp Hinvariant) as Hlr.
                specialize (Hlr l1.1 (Ptrofs.intval (Ptrofs.repr l1.2))).
                rewrite HlR in Hlr.
                apply (Hlr ofs0 Hofs0).
              - intros ofs0 Hofs0.
                destruct (lockRes tp (l1.1, ofs0)) eqn:Hres0.
                + pose proof (lockRes_valid tp Hinvariant) as Hlr.
                  specialize (Hlr l1.1 ofs0).
                  rewrite Hres0 in Hlr.
                  pose proof (Hlr (Ptrofs.intval (Ptrofs.repr l1.2)) Hofs0) as Hnone.
                  rewrite HlR in Hnone.
                  discriminate.
                + reflexivity.
            }
            assert (cntiL : containsThread (updLockSet tp l1' empty_map) i).
            { by eapply cntUpdateL. }
            unfold tp'.
            rewrite (updLock_updThread_comm tp i cnti (Kresume c Vundef) newThreadPerm l1' empty_map cntiL).
            eapply ThreadPoolWF.updThread_inv; eauto.
            * intros l2 rmap Hres.
              eapply Hnr_locks.
              assert (Hl1' : l1' = l1).
              { unfold l1'.
                destruct l1 as [b ofs].
                simpl in *.
                by f_equal. }
              rewrite Hl1' in Hres.
              unfold IRpost.
              destruct (decide (l2 = l1)) as [Heq2 | Hneq2].
              ++ subst l2.
                 rewrite decide_True; auto.
                 simpl in  Hres.
                 by rewrite OrdinalPool.gssLockRes in Hres.
              ++ rewrite decide_False; auto.
                 simpl in Hres.
                 rewrite OrdinalPool.gsoLockRes in Hres; auto.
            * intros l2 rmap Hres.
              assert (Hl1' : l1' = l1).
              { unfold l1'.
                destruct l1 as [b ofs].
                simpl in *.
                by f_equal.
              }
              rewrite Hl1' in Hres.
              destruct (eq_dec l2 l1) as [Heq2 | Hneq2].
              ** subst l2.
                 pose proof (locks_data_lock_coh tp Hinvariant l1 l0 Hlock_eq) as [Hthr Hlocks].
                 eapply permjoin_nonempty_bound; eauto.
              ** assert (Hres0 : lockRes tp l2 = Some rmap).
                 { rewrite gsoLockRes in Hres; auto. }
                 pose proof (locks_data_lock_coh tp Hinvariant l2 rmap Hres0) as [Hthr Hlocks].
                 eapply permjoin_nonempty_bound; eauto.
           * split.
             (* mem_compatible tp' m_global' *)
             assert (Hlt_new : permMapLt newThreadPerm (getMaxPerm m_global')).
             { intros b ofs.
               unfold mem_equiv.access_map_equiv in Heq_acq.
               specialize (Heq_acq b).
               rewrite <- (f_equal (fun f => f ofs) Heq_acq).
               apply (Hlt_store b ofs).
             }
             unfold tp', m_global', l1'.
             eapply mem_compatible_acquire_update; eauto.
             (* locks_coherent tp' m_global' ls *)
             assert (Hl1eq : l1' = l1).
             { unfold l1'.
               destruct l1 as [b ofs].
               simpl in *.
               by f_equal.
             }
             assert (Hlocks0 : locks_coherent tp m ls).
             { by unfold locks_coherent. }
             unfold tp'.
             rewrite Hl1eq.
             split; last first.
             (* Hlockdom after acquire *)
             intros a r Hres.
             destruct (eq_dec a l1) as [Heq2 | Hneq2].
             { subst a. done. }
             { simpl in Hres.
               rewrite OrdinalPool.gsoLockRes in Hres; auto.
               change (lockRes tp a = Some r) in Hres.
               eapply Hlockdom; eauto.
             }
             (* locks_coherent *)
             eapply locks_coherent_acquire_update with
               (tp := tp) (m := m) (i := i) (cnti := cnti) (c := c)
               (newThreadPerm := newThreadPerm) (l := l1); eauto.
             unfold m_global'.
             rewrite /Mem_load_unchecked /Mem_store_unchecked /Mem_store_unchecked_contents /=.
             rewrite Hofs.
             by rewrite Maps.PMap.gss -(encode_val_length Mptr (Vptrofs Ptrofs.zero)) Mem.getN_setN_same.
             ** intros l' Hl' Hneq.
                unfold m_global'.
                eapply Mem_load_unchecked_store_unchecked_lock_addresses_disjoint; eauto.
                replace (l1.1, Ptrofs.unsigned (Ptrofs.repr l1.2)) with l1; auto.
                destruct l1 as [b ofs].
                simpl in *.
                destruct l' as [b' ofs']; simpl in *. done.
             ** intros l' Hl' j cntj Hp.
                pose proof (cntUpdateL' _ _ cntj) as cntj_upd.
                destruct (Nat.eq_dec j i) as [Hji | Hji].
                ++ subst j.
                   unfold nonEmptyRangeCur.
                   intros z Hz.
                   rewrite restrPermMap_Cur_eq.
                   rewrite (gLockSetRes _ _ cntj_upd cntj).
                   rewrite (gssThreadRes cnti (Kresume c Vundef) newThreadPerm cntj_upd).
                   pose proof (Hlocks' l' Hl') as (_ & _ & Hrange).
                   pose proof (Hrange i cnti (compat_th tp m Hcompat cnti)) as Hold.
                   unfold nonEmptyRangeCur in Hold.
                   specialize (Hold z Hz).
                   rewrite restrPermMap_Cur_eq in Hold.
                   assert (Hσ1 : (perm_of_rmap σ1) # (l'.1) (l'.2 + z)%Z = Some Nonempty).
                   { unfold mem_equiv.access_map_equiv in Heq1.
                     specialize (Heq1 l'.1).
                     by rewrite Heq1.
                   }
                   pose proof (Hσlock_nonempty l' z Hl' Hz) as Hlock.
                   pose proof (Hjoin_rmap l'.1 (l'.2 + z)%Z) as Hjoin.
                   unfold mem_equiv.access_map_equiv in Heq_acq.
                   specialize (Heq_acq l'.1).
                   rewrite <- (f_equal (fun f => f (l'.2 + z)%Z) Heq_acq).
                   rewrite Hσ1 in Hjoin.
                   destruct ((perm_of_rmap σlock) # (l'.1) (l'.2 + z)%Z) as [p |] eqn:HpL.
                   *** destruct p; simpl in Hlock; try contradiction;
                         rewrite HpL in Hlock; inv Hlock.
                       inversion Hjoin; subst; reflexivity.
                       inversion Hjoin; subst; reflexivity.
                   *** inversion Hjoin; reflexivity.
                ++ assert (Hij : i <> j) by congruence.
                   assert (cntj_old : containsThread tp j).
                   { by eapply cntUpdate'. }
                   destruct (Hlocks' l' Hl') as (_ & _ & Hrange_old).
                   pose proof (compat_th tp m Hcompat cntj_old) as Hp_old.
                   specialize (Hrange_old j cntj_old Hp_old).
                   unfold nonEmptyRangeCur in Hrange_old |- *.
                   intros z Hz.
                   specialize (Hrange_old z Hz).
                   rewrite (restrPermMap_Cur_eq m_global' (getThreadR cntj) Hp
                              (l'.1) (l'.2 + z)%Z).
                   rewrite (gLockSetRes _ _ cntj_upd cntj).
                   erewrite @gsoThreadRes with (cntj := cntj_old); eauto.
                   rewrite (restrPermMap_Cur_eq m (getThreadR cntj_old) Hp_old
                              (l'.1) (l'.2 + z)%Z) in Hrange_old. done.
      }
      iPureIntro.
      destruct Hstep as (? & ? & ? & ? & ? & ?).
      split; done.
  Qed.
  
  Lemma rmap_auth_init_frag (γ : gname)
    (σ : resource_map.rmapUR share address (leibnizO resource)) :
    ✓ σ → rmap_auth γ (∅ : rmap) ∗ rmap_frag γ 1 (∅ : rmap) ==∗ rmap_auth γ σ ∗ rmap_frag γ 1 σ.
  Proof.
    iIntros (Hvalid) "[Hauth Hfrag]".
    rewrite /rmap_auth /rmap_frag.
    iMod (own_update_2 with "Hauth Hfrag") as "[Hauth Hfrag]"; try by apply frac_auth_update_1.
    iModIntro. iFrame.
  Qed.*) Admitted.

*)

  Lemma lock_state1_empty_change γ (m m' : mem) (IR IR' : address -> option access_map) :
    lock_state1 γ m (∅ : gset address) IR ⊢ lock_state1 γ m' (∅ : gset address) IR'.
  Proof.
    rewrite /lock_state1.
    iIntros "H".
    iDestruct "H" as (I) "(%HI & Hown & Hmap)".
    destruct HI as [Hdom Hdisj].
    assert (I = ∅) as ->.
    { apply map_empty.
      intros a.
      apply not_elem_of_dom.
      rewrite Hdom. done. }
    iExists (∅ : gmap address mpred).
    rewrite fmap_empty big_sepM_empty.
    iSplit; auto.
    iFrame.
    by rewrite big_sepM_empty.
  Qed.

  (*
  (** release **)
  Lemma rmap_frag_equiv_local `{!inG Σ rmap_authUR} (γ : gname) (q : Qp)
    (σ1 σ2 : resource_map.rmapUR share address (leibnizO resource)) :
    σ1 ≡ σ2 -> rmap_frag γ q σ1 ⊣⊢ rmap_frag γ q σ2.
  Proof.
    intros Heq.
    rewrite /rmap_frag.
    apply own_proper.
    by f_equiv.
  Qed.

  Lemma rmap_frag_lock_split `{!inG Σ rmap_authUR} (γ : gname) (q qL : Qp)
    (σ σkeep σlock : resource_map.rmapUR share address (leibnizO resource)) (Heq : σ ≡ σkeep ⋅ σlock) :
    rmap_frag γ q σ ∗ rmap_frag γ qL (∅ : raw_rmapR) ⊢ rmap_frag γ q σkeep ∗ rmap_frag γ qL σlock.
  Proof.
    iIntros "(Hfrag & Hempty)".
    iAssert (rmap_frag γ q (σkeep ⋅ σlock)) with "[Hfrag]" as "Hfrag".
    { rewrite <- (rmap_frag_equiv_local γ q σ (σkeep ⋅ σlock) Heq). iFrame. }
    iCombine "Hfrag Hempty" as "H".
    rewrite -rmap_frag_lock_transfer. iFrame.
  Qed.

  Definition rmap_entry_nonempty (x : address * shared.sharedR (leibnizO resource)) : Prop :=
    perm_of_res (resR_to_resource (Some x.2)) = Some Nonempty.

  Local Instance rmap_entry_nonempty_dec (x : address * sresR) : Decision (rmap_entry_nonempty x).
  Proof.
    unfold rmap_entry_nonempty.
    destruct (perm_of_res (resR_to_resource (Some x.2))) as [p |] eqn:Hp.
    - destruct p.
      + right; discriminate.
      + right; discriminate.
      + right; discriminate.
      + left; reflexivity.
    - right; discriminate.
  Defined.

  Definition rmap_lock_part (σ : resource_map.rmapUR share address (leibnizO resource)) :
    resource_map.rmapUR share address (leibnizO resource) := filter rmap_entry_nonempty σ.

  Definition rmap_keep_part (σ : raw_rmapR) : rmap := filter (fun x => ~ rmap_entry_nonempty x) σ.

  Lemma rmap_nonempty_partition
    (σ : resource_map.rmapUR share address (leibnizO resource)) :
    (σ : raw_rmapR) ≡
      ((rmap_keep_part σ : resource_map.rmapUR share address (leibnizO resource))
         ⋅
         (rmap_lock_part σ : resource_map.rmapUR share address (leibnizO resource))
        : raw_rmapR).
  Proof.
    apply equiv_dist.
    intros n loc.
    rewrite gmap.lookup_op.
    rewrite /rmap_keep_part /rmap_lock_part.
    rewrite !map_lookup_filter.
    destruct (σ !! loc) as [r |] eqn:Hloc; last first.
    { rewrite Hloc /=. done. }
    destruct (decide (rmap_entry_nonempty (loc, r))) as [Hne | Hne].
    - rewrite Hloc /=.
      rewrite option_guard_False; last first.
      intro Hnot. done.
      rewrite option_guard_True; last first; done.
    - rewrite Hloc /=.
      rewrite option_guard_True; try done.
      rewrite option_guard_False; try done.
  Qed.

  Lemma thread_rmap_lock_bytes_nonempty (tp : dtp) (m : mem) (ls : gset address)
    (Hcompat : mem_compatible tp m) (Hlocks : locks_coherent tp m ls)
    (i : nat) (cnti : containsThread tp i) (σ : rmap)
    (Heq : mem_equiv.access_map_equiv (perm_of_rmap σ) (getThreadR cnti)) :
    forall l z, l ∈ ls -> (0 <= z < Z.of_nat (size_chunk_nat Mptr))%Z ->
           (perm_of_rmap σ) # (l.1) (l.2 + z)%Z = Some Nonempty.
  Proof.
    intros l z Hl Hz.
    destruct (Hlocks l Hl) as (_ & _ & Hrange).
    pose proof (Hrange i cnti (Hcompat i cnti)) as Hrangei.
    unfold nonEmptyRangeCur in Hrangei.
    specialize (Hrangei z Hz).
    rewrite (restrPermMap_Cur_eq m (getThreadR cnti) (Hcompat i cnti) (l.1) (l.2 + z)%Z)
      in Hrangei.
    unfold mem_equiv.access_map_equiv in Heq.
    specialize (Heq l.1).
    rewrite Heq. done.
  Qed.

  Lemma rmap_keep_part_nonempty_on (ls : gset address) (σ : rmap)
    (Hexact : forall l z, l ∈ ls -> (0 <= z < Z.of_nat (size_chunk_nat Mptr))%Z ->
         (perm_of_rmap σ) # (l.1) (l.2 + z)%Z = Some Nonempty) :
    lock_rmap_nonempty_on ls (rmap_keep_part σ).
  Proof.
    unfold lock_rmap_nonempty_on.
    intros l z Hl Hz.
    specialize (Hexact l z Hl Hz).
    rewrite perm_of_rmap_lookup /resource_at in Hexact |- *.
    destruct (σ !! (l.1, (l.2 + z)%Z)) as [r |] eqn:Hloc.
    - assert (Hentry : rmap_entry_nonempty ((l.1, (l.2 + z)%Z), r)).
      { unfold rmap_entry_nonempty. rewrite Hloc // in Hexact. }
      rewrite perm_of_rmap_lookup /resource_at.
      rewrite map_lookup_filter Hloc /=.
      rewrite option_guard_False; last first; try intro Hnot; try done.
      simpl; if_tac; try done.
    - rewrite /rmap_keep_part perm_of_rmap_lookup /resource_at map_lookup_filter Hloc /=.
      if_tac; try done.
  Qed. 

  Lemma Mem_load_unchecked_store_unchecked_lock_addresses_disjoint_val
    (m : mem) (ls : gset address) (b b1 : Values.block) (o o1 : Z) (v : val) :
    lock_addresses_disjoint ls -> (b1, o1) ∈ ls -> (b, o) ∈ ls -> (b1, o1) <> (b, o) ->
    Mem_load_unchecked Mptr (Mem_store_unchecked Mptr m b o v) b1 o1 = Mem_load_unchecked Mptr m b1 o1.
  Proof.
    intros Hdisj Hin Hwrite Hneq.
    pose proof (Hdisj (b1, o1) (b, o) Hin Hwrite Hneq) as Hsep.
    change (b <> b1 \/ (o + size_chunk Mptr <= o1)%Z \/ (o1 + size_chunk Mptr <= o)%Z) in Hsep.
    unfold Mem_load_unchecked, Mem_store_unchecked, Mem_store_unchecked_contents.
    simpl.
    destruct (Pos.eq_dec b1 b) as [Hb | Hb].
    - subst b1.
      rewrite Maps.PMap.gss.
      f_equal.
      apply Mem.getN_setN_outside.
      rewrite encode_val_length.
      repeat rewrite <- size_chunk_conv.
      destruct Hsep as [Hbad | [Hleft | Hright]]; auto.
      exfalso. by apply Hbad.
    - rewrite Maps.PMap.gso; congruence.
  Qed.

  Lemma lock_release_rmap_update `{!VSTGS () Σ} `{!lockGS Σ} `{!inG Σ rmap_authUR}
    (γ : gname) (q : Qp) (m : mem) (ls : gset address) (IR : address -> option access_map)
    (l : val) (l1 : address) (sh : share) (R : oFunctor_car (dependent_type_functor_rec Mpred) (iProp Σ) (iProp Σ)) (σcur σ1 σthread σlock : resource_map.rmapUR share address (leibnizO resource)) (Hval : val2adr l l1) (Hl1mem : l1 ∈ ls)
    (Hload0 : Mem_load_unchecked Mptr m l1.1 l1.2 = Vptrofs Ptrofs.zero)
    (Hsplit : (σ1 : raw_rmapR) ≡ (σthread ⋅ σlock : raw_rmapR))
    (Hσlock_nonempty : lock_rmap_nonempty_on ls σlock) :
    let m_global' := Mem_store_unchecked Mptr m l1.1 l1.2 (Vptrofs Ptrofs.one) in
    let IRpost : address -> option access_map :=
      fun a => if decide (a = l1) then Some (perm_of_rmap σlock) else IR a in
    lock_inv sh l R -∗ R -∗ lock_state1 γ m ls IR -∗ frag_mem_auth m σcur -∗ rmap_frag γ q σ1 ==∗      ⌜IR l1 = Some empty_map ∧ Mem_load_unchecked Mptr m_global' l1.1 l1.2 = Vptrofs Ptrofs.one ∧
      (forall a : address, a ∈ ls -> a <> l1 ->
         Mem_load_unchecked Mptr m_global' a.1 a.2 = Mem_load_unchecked Mptr m a.1 a.2)⌝ ∧
    frag_mem_auth m_global' σcur ∗ rmap_frag γ q σthread ∗ lock_state1 γ m_global' ls IRpost ∗
      lock_inv sh l R.
  Proof.
    intros m_global' IRpost.
    iIntros "Hl HR Hls Hmem Hfrag".
    iDestruct "Hls" as (I) "((%Hdom & %Hldisj) & HI & Hmap)".
    iDestruct "Hl" as (a) "(%Hva & Hlk & Hinv)".
    assert (Ha : a = l1).
    { unfold val2adr in Hva, Hval. destruct l; try contradiction; congruence. }
    subst a.
    assert (HinI : l1 ∈ dom I).
    { by rewrite Hdom. }
    apply elem_of_dom in HinI.
    destruct HinI as (R0 & HIlookup).
    iDestruct (own_valid_2 (A := gmap_view.gmap_viewR address (laterO (iPropO Σ)))
                with "HI Hinv") as "#Hvalid".
    iDestruct (algebra.gmap_view_both_validI with "[$Hvalid]") as "(_ & #HeqR)".
    rewrite lookup_fmap HIlookup option_equivI /= later_equivI.
    iDestruct (big_sepM_delete _ _ l1 R0 HIlookup with "Hmap") as "[Hhere Hrest]".
    iDestruct "Hhere" as "[Hfree | Hheld]".
    { iDestruct "Hfree" as (qL σL pL) "(HfragL & (%HIR & %Hperm & %Hone & %Hnonempty) & HRold)".
      rewrite Hload0 in Hone.
      inv Hone.
    }
    iDestruct "Hheld" as (qL) "(HemptyL & (%HIRempty & %Hzero))".
    iDestruct (rmap_frag_lock_split γ q qL σ1 σthread σlock Hsplit with "[$Hfrag $HemptyL]")
      as "[Hfrag_thread Hfrag_lock]".
      (*
    (* Prepare the memory assertion expected by the store lemma. *)
    iDestruct "Hmem" as (Hltσcur) "(%Hcohσcur & Hrs)".
    pose proof (mem_equiv.useful_permMapLt_trans Hltσcur Hltσcur) as Hlt_pre.
    iAssert (frag_mem_auth (restrPermMap Hltσcur) σcur) with "[Hrs]" as "Hmem_pre".
    { rewrite /frag_mem_auth.
      iExists Hlt_pre.
      iFrame "Hrs".
      iPureIntro.
      rewrite (restrPermMap_idem Hlt_pre).
      replace (restrPermMap (permMapLt_restr Hlt_pre)) with (restrPermMap Hltσcur); auto.
      apply restr_proof_irr.
    }
    (* Store 1; the global rmap remains σcur. *)
    iMod (frag_mem_auth_store_unchecked_lock_zero_restr m σcur Hltσcur sh l1.1 l1.2 (Vptrofs Ptrofs.one) with "Hmem_pre Hlk") as (Hlt_store) "[Hmem_store Hlk]".
    iPoseProof (frag_mem_auth_restr_to_global
                  (Mem_store_unchecked Mptr (restrPermMap Hltσcur) l1.1 l1.2 (Vptrofs Ptrofs.one)) (perm_of_rmap σcur) Hlt_store σcur with "Hmem_store") as "Hmem_local".
    assert (Hlt_global : permMapLt (perm_of_rmap σcur) (getMaxPerm m_global')).
    { rewrite /m_global' getMaxPerm_store_unchecked //. }
    assert (Hstore_restr : Mem_store_unchecked Mptr (restrPermMap Hltσcur) l1.1 l1.2 (Vptrofs Ptrofs.one) = restrPermMap Hlt_global).
    { unfold m_global'; apply Mem.mkmem_ext; reflexivity. }
    rewrite Hstore_restr.
    iPoseProof (frag_mem_auth_restr_to_global m_global' (perm_of_rmap σcur) Hlt_global σcur
                 with "Hmem_local") as "Hmem".
    (* The released lock now contains 1. *)
    assert (Hload1' : Mem_load_unchecked Mptr m_global' l1.1 l1.2 = Vptrofs Ptrofs.one).
    { rewrite /m_global' /Mem_load_unchecked /Mem_store_unchecked /Mem_store_unchecked_contents /= Maps.PMap.gss /=.
      rewrite <- (encode_val_length Mptr (Vptrofs Ptrofs.one)).
      rewrite Mem.getN_setN_same.
      pose proof (decode_encode_val_general (Vptrofs Ptrofs.one) Mptr Mptr) as Hdecode.
      unfold Mptr, Vptrofs, decode_encode_val in Hdecode |- *.
      destruct Archi.ptr64; simpl in *; auto.
    }
    (* Other lock values are preserved. *)
    assert (Hload_other :
             forall a, a ∈ ls -> a <> l1 -> Mem_load_unchecked Mptr m_global' a.1 a.2 = Mem_load_unchecked Mptr m a.1 a.2).
    { intros (b1 & o1) Hin Hneq.
      unfold m_global'.
      destruct l1 as [b o]; simpl in *.
      apply (Mem_load_unchecked_store_unchecked_lock_addresses_disjoint_val
               m ls b b1 o o1 (Vptrofs Ptrofs.one) Hldisj Hin Hl1mem Hneq).
    }
    (* Put the transferred fragment and invariant into the lock. *)
    iAssert (lock_state1 γ m_global' ls IRpost) with "[HI Hrest Hfrag_lock HR]" as "Hls_store".
    { rewrite /lock_state1.
      iExists I.
      iFrame "HI".
      iSplit.
      { iPureIntro. split; assumption. }
      rewrite (big_sepM_delete _ _ l1 R0 HIlookup).
      iSplitL "Hfrag_lock HR".
      - iLeft.
        iExists qL, σlock, (perm_of_rmap σlock).
        iFrame "Hfrag_lock".
        iSplit.
        + iPureIntro.
          split.
          { unfold IRpost; destruct (decide (l1 = l1)) as [_ | Hneq]; auto. done. }
          split; try intro b; done.
        + iNext.
          iRewrite "HeqR"; done.
      - iApply (big_sepM_mono with "Hrest").
        iIntros (a Q Hlookup) "Ha".
        apply lookup_delete_Some in Hlookup.
        destruct Hlookup as [Hneq Hlookup].
        assert (Hin : a ∈ ls).
        { rewrite <- Hdom. eapply elem_of_dom_2; eauto. }
        assert (HIRsame : IRpost a = IR a).
        { unfold IRpost. destruct (decide (a = l1)) as [Heqa | Hneqa]; auto. done. }
        assert (Hsame : Mem_load_unchecked Mptr m_global' a.1 a.2 =
                          Mem_load_unchecked Mptr m a.1 a.2).
        { apply Hload_other; done. }
        rewrite HIRsame Hsame. iFrame.
    }
    (* Rebuild the lock assertion required by the release postcondition. *)
    iAssert (lock_inv sh l R) with "[Hlk Hinv]" as "Hl".
    { rewrite /lock_inv. iExists l1. iSplit; auto. }
    iModIntro.
    iFrame.
    iPureIntro. split; done.
  Qed.*) Admitted.
  
  Lemma release_safe (γ : gname) (tp : dtp) (m : mem) (ls : gset address) (i : nat) (q : Qp)
    (σ1 : resource_map.rmapUR share address (leibnizO resource))
    (Htp_wf : threads_wellformed tp) (Hinvariant : invariant tp)
    (Hcompat : mem_compatible tp m) (Hlocks : locks_coherent tp m ls)
    (Hlockdom : forall a r, lockRes tp a = Some r -> a ∈ ls) (cnti : containsThread tp i)
    (Hlt : permMapLt (perm_of_rmap σ1) (getMaxPerm m))
    (Heq1 : mem_equiv.access_map_equiv (perm_of_rmap σ1) (getThreadR cnti))
    (argsty : typelist) (retty : type) (cc : calling_convention) (k : cont) (args : list val)
    (Hi : getThreadC cnti = Kblocked (Callstate (Ctypes.External UNLOCK argsty retty cc) args k))
    (x : Jext_spec_type (concurrent_ext_spec CS ext_link) UNLOCK) :
  ⊢ other_threads_safe γ tp i -∗
    Jext_spec_pre (concurrent_ext_spec CS ext_link) UNLOCK x (genv_symb_injective ge) (sig_args (ef_sig UNLOCK)) args -∗
    ▷ post_safe γ q x argsty retty cc args k -∗ lock_state1 γ m ls (lockRes tp) -∗
    thread_state_interp γ (getThreadR cnti) q m σ1 () -∗
    |={⊤}[∅]▷=> ∃ (tp' : t) (m' : mem) (ev : Events.sync_event) (σnew : rmap),
        ⌜threads_wellformed tp' /\ invariant tp' /\ mem_compatible tp' m' /\ locks_coherent tp' m' ls /\ (forall a r, lockRes tp' a = Some r -> a ∈ ls) /\ syncStep true cnti Hcompat tp' m' ev⌝ ∧
        ext_auth () ∗ rmap_auth γ σnew ∗ frag_mem_auth m' σnew ∗ threads_safe tp' γ ∗
        lock_state1 γ m' ls (lockRes tp').
  Proof.
    iIntros "Hsafe Hpre Hpost Hls S".
    iDestruct "S" as (σcur) "(%Heq & Hmem & Hauth & Hfrag & Hext)".
    rewrite CEspec_release_pre /=.
    iDestruct "Hpre" as (x' Heqx) "Hpre".
    destruct x' as ((l, sh), R).
    rewrite /funspec2pre' /=.
    set (c := Callstate (Ctypes.External UNLOCK argsty retty cc) args k).
    iDestruct "Hpre" as (Hty Hprops Hargs) "Hpre".
    simpl in Hargs.
    subst.
    rewrite /SEPx /GLOBALSx /LOCALx.
    monPred.unseal.
    iDestruct "Hpre" as "(_ & Hsep)".
    iDestruct "Hsep" as "(Hexcl & Hl & HR & _)".
    simpl in Hprops.
    destruct Hprops as [Hsh _].
    (* Find the concrete lock address. *)
    iDestruct (lock_inv_in_lock_state γ m ls (lockRes tp) sh l R with "Hls Hl") as "%Hin".
    destruct Hin as (l1 & Hval & Hl1mem).
    assert (Hl1 : l = Vptr l1.1 (Ptrofs.repr l1.2)).
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
      subst.
      simpl.
      change (Ptrofs.Z_mod_modulus (Ptrofs.unsigned i0)) with (Ptrofs.unsigned (Ptrofs.repr (Ptrofs.unsigned i0))).
      by rewrite Ptrofs.repr_unsigned.
    }
    pose proof (Hlocks l1 Hl1mem) as Hlocks_l1.
    destruct Hlocks_l1 as (HlockRes & Hlockstate & Hrange).
    destruct (lockRes tp l1) as [l0 |] eqn:E.
    2: { exfalso. apply HlockRes; done. }
    destruct Hlockstate as [[Hload0 Hempty] | Hload1].
    - (* the actual release case: lock is held *)
       set (σthread := rmap_lock_part σ1).
       set (σlock := rmap_keep_part σ1).
       assert (Hsplit : (σ1 : raw_rmapR) ≡ (σthread ⋅ σlock : raw_rmapR)).
       { unfold σthread, σlock.
         rewrite comm.
         apply rmap_nonempty_partition.
       }
       assert (Hσlock_nonempty : lock_rmap_nonempty_on ls σlock).
       { unfold σlock.
         apply rmap_keep_part_nonempty_on.
         apply (thread_rmap_lock_bytes_nonempty tp m ls Hcompat Hlocks i cnti σ1 Heq1).
       }
       set (m_global' := Mem_store_unchecked Mptr m l1.1 l1.2 (Vptrofs Ptrofs.one)).
       set (IRpost := fun a : address =>
                        if decide (a = l1) then Some (perm_of_rmap σlock) else lockRes tp a).
       iMod (lock_release_rmap_update
               γ q m ls (lockRes tp) l l1 sh R σcur σ1 σthread σlock
               Hval Hl1mem Hload0 Hsplit Hσlock_nonempty
              with "Hl HR Hls Hmem Hfrag")
         as "Hrelease_result".

       iDestruct "Hrelease_result" as "[Hrelease_facts [Hmem [Hfrag_thread [Hls_store Hl]]]]".
       iDestruct "Hrelease_facts" as %Hrelease.
       destruct Hrelease as (HIRempty & Hload1' & Hload_other).
       (* Obtain a bound for the remaining thread permissions. *)
(*       iDestruct "Hmem" as (Hlt0) "(%Hcoh0 & Hrs)".
       iDestruct (resource_map.resource_map_auth_valid with "Hrs") as %(_ & Hvcur).
       iAssert ((rmap_auth γ σcur ∗ rmap_frag γ q σthread) ∧
                  ⌜✓ (σthread : raw_rmapR) ∧ permMapLt (perm_of_rmap σthread) (perm_of_rmap σcur)⌝)%I with "[Hauth Hfrag_thread]" as "[(Hauth & Hfrag_thread) %Hbounds]".
       {
         iSplit; iFrame.
         iApply (rmap_auth_frag_permMapLt_valid γ q σcur σthread Hvcur).
         iFrame.
       }
       destruct Hbounds as [Hvthread Hlt_thread_cur].
       assert (Hlt_thread : permMapLt (perm_of_rmap σthread) (getMaxPerm m_global')).
       { eapply permMapLt_trans with (q := perm_of_rmap σcur); done. }
       set (m_thread' := restrPermMap Hlt_thread).
       pose proof (mem_equiv.useful_permMapLt_trans Hlt_thread Hlt0) as Hlt_inner.
       iAssert (frag_mem_auth m_thread' σcur) with "[Hrs]" as "Hmem_thread".
       { rewrite /frag_mem_auth.
         iExists Hlt_inner.
         iFrame "Hrs".
         iPureIntro.
         rewrite (restrPermMap_idem Hlt_inner).
         replace (restrPermMap (permMapLt_restr Hlt_inner)) with (restrPermMap Hlt0); auto.
         apply restr_proof_irr.
       }
       iAssert (thread_state_interp γ (getCurPerm m_thread') q m_thread' σthread ())
         with "[Hmem_thread Hauth Hfrag_thread Hext]" as "Hstate".
       { rewrite /thread_state_interp.
         iExists σcur.
         iSplit; iFrame.
         iPureIntro.
         pose proof (mem_equiv.getCur_restr (perm_of_rmap σthread) m_global' Hlt_thread) as Hcur.
         done.
       }
       (* Pass the physical step and invoke the continuation. *)
       rewrite /post_safe.
       rewrite step_fupd_fupd.
       iApply step_fupd_intro; first done.
       iNext.
       iSpecialize ("Hpost" $! (None : option val) m_thread' σthread () with "[]").
       { iPureIntro. split; auto. done. }
       iMod "Hpost" as "Hpost".
       iDestruct ("Hpost" with "Hstate [Hl]") as (c') "(%Hafter & Hstate & Hjsafe)".
       { rewrite CEspec_release_post /=.
         iExists (l, sh, R).
         iSplit.
         { iPureIntro. exact Heqx. }
         rewrite /funspec2post' /PROPx /PARAMSx /GLOBALSx /LOCALx /SEPx /=.
         iSplit; first done.
         iFrame "Hl".
       }
       iUnfold thread_state_interp in "Hstate".
       iDestruct "Hstate" as (σnew) "(%Heq_post & Hmem_thread & Hauth & Hfrag_thread & Hext)".
       iPoseProof (frag_mem_auth_restr_to_global m_global' (perm_of_rmap σthread) Hlt_thread σnew
                    with "Hmem_thread") as "Hmem".
       iAssert (lock_state1 γ m_global' ls IRpost) with "[Hls_store]" as "Hls_store".
       { rewrite /lock_state1.
         iDestruct "Hls_store" as (J) "(HdomJ & HownJ & HmapJ)".
         iExists J.
         iFrame "HdomJ HownJ".
         iApply (big_sepM_mono with "HmapJ").
         iIntros (a Q Ha) "Ha".
         iDestruct "Ha" as "[Hfree | Hheld]".
         - iLeft.
           iDestruct "Hfree" as (qL0 σL0 pL0) "(Hf & Hp & HQ)".
           iExists qL0, σL0, pL0.
           iFrame. done.
         - iRight. done.
       }
       assert (Hlt_post : permMapLt (perm_of_rmap σthread) (getMaxPerm m)). done.
       set (δ := PTree.map (fun b fmax ofs =>
                              match fmax ofs with
                              | Some _ => Some ((perm_of_rmap σthread) # b ofs)
                              | None => None end) (getMaxPerm m).2).
       assert (Hnone_of_lt : forall (pm : access_map) b ofs,
            permMapLt pm (getMaxPerm m) -> (getMaxPerm m) # b ofs = None -> pm # b ofs = None).
       {
         intros pm b ofs Hpm Hnone.
         specialize (Hpm b ofs).
         rewrite Hnone in Hpm.
         destruct (pm # b ofs); [contradiction | reflexivity].
       }
       assert (Hcompute : mem_equiv.access_map_equiv (computeMap (getThreadR cnti) δ)
                            (perm_of_rmap σthread)).
       {
         intros b.
         extensionality ofs.
         case_eq (Maps.PTree.get b (getMaxPerm m).2).
         - intros fmax Hb.
           case_eq (fmax ofs).
           + intros pmax Hofs1.
             eapply computeMap_1 with
               (df := fun ofs0 => match fmax ofs0 with
                               | Some _ => Some ((perm_of_rmap σthread) # b ofs0)
                               | None => None end).
             * unfold δ.
               by rewrite Maps.PTree.gmap Hb.
             * by rewrite Hofs1.
           + intros Hofs1.
             transitivity ((getThreadR cnti) # b ofs).
             * eapply computeMap_2 with (df := fun ofs0 =>
                          match fmax ofs0 with
                          | Some _ => Some ((perm_of_rmap σthread) # b ofs0)
                          | None => None end).
               ** unfold δ.
                  by rewrite Maps.PTree.gmap Hb.
               ** by rewrite Hofs1.
             * assert (Hmax_none : (getMaxPerm m) # b ofs = None).
               { unfold Maps.PMap.get. by rewrite Hb. }
               rewrite (Hnone_of_lt (getThreadR cnti) b ofs (Hcompat i cnti) Hmax_none).
               by rewrite (Hnone_of_lt (perm_of_rmap σthread) b ofs Hlt_post Hmax_none).
         - intros Hb.
           transitivity ((getThreadR cnti) # b ofs).
           + apply computeMap_3.
             unfold δ.
             by rewrite Maps.PTree.gmap Hb.
           + assert (Hmax_none : (getMaxPerm m) # b ofs = None).
             { unfold Maps.PMap.get.
               rewrite Hb.
               pose proof (Max_isCanonical m) as Hcan.
               unfold isCanonical in Hcan.
               by rewrite Hcan. }
             rewrite (Hnone_of_lt (getThreadR cnti) b ofs (Hcompat i cnti) Hmax_none).
             by rewrite (Hnone_of_lt (perm_of_rmap σthread) b ofs Hlt_post Hmax_none).
       }
       set (newThreadPerm := computeMap (getThreadR cnti) δ).
       set (newLockPerm := perm_of_rmap σlock).
       assert (Heq_release : mem_equiv.access_map_equiv (perm_of_rmap σthread) newThreadPerm).
       { intros b. by symmetry. }
       set (l1' := (l1.1, Ptrofs.intval (Ptrofs.repr l1.2))).
       assert (Hl1eq : l1' = l1).
       { unfold l1'.
         destruct l1 as [b ofs].
         change ((b, Ptrofs.Z_mod_modulus ofs) = (b, ofs)).
         by rewrite Hofs. }
       set (tp' := updLockSet (updThread cnti (Kresume c Vundef) newThreadPerm) l1' newLockPerm).
       set (ev := Events.release l1' (Some (build_delta_content δ m_global'))).
       iAssert (threads_safe tp' γ) with "[Hsafe Hjsafe Hfrag_thread]" as "Hthreads".
       { rewrite /threads_safe.
         assert (Hnum : pos.n (OrdinalPool.num_threads tp') = pos.n (OrdinalPool.num_threads tp)).
         { subst tp'; auto. }
         rewrite Hnum.
         iApply "Hsafe".
         - iIntros "!>" (k0 y (-> & Hk)%lookup_seq Hneq) "Hy".
           replace (0 + k0) with k0 in * by lia.
           assert (Hneq' : i <> k0) by lia.
           iDestruct "Hy" as (q0 σ0 cnty) "(%Heqy & Hsafe_y & Hfrag_y)".
           assert (cnty' : containsThread tp' k0).
           { subst tp'; auto. }
           iExists q0, σ0, cnty'.
           iSplit.
           { iPureIntro.
             subst tp'.
             rewrite gLockSetRes.
             erewrite @gsoThreadRes with (cntj := cnty) by congruence. done. }
           iFrame "Hfrag_y".
           rewrite /thread_safe.
           iDestruct "Hsafe_y" as (cnty0) "Hsafe_y".
           assert (Hcnty : cnty0 = cnty) by apply proof_irrelevance.
           subst cnty0.
           iExists cnty'.
           subst tp'.
           rewrite gLockSetCode.
           erewrite gsoThreadCode by congruence. iFrame.
         - assert (cnti' : containsThread tp' i); subst tp'; auto.
           iExists q, σthread, cnti'.
           iSplit.
           { iPureIntro. by rewrite gLockSetRes gssThreadRes. }
           iFrame.
           rewrite /thread_safe.
           iExists cnti'.
           rewrite gLockSetCode gssThreadCode /=.
           iIntros (c'') "%Hafter''".
           change (Some (Returnstate Vundef k) = Some c') in Hafter.
           change (Some (Returnstate Vundef k) = Some c'') in Hafter''.
           assert (Hc : c'' = c') by congruence.
           rewrite Hc. iFrame.
       }
       assert (HlockRes_tp' : lockRes tp' = IRpost).
       { extensionality a.
         unfold tp'.
         rewrite Hl1eq.
         unfold IRpost.
         destruct (decide (a = l1)) as [Ha | Hneq].
         - subst a; by rewrite gssLockRes.
         - rewrite gsoLockRes; last congruence; by rewrite gsoThreadLPool.
       }
       iAssert (lock_state1 γ m_global' ls (lockRes tp')) with "[Hls_store]" as "Hls_final".
       { by rewrite HlockRes_tp'. }
       iExists tp', m_global', ev, σnew.
       iModIntro.
       iSplit; iFrame.
       iPureIntro.
       assert (syncStep true cnti Hcompat tp' m_global' ev /\ threads_wellformed tp'
               ∧ invariant tp' ∧ mem_compatible tp' m_global'
               ∧ locks_coherent tp' m_global' ls ∧
                 (∀ (a : address) (r : access_map), OrdinalPool.lockRes tp' a = Some r → a ∈ ls)) as Hstep.
       {
         split.
         assert (Hofs_int : Ptrofs.intval (Ptrofs.repr l1.2) = l1.2).
         { by change (Ptrofs.Z_mod_modulus l1.2 = l1.2). }
         unfold tp', ev, l1'.
         eapply step_release with
           (tp' := updThread cnti (Kresume c Vundef) newThreadPerm)
           (marg := restrPermMap (Hcompat i cnti)) (c := c) (b := l1.1) (ofs := Ptrofs.repr l1.2)
           (virtueThread := δ) (virtueLP := newLockPerm) (rmap := empty_map); eauto.
         - (* bounded delta *)
           unfold δ, bounded_maps.sub_map.
           intros b fδ Hfδ.
           rewrite PTree.gmap in Hfδ.
           destruct (((getMaxPerm m).2 !! b)%maps) as [fmax |] eqn:Hmax; simpl in Hfδ;
             try discriminate.
           inv Hfδ.
           exists fmax.
           split; auto.
           intros ofs Hδ.
           destruct (fmax ofs); simpl in Hδ; try discriminate; done.
         - (* empty default of the new lock map *)
           unfold newLockPerm, bounded_maps.map_empty_def.
           unfold perm_of_rmap.
           induction (map_to_list σlock) as [|[a r] entries IH]; auto.
         - (* at_external *)
           unfold c. by rewrite Hl1.
         - (* load zero *)
           change (Some (Mem_load_unchecked Mptr m l1.1 (Ptrofs.intval (Ptrofs.repr l1.2))) =
                     Some (Vptrofs Ptrofs.zero)).
           by rewrite Hofs_int Hload0.
         - (* store one *)
           rewrite Hofs_int.
           unfold m_global', unchecked_store, Mem_store_unchecked.
           f_equal.
           apply Mem.mkmem_ext; reflexivity.
         - (* old lock resource *)
           change (lockRes tp l1' = Some empty_map).
           rewrite Hl1eq.
           exact HIRempty.
         - change (permMapJoin newThreadPerm newLockPerm (getThreadR cnti)).
           assert (Hnone : perm_of_res (ε, None) = (@None permission)).
           { rewrite /perm_of_res /=. if_tac; auto. done. }
           intros b ofs.
           rewrite <- (Heq_release b).
           rewrite <- (Heq1 b).
           unfold newLockPerm, σthread, σlock, rmap_lock_part, rmap_keep_part.
           rewrite !perm_of_rmap_lookup /resource_at !map_lookup_filter.
           destruct (σ1 !! (b, ofs)) as [r |] eqn:Hloc.
           + destruct (decide (rmap_entry_nonempty ((b, ofs), r))) as [Hentry | Hentry].
             * rewrite ?Hloc /=.
               rewrite option_guard_True; last exact Hentry.
               rewrite option_guard_False.
               2: { by intro Hnot. }
               try rewrite Hnone.
               apply permjoin_def.permjoin_None_r.
             * rewrite ?Hloc /=.
               rewrite option_guard_False; last exact Hentry.
               rewrite option_guard_True; last exact Hentry.
               try rewrite Hnone.
               apply permjoin_def.permjoin_None_l.
           + rewrite ?Hloc /=.
             try rewrite Hnone.
             if_tac.
             apply permjoin_def.permjoin_None_l. done.
         - split.
           { (* threads_wellformed tp' *)
             unfold threads_wellformed.
             intros j cntj.
             unfold tp'.
             rewrite gLockSetCode.
             destruct (Nat.eq_dec j i) as [-> | Hneq].
             + rewrite gssThreadCode.
               split.
               change (Some (UNLOCK, [l]) <> None); auto. done.
             + erewrite gsoThreadCode by congruence.
               apply Htp_wf.
            }
           assert (Hnone : perm_of_res (ε, None) = (@None permission)).
           { rewrite /perm_of_res /=.
             destruct (eq_dec Share.bot Share.bot) as [_ | Hbad]; auto.
             if_tac; auto. done. if_tac; auto. done. }
           assert (Hparts : forall b ofs,
                      ((getThreadR cnti) # b ofs = Some Nonempty /\
                         newThreadPerm # b ofs = (getThreadR cnti) # b ofs /\
                         newLockPerm # b ofs = None) \/
                        ((getThreadR cnti) # b ofs <> Some Nonempty /\
                           newThreadPerm # b ofs = None /\
                           newLockPerm # b ofs = (getThreadR cnti) # b ofs)).
           {
             intros b ofs.
             rewrite <- (Heq_release b).
             rewrite <- (Heq1 b).
             unfold newLockPerm, σthread, σlock,
               rmap_lock_part, rmap_keep_part.
             rewrite !perm_of_rmap_lookup /resource_at !map_lookup_filter.
             destruct (σ1 !! (b, ofs)) as [r |] eqn:Hloc.
             - destruct (decide (rmap_entry_nonempty ((b, ofs), r))) as [Hentry | Hentry].
               + rewrite ?Hloc /=.
                 rewrite option_guard_True; last exact Hentry.
                 rewrite option_guard_False.
                 2: { by intro Hnot. }
                 left.
                 split; done.
               + rewrite ?Hloc /=.
                 rewrite option_guard_False; try done.
                 rewrite option_guard_True; try done.
                 right.
                 split; try done.
             - rewrite ?Hloc /=.
               destruct (eq_dec Share.bot Share.bot) as [_ | Hbad]; auto.
               + right.
                 split; try done.
                 if_tac; auto.
           }
           assert (Hthread_old : permMapLt newThreadPerm (getThreadR cnti)).
           {
             intros b ofs.
             destruct (Hparts b ofs) as [(Hne & Ht & Hl) | (Hne & Ht & Hl)].
             - rewrite Ht; apply po_refl.
             - rewrite Ht; apply event_semantics.po_None.
           }
           assert (Hlock_old : permMapLt newLockPerm (getThreadR cnti)).
           {
             intros b ofs.
             destruct (Hparts b ofs) as [(Hne & Ht & Hl) | (Hne & Ht & Hl)].
             - rewrite Hl; apply event_semantics.po_None.
             - rewrite Hl; apply po_refl.
           }
           assert (Hparts_disjoint : permMapsDisjoint newThreadPerm newLockPerm).
           {
             intros b ofs.
             destruct (Hparts b ofs) as [(Hne & Ht & Hl) | (Hne & Ht & Hl)]; rewrite Ht Hl.
             - exists ((getThreadR cnti) # b ofs).
               destruct ((getThreadR cnti) # b ofs); reflexivity.
             - exists ((getThreadR cnti) # b ofs).
               reflexivity.
           }
           assert (Hdisj_down : forall (p1 p2 q1 q2 : access_map),
                      permMapsDisjoint p1 p2 -> permMapLt q1 p1 -> permMapLt q2 p2 ->
                      permMapsDisjoint q1 q2).
           { intros p1 p2 q1 q2 Hd H1 H2 b ofs.
             eapply perm_union_lower_2.
             - apply (Hd b ofs).
             - apply (H1 b ofs).
             - apply (H2 b ofs).
           }
           assert (Hlockbytes : forall a z, a ∈ ls -> (0 <= z < Z.of_nat (size_chunk_nat Mptr))%Z ->
                                       newThreadPerm # (a.1) (a.2 + z)%Z = Some Nonempty /\
                                         newLockPerm # (a.1) (a.2 + z)%Z = None).
           {
             intros a z Ha Hz.
             pose proof (thread_rmap_lock_bytes_nonempty tp m ls Hcompat Hlocks i cnti σ1 Heq1 a z Ha Hz) as Holdσ.
             assert (Hold : (getThreadR cnti) # (a.1) (a.2 + z)%Z = Some Nonempty).
             { rewrite <- (Heq1 a.1); done. }
             destruct (Hparts a.1 (a.2 + z)%Z) as [(Hne & Ht & Hl) | (Hne & Ht & Hl)].
             - split; auto.
               rewrite Ht //.
             - exfalso; apply Hne; done.
           }
           assert (Hzero_range : (0 <= 0 < Z.of_nat (size_chunk_nat Mptr))%Z).
           { unfold Mptr. destruct Archi.ptr64; simpl.
             rewrite <- size_chunk_conv. cbn [size_chunk]. lia.
             rewrite <- size_chunk_conv. cbn [size_chunk]. lia. }
           assert (Hlock_addr : forall a, a ∈ ls -> newLockPerm # (a.1) a.2 = None).
           { intros a Ha.
             pose proof (Hlockbytes a 0 Ha Hzero_range) as [_ Hl].
             by rewrite Z.add_0_r in Hl. }
           assert (Hmax : getMaxPerm m_global' = getMaxPerm m) by done.
           + split.
             (* invariant tp' *)
             set (tpT := updThread cnti (Kresume c Vundef) newThreadPerm).
             assert (HinvT : invariant tpT).
             { unfold tpT. eapply ThreadPoolWF.invariant_decr; eauto. }
             assert (HresT : forall a, lockRes tpT a = lockRes tp a).
             { intro a. unfold tpT. by rewrite gsoThreadLPool. }
             assert (HheldT : lockRes tpT l1 = Some empty_map).
             { by rewrite HresT. }
             unfold tp'.
             rewrite Hl1eq.
             change (invariant (updLockSet tpT l1 newLockPerm)).
             destruct l1 as [b0 o0].
             eapply ThreadPoolWF.updLock_inv; eauto.
             * (* Payload disjoint with old locks *)
               intros a r Hneq Hres.
               rewrite HresT in Hres.
               eapply Hdisj_down.
               apply (no_race tp Hinvariant i a cnti r Hres); auto.
               intros b ofs.
               apply (Hlock_old b ofs).
               done.
             * (* Payload disjoint with all threads after updating *)
               intros j cntj.
               unfold tpT in cntj |- *.
               destruct (Nat.eq_dec i j) as [Heqij | Hneq].
               ++ subst j.
                  by rewrite gssThreadRes.
               ++ assert (cntj_old : containsThread tp j).
                  { eapply cntUpdate'; done.  }
                  erewrite @gsoThreadRes with (cntj := cntj_old); last congruence.
                  apply permMapsDisjoint_comm.
                  eapply Hdisj_down.
                  ** apply (no_race_thr tp Hinvariant i j cnti cntj_old Hneq).
                  ** done.
                  ** intros b ofs; apply po_refl.
            * (* Bounds at address  *)
              intros a r Hneq Hres.
              rewrite HresT in Hres.
              split.
              ++ apply ((proj2 (locks_data_lock_coh tp Hinvariant (b0, o0) empty_map HIRempty)) a r Hres).
              ++ rewrite (Hlock_addr a (Hlockdom a r Hres)).
                 apply event_semantics.po_None.
           * (* Payload where permission None at other lock. *)
             rewrite (Hlock_addr (b0, o0) Hl1mem).
             apply event_semantics.po_None.
           * (* All thread where their permission max Nonempty at lock. *)
             intros j cntj.
             apply ((proj1 (locks_data_lock_coh tpT HinvT (b0, o0) empty_map HheldT)) j cntj).
           * (* No lock starting in range of current lock *)
             intros ofs0 Hbetween.
             pose proof (lockRes_valid tpT HinvT b0 o0) as Hvalid.
             rewrite HheldT in Hvalid.
             apply (Hvalid ofs0 Hbetween).
           * (* No lock overlap current lock *)
             intros ofs0 Hbetween.
             destruct (lockRes tpT (b0, ofs0)) as [r |] eqn:Hres0; try done.
             pose proof (lockRes_valid tpT HinvT b0 ofs0) as Hvalid.
             rewrite Hres0 in Hvalid.
             specialize (Hvalid o0 Hbetween).
             by rewrite HheldT in Hvalid.
           * split.
             { eapply Build_mem_compatible.
               - (* Thread permissions. *)
                 intros j cntj.
                 unfold tp' in cntj |- *.
                 pose proof (cntUpdateL' _ _ cntj) as cntj_upd.
                 rewrite (gLockSetRes _ _ cntj_upd cntj).
                 destruct (Nat.eq_dec j i) as [-> | Hneq].
                 + rewrite gssThreadRes Hmax.
                   eapply permMapLt_trans with (q := getThreadR cnti); eauto.
                   apply (compat_th tp m Hcompat cnti).
                 + assert (cntj_old : containsThread tp j).
                   { eapply cntUpdate'; eauto. }
                   erewrite @gsoThreadRes with (cntj := cntj_old); last congruence.
                   rewrite Hmax.
                   apply (compat_th tp m Hcompat cntj_old).
               - (* Lock permissions. *)
                 intros a r Hres.
                 rewrite HlockRes_tp' in Hres.
                 unfold IRpost in Hres.
                 destruct (decide (a = l1)) as [Ha | Ha].
                 + subst a.
                   injection Hres as Hr.
                   subst r.
                   rewrite Hmax.
                   eapply permMapLt_trans with (q := getThreadR cnti); eauto.
                   apply (compat_th tp m Hcompat cnti).
                 + rewrite Hmax.
                   apply (compat_lp tp m Hcompat a r Hres).
               - (* Valid blocks. *)
                 intros a r Hres.
                 change (Mem.valid_block m a.1).
                 rewrite HlockRes_tp' in Hres.
                 unfold IRpost in Hres.
                 destruct (decide (a = l1)) as [Ha | Ha].
                 + subst a.
                   apply (lockRes_blocks tp m Hcompat l1 empty_map HIRempty).
                 + apply (lockRes_blocks tp m Hcompat a r Hres).
             }
             split.
             {
               unfold locks_coherent.
               intros a Ha.
               destruct (Hlocks a Ha) as (Hhas & Hvalue & Hrange_old).
               split.
               { rewrite HlockRes_tp'.
                 unfold IRpost.
                 destruct (decide (a = l1)); try done.
               }
               split.
               {
                 destruct (decide (a = l1)) as [Heqa | Hneq].
                 - subst a; right; apply Hload1'.
                 - rewrite (Hload_other a Ha Hneq).
                   destruct Hvalue as [[Hload Hempty0] | Hload].
                   + left; split; try done.
                     rewrite HlockRes_tp'.
                     unfold IRpost.
                     rewrite decide_False; try done.
                   + right; done.
               }
               intros j cntj Hp.
               unfold nonEmptyRangeCur.
               intros z Hz.
               rewrite restrPermMap_Cur_eq.
               unfold tp' in cntj |- *.
               pose proof (cntUpdateL' _ _ cntj) as cntj_upd.
               rewrite (gLockSetRes _ _ cntj_upd cntj).
               destruct (Nat.eq_dec j i) as [-> | Hneq].
               - rewrite gssThreadRes.
                 apply (proj1 (Hlockbytes a z Ha Hz)).
               - assert (cntj_old : containsThread tp j).
                 { eapply cntUpdate'; eauto. }
                 erewrite @gsoThreadRes with (cntj := cntj_old); last congruence.
                 pose proof (Hrange_old j cntj_old (compat_th tp m Hcompat cntj_old)) as Hrangej.
                 unfold nonEmptyRangeCur in Hrangej.
                 specialize (Hrangej z Hz).
                 rewrite restrPermMap_Cur_eq in Hrangej. done.
             }
             intros a r Hres.
             change (lockRes tp' a = Some r) in Hres.
             rewrite HlockRes_tp' in Hres.
             unfold IRpost in Hres.
             destruct (decide (a = l1)) as [Ha | Hneq]; try subst a; try done.
             apply (Hlockdom a r Hres).
          }
          destruct Hstep as (? & ? & ? & ? & ? & ?).
          split; done.
    - (* load = 1: lock is already unlocked *)
      iDestruct "Hls" as (I) "((%Hdom & %Hldisj) & HI & Hmap)".
      iDestruct "Hl" as (a) "(%Hva & Hlk & Hinv)".
      assert (Ha : a = l1).
      { unfold val2adr in Hva, Hval. destruct l; try contradiction; congruence. }
      subst a.
      iDestruct (own_valid_2 (A := gmap_view.gmap_viewR address (laterO (iPropO Σ)))
                  with "HI Hinv") as "#Hvalid".
      iDestruct (algebra.gmap_view_both_validI with "[$Hvalid]") as "(_ & #HeqR)".
      destruct (I !! l1) as [R0 |] eqn:HIlookup.
      2: { rewrite lookup_fmap HIlookup option_equivI /=.
           by iDestruct "HeqR" as "[]". }
      rewrite lookup_fmap HIlookup option_equivI /= later_equivI.
      iDestruct (big_sepM_delete _ _ l1 R0 HIlookup with "Hmap") as "[Hhere Hrest]".
      iDestruct "Hhere" as "[Hfree | Hheld]".
      + iDestruct "Hfree" as (qL σL pL) "(HfragL & (%HIR & %Hperm & %Hone & %Hnonempty) & HRlock)".
        iApply step_fupd_intro; first done.
        iNext.
        iExFalso.
        iAssert R with "[HRlock]" as "HRlock".
        { by iRewrite "HeqR" in "HRlock". }
        rewrite /exclusive_mpred.
        iApply ("Hexcl" with "[$HR $HRlock]").
      + iDestruct "Hheld" as (qL) "(_ & (%HIR & %Hzero))".
        rewrite Hzero in Hload1.
        inv Hload1.
        Unshelve.
        done.
  Qed.*) Admitted.
  *)

  Lemma rmap_auth_frag_init `{!inG Σ rmap_authUR} γ (σ1 : raw_rmapR) (Hv : ✓ σ1) :
    rmap_auth γ ∅ ∗ rmap_frag γ ∅ ==∗ rmap_auth γ σ1 ∗ rmap_frag γ σ1.
  Proof.
    rewrite /rmap_auth /rmap_frag -!own_op.
    iIntros "H"; iApply (own_update with "H").
    apply auth_update.
    assert (Hl : ((∅ : raw_rmapR), (∅ : raw_rmapR)) ~l~> (σ1 ⋅ ∅, σ1 ⋅ ∅)).
    { apply op_local_update_discrete; intros _. by rewrite right_id. }
    by rewrite !right_id in Hl.
  Qed.

  Lemma glob_coherent_enter (m : mem)
    (σ σi : resource_map.rmapUR share address (leibnizO resource))
    (p : access_map) (Hp : permMapLt p (getMaxPerm m)) :
    ✓ σ → glob_coherent m σ → rmap_included σi σ →
    mem_equiv.access_map_equiv (perm_of_rmap σi) p →
    coherent (restrPermMap Hp) σi.
  Proof.
    intros Hv Hglob Hincl Heq.
    pose proof (glob_coherent_bound _ _ Hglob) as Hbound.
    destruct Hglob as (Hlt & Hcoh).
    destruct Hincl as (fr & Hfr).
    assert (Hloc : ∀ l, (σi !! l : shresR) ≼ σ !! l).
    { intros l. exists (fr !! l). specialize (Hfr l). rewrite gmap.lookup_op // in Hfr. }
    intros (b, ofs). split; [|split].
    - (* bound *)
      intros Hge.
      pose proof (Hloc (b, ofs)) as Hl.
      rewrite (Hbound (b, ofs) Hge) in Hl.
      apply option_included in Hl as [Hn | (? & ? & _ & Hc & _)]; done.
    - (* contents: the value seen by the thread is the global one *)
      intros v Hv'.
      change (contents_at m (b, ofs) = v).
      destruct (Hcoh (b, ofs)) as (_ & Hcont & _).
      destruct (resR_le _ _ (Hv (b, ofs)) (Hloc (b, ofs))) as [_ [Hn | Hsnd]].
      + rewrite /resource_at Hn in Hv'. discriminate.
      + apply (Hcont v). rewrite /resource_at -Hsnd. done.
    - (* access: Cur of the restricted memory is p *)
      rewrite /access_cohere access_at_restrPermMap_Cur; cbn [fst snd].
      rewrite -(Heq b) perm_of_rmap_lookup //.
  Qed.

  Lemma coherent_perm_of_rmap_cur (m : mem) (σ : rmap) :
    coherent m σ → mem_equiv.access_map_equiv (perm_of_rmap σ) (getCurPerm m).
  Proof.
    intros Hcoh b. extensionality ofs.
    destruct (Hcoh (b, ofs)) as (_ & _ & H).
    rewrite perm_of_rmap_lookup /getCurPerm PMap.gmap.
    apply (eq_sym H).
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
  iMod (init_conc_VST_frag tt) as "H".
  iSpecialize ("H" $! Hinv).
  iDestruct "H" as (HG FS ES HL γ) "(Hstate & Hauth & Hfrag & Hfunspec & Hext & locks & _)".
  destruct HG as [HGin γh γm].
  set (HHfrag := Build_VSTGS _ _
                   ({| heapGS_invGS := Hinv;
                      heapGS_gen_heapGS := {| gen_heap_inG := HGin; gen_heap_name := γh; gen_meta_name := γm |};
                      heapGS_funspecGS := FS |} : heapGS Σ) ES).
  destruct (spr HHfrag HL ∅) as (b & q & (? & ? & Hinit) & Hsafe); [| done..].
  iMod (Hsafe with "[$Hstate $Hfunspec $Hext]") as (?) "(S & Heq & Hsafe & Hfcode & Hcore)".
  pose (mcode := proj1_sig init_mem).
  assert (Hinitcode : Genv.init_mem prog = Some mcode).
  { apply (proj2_sig init_mem). }
  iMod (code_ctx_alloc (HH := HHfrag) mcode with "[$Hfcode $Hcore]") as "#Hcode".
  clearbody mcode.
  iDestruct "Heq" as "%Heq".
  iUnfold state_interp_with_rmap, frag_mem_auth in "S".
  iDestruct "S" as "((%Hcoh & Hmem) & Hext)".
    iDestruct "Hmem" as "(%Hcoh0 & Hmem)".
  iDestruct (resource_map.resource_map_auth_valid with "Hmem") as %(_ & Hvalid).
  iMod (rmap_auth_frag_init γ σ Hvalid with "[$Hauth $Hfrag]") as "(Hauth & Hfrag)".
  assert (Hglob : glob_coherent (`init_mem) σ) by (exists Hcoh; done).
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
  set (tp := initial_machine _ _).
  assert (invariant tp) as Hinvariant by apply ThreadPoolWF.initial_invariant0.
  assert (HybridMachineSig.mem_compatible tp (`init_mem)) as Hcompat
        by apply ThreadPoolWF.initial_mem_compatible.
  assert (threads_wellformed tp) as Htp_wf by done.
  iAssert (threads_safe tp γ) with "[Hsafe Hfrag Hmem]" as "Hsafe".
  { subst tp.
    rewrite /threads_safe /=.
    iSplitL; last done.
    iExists (gen_heap_name heapGS_gen_heapGS), σ.
    unshelve iExists _; first done.
    iSplit; first by iPureIntro; done.
    iSplitR "Hfrag Hmem"; last (rewrite /thread_rmap; iFrame).
    rewrite /thread_safe.
    unshelve iExists _; first done.
    simpl; iApply (jsafe_jsafe_frag with "Hsafe"). }
  assert (locks_coherent tp (`init_mem) ∅) as Hlocks by done.
  clear Hcoh_empty.
  iAssert (@lock_state1 HHfrag HL inG2 γ (`init_mem) (∅ : gset address) (lockRes tp))
    with "[locks]" as "locks".
  { iApply (lock_state1_empty_change with "locks"). }
  assert (Hlockdom : forall a r, lockRes tp a = Some r -> a ∈ (∅ : gset address)).
  { intros a r Hr; subst tp. set_solver. }
  forget (proj1_sig init_mem) as m.
  forget (@nil Events.machine_event) as tr.
  clearbody tp.
  set (ls := (∅ : gset address)) in Hlocks, Hlockdom |- *.
  clearbody ls.
  clear dependent b x q.
  clear Heq Hcoh Hcoh0 Hvalid.
  Local Opaque lock_state1.
  iLöb as "IH" forall (sch tr tp m n ls σ Htp_wf Hinvariant Hcompat Hlocks Hlockdom Hglob).
  destruct n as [|n].
  { iPureIntro. constructor. }
  destruct sch as [|i sch].
  { iApply step_fupdN_intro; first done; iPureIntro. constructor; done. }
  simpl; destruct (lt_dec i (pos.n (OrdinalPool.num_threads tp))) as [Hlt_thrd |Hge_thrd].
  2 : {
    iApply step_fupd_intro; try done.
    iNext.
    iAssert (|={⊤}[∅]▷=>^n ∀ U'', ⌜HybridMachineSig.HybridCoarseMachine.csafe (U'', tr, tp) m n⌝) with "[-]" as "H".
    { rewrite step_fupdN_plain_forall //.
      iIntros (U'').
      iApply ("IH" $! U'' tr tp m n ls with "[] [] [] [] [] [] Hext Hauth Hsafe locks"); try done.
    }
    iApply (step_fupdN_mono with "H"); iPureIntro.
    intros Hsafe.
    eapply HybridMachineSig.HybridCoarseMachine.AngelSafe
        with (tr := []); simpl; rewrite seq.cats0; last apply Hsafe.
    eapply HybridMachineSig.schedfail; eauto.
    rewrite /containsThread /= /OrdinalPool.containsThread.
    intros ?.
    pose proof (@ssrnat.leP (S i) (pos.n (OrdinalPool.num_threads tp))) as Hle; inv Hle; [lia | congruence].
  }
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
        iApply ("IH" $! _ _ _ _ _ _ with "[] [] [] [] [] [] Hext Hauth Hsafe locks"); try done.
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
                 with "[%] [%] [%] [%] [%] [] Hext Hauth [Hsafe Hfragi Hsafei] locks"); try done.
        - intros j cntj.
          destruct (eq_dec j i) as [-> | Hneq].
          + rewrite (gssThreadCC cnti (Kblocked s) cntj) /= Hat_ext //.
          + pose proof (cntUpdateC' (Kblocked s) cnti cntj) as cntj0.
            rewrite -gsoThreadCC //; by apply Htp_wf.
        - by apply ThreadPoolWF.updThreadC_invariant.
        - eapply (StepLemmas.updThreadC_compatible (asmSem := Sem)); done.
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
      iMod "Hsafei" as "Hsafei".
      rewrite /thread_rmap.
      iDestruct "Hfragi" as "(Hfragi & Hmemi)".
      iDestruct (rmap_auth_valid with "Hauth") as %Hvσ.
      iDestruct (rmap_auth_frag_included with "[$Hauth $Hfragi]") as %Hincl1.
      (* enter: coherence of thread i with its restricted memory *)
      assert (Hcoh_i : coherent (restrPermMap (Hcompat i cnti)) σ1).
      { eapply glob_coherent_enter; done. }
      assert (Hglob_i : glob_coherent (restrPermMap (Hcompat i cnti)) σ).
      { apply glob_coherent_restrPermMap; done. }
      iDestruct ("Hsafei" $! (restrPermMap (Hcompat i cnti)) σ1 with "[Hauth Hext Hfragi Hmemi]")
        as "[Hhalt | [Hstep | Hextc]]".
      { rewrite /thread_state_interp /conc_state_interp /thread_mem_auth /thread_rmap.
        iExists σ; iSplit; first done.
        iSplitL "Hauth Hext"; first iFrame.
        iSplit; first done.
        iFrame. }
      (* contradiction *)
      { iDestruct "Hhalt" as (i0 Hhalt') "_". done. }
      2 : { iDestruct "Hextc" as (??? Hext') "?". simpl in Hext'; congruence. }
      (* HStep *)
      iMod "Hstep" as (c' m' σ') "(%Hstep & S & Hsafei)".
      rewrite /thread_state_interp /conc_state_interp /thread_mem_auth /thread_rmap.
      iDestruct "S" as (σnew) "(%Hglob' & (Hauth & Hext) & %Hcoh' & Hfragi & Hmemi)".
      iApply step_fupd_intro; first done.
      iNext.
      pose proof Hstep as Hstep'.
      apply (ev_step_ax2 (Clight_evsem.CLC_evsem ge)) in Hstep' as (ev & Hstep').
      assert (Hmemstep : mem_step (restrPermMap (Hcompat i cnti)) m').
      { eapply (CLC_corestep_mem _ _ (restrPermMap (Hcompat i cnti))); eauto. }
      assert (mem_compatible (updThread cnti (Krun c') (getCurPerm m')) m') as Hcompat'.
      { by eapply (CoreLanguageDry.corestep_compatible (Sem := Sem)). }
      assert (Hlock_loads : forall l0, l0 ∈ ls ->
                Mem_load_unchecked Mptr m l0.1 l0.2 = Mem_load_unchecked Mptr m' l0.1 l0.2).
      { intros l0 Hl0.
        pose proof (Hlocks l0 Hl0) as Hlock0.
        destruct Hlock0 as (_ & _ & Hne).
        specialize (Hne i cnti (Hcompat i cnti)).
        rewrite <- (Mem_unchecked_restrPermMap m (getThreadR cnti) (Hcompat i cnti) l0).
        unfold Mem_load_unchecked.
        f_equal.
        eapply mem_step_preserves_lock_bytes; eauto. }
      iAssert (lock_state1 γ m' ls (lockRes (updThread cnti (Krun c') (getCurPerm m'))))
        with "[locks]" as "locks".
      { Local Transparent lock_state1.
        rewrite /lock_state1.
        iDestruct "locks" as (I) "(Hdom & Hown & Hmap)".
        iExists I.
        iFrame "Hdom Hown".
        iApply (big_sepM_mono with "Hmap").
        iIntros (a R Ha) "H".
        iDestruct "H" as "[Hunlocked | Hlocked]".
        - iLeft.
          iDestruct "Hunlocked" as (σlock l0) "(Hfrag & (%HIR & %Heq & %Hload & %Hnonempty) & HR)".
          iExists σlock, l0.
          iFrame "Hfrag HR".
          iPureIntro.
          assert (Ha_ls : a ∈ ls) by (eapply Hlockdom; eauto).
          split; first by rewrite gsoThreadLPool.
          split; first done.
          split; last done.
          rewrite -(Hlock_loads a Ha_ls). exact Hload.
        - iRight.
          iDestruct "Hlocked" as %(HIR & Hload).
          iPureIntro.
          assert (Ha_ls : a ∈ ls) by (eapply Hlockdom; eauto).
          split; first by rewrite gsoThreadLPool.
          rewrite -(Hlock_loads a Ha_ls) //.
      }
      assert (Hlockdom' : forall a r,
                 lockRes (updThread cnti (Krun c') (getCurPerm m')) a = Some r -> a ∈ ls).
      { intros a r Hr.
        rewrite gsoThreadLPool in Hr.
        eapply Hlockdom; eauto.
      }
      iSpecialize ("IH" $! _ _ (updThread cnti (Krun c') (getCurPerm m')) m' n ls σnew
          with "[%] [%] [%] [%] [%] [%] Hext Hauth [Hsafe Hsafei Hfragi Hmemi] locks"); try done.
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
        split; try done.
        split.
        ** rewrite -(Hlock_loads l0 Hl0) //.
        ** intros i0 cnti0 Hp0.
           destruct (Nat.eq_dec i i0) as [-> | Hneq].
           ++ have Hne := HnonEmpty i0 cnti (Hcompat i0 cnti).
              rewrite /nonEmptyRangeCur in Hne |- *.
              intros i1 Hi1.
              rewrite restrPermMap_Cur_eq.
              rewrite (gssThreadRes cnti (Krun c') (getCurPerm m') cnti0) /=.
              rewrite /getCurPerm PMap.gmap /=.
              eapply mem_step_preserves_nonempty_range; eauto.
           ++ assert (cnti_old : containsThread tp i0); try by eapply cntUpdate'; eauto.
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
           iDestruct "Hy" as (q0 σ0 cnty) "(%Hqy & Hsafe_y & Hfrag_y & Hmem_y)".
           replace (0 + k) with k in * by lia.
           assert (Hneq' : i <> k) by lia.
           set (cnty' := @cntUpdate _ _ _ i k tp (Krun c') (getCurPerm m') cnti cnty).
           iExists q0, σ0, cnty'.
           iSplit.
           { iPureIntro. subst cnty'. erewrite gsoThreadRes; eauto. }
           iSplitL "Hsafe_y".
           { rewrite /thread_safe.
             iDestruct "Hsafe_y" as (cnty0) "Hsafe_y".
             set (cnty0' := @cntUpdate _ _ _ i k tp (Krun c') (getCurPerm m') cnti cnty0).
             iExists cnty0'. subst cnty0'.
             rewrite gsoThreadCode; auto.
           }
           rewrite /thread_rmap; iFrame.
        ** (* selected thread *)
           set (cnti' := @cntUpdate _ _ _ i i tp (Krun c') (getCurPerm m') cnti cnti).
           iExists q, σ', cnti'.
           iSplit.
           { iPureIntro. subst cnti'. rewrite gssThreadRes.
             apply coherent_perm_of_rmap_cur; auto. }
           iSplitL "Hsafei".
           { rewrite /thread_safe. iExists cnti'. subst cnti'. rewrite gssThreadCode //. }
           rewrite /thread_rmap; iFrame.
      * iApply (step_fupdN_mono with "IH").
        iPureIntro; intros Hsafe.
        eapply HybridMachineSig.HybridCoarseMachine.CoreSafe; last done.
        rewrite /HybridMachineSig.MachStep /=.
        change (i :: sch) with (HybridMachineSig.yield (i :: sch)) at 2.
        change m' with (HybridMachineSig.diluteMem m') at 3.
        eapply HybridMachineSig.thread_step; first done.
        instantiate (1 := ev).
        eapply step_dry with (c := s) (m1 := restrPermMap (Hcompat i cnti)) (c' := c') (ev := ev); eauto.
    - (* Kblocked: HybridMachineSig.sync_step *)
    pose proof (Htp_wf _ cnti) as Hwfi; rewrite Hi in Hwfi.
    rewrite jsafe_frag_unfold /jsafe_frag_pre.
    iMod "Hsafei" as "Hsafei".
    rewrite /thread_rmap.
    iDestruct "Hfragi" as "(Hfragi & Hmemi)".
    iDestruct (rmap_auth_valid with "Hauth") as %Hvσ.
    iDestruct (rmap_auth_frag_included with "[$Hauth $Hfragi]") as %Hincl1.
    assert (Hcoh_i : coherent (restrPermMap (Hcompat i cnti)) σ1).
    { eapply glob_coherent_enter; done. }
    assert (Hglob_i : glob_coherent (restrPermMap (Hcompat i cnti)) σ).
    { apply glob_coherent_restrPermMap; auto. }
    iDestruct ("Hsafei" $! (restrPermMap (Hcompat i cnti)) σ1 with "[Hauth Hext Hfragi Hmemi]")
      as "[Hhalt | [Hstep | Hextc]]".
    { rewrite /thread_state_interp /conc_state_interp /thread_mem_auth /thread_rmap.
      iExists σ; iSplit; first done.
      iSplitL "Hauth Hext"; first iFrame.
      iSplit; first done.
      iFrame.
    }
    (* impossible: blocked external call cannot be halted *)
    { iDestruct "Hhalt" as (? Hhalt') "?"; destruct s; done. }
    (* impossible: corestep cannot start from an external state *)
    { iMod "Hstep" as (??? Hstep) "?"; apply cl_corestep_not_at_external in Hstep; done. }
    (* external case *)
    iDestruct "Hextc" as (e args x) "(%Hat_ext & S & Hpre & Hpost)".
    simpl in Hat_ext.
    iAssert (∃ ls' : gset address,
                |={⊤}[∅]▷=> ∃ (tp' : t (ThreadPool := OrdinalPool.OrdinalThreadPool)) m' ev σnew,
               ⌜threads_wellformed tp' ∧ invariant tp' ∧ mem_compatible tp' m' ∧
                locks_coherent tp' m' ls' ∧
                (forall a r, lockRes tp' a = Some r -> a ∈ ls') ∧
                glob_coherent m' σnew ∧
                syncStep true cnti Hcompat tp' m' ev⌝ ∧
            ext_auth () ∗ rmap_auth γ σnew ∗ threads_safe tp' γ ∗
              lock_state1 γ m' ls' (lockRes tp')) with "[Hpost Hsafe locks Hpre S]" as "Hsafe".
    2 : {
      iDestruct "Hsafe" as (ls') "Hsafe".
      iMod "Hsafe".
      iIntros "!> !>".
      iMod "Hsafe" as (tp' m' ev σnew) "(%Hsync & Hext & Hauth & Hth & locks)".
      destruct Hsync as (Htp_wf' & Hinvariant' & Hcompat' & Hlocks' & Hlockdom' & Hglob' & Hsync).
      iAssert (|={⊤}[∅]▷=>^n ∀ U'', ⌜HybridMachineSig.HybridCoarseMachine.csafe
                 (U'', tr ++ [Events.external i ev], tp') m' n⌝) with "[-]" as "H".
      { rewrite step_fupdN_plain_forall //.
        iIntros.
        iApply ("IH" $! x0 (tr ++ [Events.external i ev]) tp' m' n ls' σnew
                 with "[] [] [] [] [] [] Hext Hauth Hth locks"); try done. }
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
    + (* acquire *)  iExists ls. admit.
    + (* release *)  iExists ls. admit.
    + (* makelock *) admit.
    + (* freelock *) admit.
    + (* spawn *)    iExists ls. admit.
  
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
