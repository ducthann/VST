(*
   Whole-program initialization with an explicitly exposed resource map.

   This theorem is the [semax_prog_rule] analogue for
   [initial_world_with_rmap].  It keeps the authoritative resource map [σ]
   visible, together with the exact pointwise correspondence between
   [perm_of_rmap σ] and the current CompCert permission map.
 *)

Set Warnings "-notation-overridden,-custom-entry-overridden,-hiding-delimiting-key".

From iris.base_logic.lib Require Import iprop.
Require Import VST.veric.semax_prog.
Require Import VST.concurrency.juicy.initial_world_with_rmap.
Require Import VST.veric.juicy_extspec.

Set Warnings "notation-overridden,custom-entry-overridden,hiding-delimiting-key".

Import Ctypes Clight.

Set Bullet Behavior "Strict Subproofs".

Section semax_prog_with_rmap.
  Context (Espec : OracleKind).
  Context {Σ : gFunctors}.
  Context `{!VSTGS (OK_ty Espec) Σ}.
  
Lemma semax_prog_rule_with_rmap {CS : compspecs} :
  forall V G prog m h z,
    postcondition_allows_exit tint ->
    semax_prog (C := CS) prog z V G ->
    Genv.init_mem prog = Some m ->
    { b : block & { q : CC_core &
                          (Genv.find_symbol
                             (globalenv prog) (prog_main prog) = Some b) *

                            (exists m',
                                semantics.initial_core
                                  (cl_core_sem (globalenv prog))
                                  h m q m'
                                  (Vptr b Ptrofs.zero) nil) *

                            (state_interp Mem.empty z ∗
                               funspec_auth ∅ ∗
                               has_ext z
                               ⊢ |==>
                               ∃ σ : rmap,
                                 (frag_mem_auth 1 m σ ∗ ext_auth z) ∗
                                   ⌜access_map_pointwise_eq
                                   (perm_of_rmap σ)
                                   (getCurPerm m)⌝ ∗
                                   (jsafeN OK_spec
                                      (globalenv prog) ⊤ z q ∧
                                      matchfunspecs
                                        (globalenv prog) G))
    } }%type.
