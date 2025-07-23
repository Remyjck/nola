(** * Nola's later-free invariants *)

From nola.bi Require Export internal modw.
From nola.bi Require Import wpw.
From nola.iris Require Export iprop.
From nola.iris Require Import sinv.
From iris.base_logic.lib Require Export wsat invariants.
From iris.algebra Require Import gset.
From iris.proofmode Require Import proofmode.
Import iPropAppNotation ModwNotation WpwNotation.

Implicit Type (FML : oFunctor) (i : positive) (N : namespace).

(** Ghost state for invariants *)
Class inv'GpreS Σ : Type := inv'GpreS_sinv : sinvGpreS Σ.
Local Existing Instance inv'GpreS_sinv.
Class inv'GS Σ : Type := inv'GS_sinv : sinvGS Σ.
Local Existing Instance inv'GS_sinv.
Definition inv'Σ := sinvΣ.
#[export] Instance subG_inv'Σ
  `{!subG (inv'Σ Σ) Σ} : inv'GpreS Σ.
Proof. solve_inG. Qed.

Section inv.
  Context `{!inv'GS Σ, !invGS_gen hlc Σ, !Csem CON JUDG Σ, !Jsem JUDG (iProp Σ)}.
  Implicit Type (Px : cif CON Σ).

  Import CsemNotation.

  (** [inv_tok]: Invariant token *)
  Local Definition inv_tok_def (N : namespace) Px : iProp Σ :=
    ∃ i, ⌜i ∈ (↑N:coPset)⌝ ∧ sinv_tok i Px.
  Local Definition inv_tok_aux : seal inv_tok_def. Proof. by eexists. Qed.
  Definition inv_tok := inv_tok_aux.(unseal).
  Local Lemma inv_tok_unseal : inv_tok = inv_tok_def.
  Proof. exact: seal_eq. Qed.

  (** [inv_tok] is non-expansive *)
  #[export] Instance inv_tok_ne N : NonExpansive (inv_tok N).
  Proof. rewrite inv_tok_unseal. solve_proper. Qed.
  #[export] Instance inv_tok_proper N : Proper ((≡) ==> (⊣⊢)) (inv_tok N).
  Proof. apply ne_proper, _. Qed.
  (** [inv_tok] is persistent *)
  #[export] Instance inv_tok_persistent {N Px} : Persistent (inv_tok N Px).
  Proof. rewrite inv_tok_unseal. exact _. Qed.
  (** [inv_tok] is timeless for discrete formulas *)
  #[export] Instance inv_tok_timeless `{!Discrete ⟦Px⟧ᶜ} {N} :
    Timeless (inv_tok N Px).
  Proof. rewrite inv_tok_unseal. exact _. Qed.

  (** Weaken the namespace of [inv_tok] *)
  Lemma inv_tok_subset {N N' Px} : ↑N ⊆@{coPset} ↑N' →
    inv_tok N Px ⊢ inv_tok N' Px.
  Proof. rewrite inv_tok_unseal=> ?. iIntros "[%[% $]] !%". set_solver. Qed.

  (** Semantics *)
  Local Definition inv_sem i P : iProp Σ :=
    P ∗ ownD {[i]} ∨ ownE {[i]}.
  (** [inv_sem sm] is non-expansive when [sm] is *)
  Local Lemma inv_sem_ne :
   ⊢@{iProp Σ} ∀ i, internal_ne (inv_sem i).
  Proof.
    iIntros (???) "≡". unfold inv_sem. by iRewrite ("≡").
  Qed.
  (** [inv_sem sm] is always timeless when [sm] is *)
  Local Instance inv_sem_timeless `{!∀ (P : iProp Σ), Timeless (P)} {i P} :
    Timeless (inv_sem i P).
  Proof. unfold inv_sem, ownD, ownE. exact _. Qed.

  (** World satisfaction *)
  Local Definition inv_wsat_def : iProp Σ := sinv_wsat inv_sem.
  Local Definition inv_wsat_aux : seal inv_wsat_def. Proof. by eexists. Qed.
  Definition inv_wsat := inv_wsat_aux.(unseal).
  Local Lemma inv_wsat_unseal : inv_wsat = inv_wsat_def.
  Proof. exact: seal_eq. Qed.

  (** [inv_wsat] is non-expansive *)
  (* #[export] Instance inv_wsat_ne : NonExpansive inv_wsat.
  Proof. rewrite inv_wsat_unseal /inv_wsat_def /inv_sem. solve_proper. Qed. *)
  (* #[export] Instance inv_wsat_proper : Proper ((≡) ==> (≡)) inv_wsat.
  Proof. apply ne_proper, _. Qed. *)

  (** [inv_wsat] is timeless if [sm] is always timeless
    and the underlying ofe is discrete *)
  (* #[export] Instance inv_wsat_timeless
    `{!OfeDiscrete (FML $oi Σ), !∀ Px, Timeless (sm Px)} :
    Timeless (inv_wsat).
  Proof. rewrite inv_wsat_unseal. exact _. Qed. *)
  (** Allocate [ownD] *)
  Lemma alloc_ownD (I : gset positive) N :
    ⊢ |==> ∃ i, ⌜i ∉ I⌝ ∧ ⌜i ∈ (↑N:coPset)⌝ ∧ ownD {[i]}.
  Proof.
    iMod (own_unit (gset_disjUR positive) disabled_name) as "D".
    iMod (own_updateP with "[$]") as (x) "[X D]".
    { apply (gset_disj_alloc_empty_updateP_strong'
        (λ i, i ∉ I ∧ i ∈ (↑N:coPset)))=> J.
      case: (fresh_inv_name (I ∪ J) N)=> [i[/not_elem_of_union[??]?]].
      by exists i. }
    iDestruct "X" as %[i[->[??]]]. iModIntro. iExists i. iSplit; by [|iSplit].
  Qed.
  (** Access [ownE] *)
  Local Lemma ownE_subset {E F} : F ⊆ E → ownE E ⊣⊢ ownE F ∗ ownE (E∖F).
  Proof.
    move=> ?. rewrite {1}(union_difference_L F E); [|done].
    by rewrite ownE_op; [|set_solver].
  Qed.
  (** Access [ownE] from [fupd] *)
  Local Lemma fupd_ownE_acc {E F} : F ⊆ E →
    ⊢ |={E,E∖F}=> ownE F ∗ (ownE F ={E∖F,E}=∗ True).
  Proof.
    rewrite fancy_updates.uPred_fupd_unseal /fancy_updates.uPred_fupd_def=> FE.
    rewrite (ownE_subset FE). by iIntros "[$[$$]]!>!>$[$$]!>".
  Qed.
  Local Lemma fupd_ownE_acc_in {i E F} : i ∈ F → F ⊆ E →
    ⊢ |={E,E∖F}=> ownE {[i]} ∗ (ownE {[i]} ={E∖F,E}=∗ True).
  Proof.
    move=> iF FE. iMod (fupd_ownE_acc FE) as "[F cl]".
    rewrite (ownE_subset (E:=F) (F:={[i]})); [|set_solver].
    iDestruct "F" as "[$ F∖i]". iIntros "!> i". iApply ("cl" with "[$]").
  Qed.

  (** Allocate [inv_tok] suspending the world satisfaction *)
  Lemma inv_tok_alloc_suspend Px N :
    inv_wsat ==∗ inv_tok N Px ∗ (⟦Px⟧ᶜ -∗ inv_wsat).
  Proof.
    rewrite inv_tok_unseal inv_wsat_unseal. iIntros "W".
    iDestruct (sinv_tok_alloc_suspend Px with "W") as (I) "big".
    iMod (alloc_ownD I N) as (???) "D". iMod ("big" with "[//]") as "[#i →W]".
    iModIntro. iSplitR; [by iFrame "i"|]. iIntros "?". iApply "→W". iLeft.
    iFrame.
  Qed.
  (** Allocate [inv_tok] *)
  Lemma inv_tok_alloc Px N : ⟦Px⟧ᶜ =[inv_wsat]=∗ inv_tok N Px.
  Proof.
    iIntros "? W". iMod (inv_tok_alloc_suspend with "W") as "[$ →W]". iModIntro.
    by iApply "→W".
    Unshelve.
  Qed.

  (** Allocate [inv_tok] before storing the content *)
  Lemma inv_tok_alloc_open {E} Px N : ↑N ⊆ E →
    ⊢ |=[inv_wsat]{E, E∖↑N}=> inv_tok N Px ∗
      (⟦Px⟧ᶜ =[inv_wsat]{E∖↑N, E}=∗ True).
  Proof.
    rewrite inv_tok_unseal inv_wsat_unseal=> NE. iIntros "W".
    iDestruct (sinv_tok_alloc_suspend Px with "W") as (I) "big".
    iMod (alloc_ownD I N) as (?? iN) "D".
    iMod ("big" with "[//]") as "[#sm →W]".
    iMod (fupd_ownE_acc_in iN NE) as "[i cl]".
    iDestruct ("→W" with "[$i]") as "$". iModIntro.
    iSplit; [iExists _; by iSplit|]. iIntros "Px W".
    iDestruct (sinv_tok_acc with "sm W") as "[[[_ D']|i] →W]".
    { iDestruct (ownD_singleton_twice with "[$D $D']") as %[]. }
    iMod ("cl" with "i") as "_". iModIntro. iSplit; [|done]. iApply "→W".
    iLeft. iFrame.
  Qed.

  (** Access using [inv_tok] *)
  Lemma inv_tok_acc {N E Px} : ↑N ⊆ E →
    inv_tok N Px =[inv_wsat]{E,E∖↑N}=∗
      ⟦Px⟧ᶜ ∗ (⟦Px⟧ᶜ =[inv_wsat]{E∖↑N,E}=∗ True).
  Proof.
    rewrite inv_tok_unseal inv_wsat_unseal=> NE. iIntros "[%i[%iN #sm]] W".
    iMod (fupd_ownE_acc_in iN NE) as "[i cl]".
    iDestruct (sinv_tok_acc with "sm W") as "[in →W]".
    iDestruct "in" as "[[$ D]|i']"; last first.
    { iDestruct (ownE_singleton_twice with "[$i $i']") as %[]. }
    iDestruct ("→W" with "[$i]") as "$". iIntros "!> Px W".
    iDestruct (sinv_tok_acc with "sm W") as "[[[_ D']|i] →W]".
    { iDestruct (ownD_singleton_twice with "[$D $D']") as %[]. }
    iMod ("cl" with "i") as "_". iModIntro. iSplit; [|done]. iApply "→W".
    iLeft. iFrame.
  Qed.
  (** Access using [inv_tok] via view shift, for presentation *)
  Lemma inv_tok_acc_vs {N Px E Q R} : ↑N ⊆ E →
    □ (⟦Px⟧ᶜ -∗ Q =[inv_wsat]{E∖↑N}=∗ ⟦Px⟧ᶜ ∗ R) -∗
      □ (inv_tok N Px -∗ Q =[inv_wsat]{E}=∗ R).
  Proof.
    iIntros (?) "#vs !> i Q". iMod (inv_tok_acc with "i") as "[Px cl]"; [done|].
    iMod ("vs" with "Px Q") as "[Px $]". by iApply "cl".
  Qed.

  (** Access using [inv_tok] for persistent propositions *)
  Lemma inv_tok_acc_persistent {N Px E} : Persistent (⟦Px⟧ᶜ) → ↑N ⊆ E →
    inv_tok N Px =[inv_wsat]{E}=∗ ⟦Px⟧ᶜ.
  Proof.
    iIntros (??) "i". iMod (inv_tok_acc with "i") as "[#Px cl]"; [done|].
    iFrame "Px". by iApply "cl".
  Qed.

  Lemma sem_alteration {N Px Qx} :
    (⟦ Px ⟧ᶜ ∗-∗ ⟦ Qx ⟧ᶜ) ->
    inv_tok N Px ∗-∗ inv_tok N Qx.
  Proof.
    intros Heq.
    rewrite inv_tok_unseal /inv_tok_def.
    iSplit; iIntros "(%i & %Hin & Hinv)";
      iExists i; iFrame "%"; by iApply (sem_alteration Heq).
  Qed.
End inv.

Section inv_wp.
  Context `{!inv'GS Σ, !iris'GS_gen hlc Λ Σ}.

  Import CsemNotation.

  Context `{!Csem CON JUDG Σ, !Jsem JUDG (iProp Σ)}.
  Implicit Type (Px : cif CON Σ).

  (** Access using [inv_tok] via [twp], for presentation *)
  Lemma inv_tok_acc_twp `{!Atomic (stuckness_to_atomicity s) e}
    {N Px E Q Ψ} :
    ↑N ⊆ E → to_val e = None →
    [[{ ⟦Px⟧ᶜ ∗ Q }]][inv_wsat] e @ s; E∖↑N [[{ v, RET v; ⟦Px⟧ᶜ ∗ Ψ v }]] -∗
      [[{ inv_tok N Px ∗ Q }]][inv_wsat] e @ s; E [[{ v, RET v; Ψ v }]].
  Proof.
    iIntros (??) "#twp %Φ !> [i Q] →Φ".
    iMod (inv_tok_acc with "i") as "[Px cl]"; [done..|].
    iApply ("twp" with "[$Px $Q //]"). iIntros (?) "[Px Ψ]".
    iMod ("cl" with "Px") as "_". iModIntro. by iApply "→Φ".
  Qed.
End inv_wp.

(** Allocate [inv_wsat] *)
Lemma inv_wsat_alloc `{!inv'GpreS Σ, !invGS_gen hlc Σ} :
  ⊢ |==> ∃ _ : inv'GS Σ, inv_wsat.
Proof.
  iMod sinv_wsat_alloc as (?) "W". iModIntro. iExists _.
  rewrite inv_wsat_unseal. iApply "W". iApply inv_sem_ne.
Qed.
