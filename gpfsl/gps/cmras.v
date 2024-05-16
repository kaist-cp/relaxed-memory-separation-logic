From gpfsl.gps Require Export protocols.
From gpfsl.logic Require Export atomic_cmra.
From gpfsl.algebra Require Import to_agree.
From gpfsl.base_logic Require Import history.

Require Import iris.prelude.options.

Notation stateT Prtcl := (gmap time Prtcl)%type.

Section CMRAs.
  Context {Prtcl : protocolT}.

  Definition stateMapUR : ucmra := agreeMR time Prtcl.
  Definition toStateMapUR : (stateT Prtcl) → stateMapUR := to_agreeM.

  (* cmra for protocol states *)
  Definition gpsR : cmra := authR stateMapUR.
  Definition stateMap_auth ζ : gpsR := ● toStateMapUR ζ ⋅ ◯ toStateMapUR ζ.
  Definition stateMap_frag ζ : gpsR := ◯ toStateMapUR ζ.

  Lemma stateMap_idemp (ζ : stateMapUR) : ζ ⋅ ζ ≡ ζ.
  Proof. by apply agreeM_idemp. Qed.

  Lemma stateMap_valid ζ : ✓ toStateMapUR ζ.
  Proof. by apply to_agreeM_valid. Qed.

  Lemma stateMap_included ζ1 ζ2:
    ζ1 ⊆ ζ2 ↔ toStateMapUR ζ1 ≼ toStateMapUR ζ2.
  Proof. symmetry. apply to_agreeM_included. Qed.

  Lemma stateMap_eq ζ1 ζ2:
    toStateMapUR ζ1 ≡ toStateMapUR ζ2 → ζ1 = ζ2.
  Proof. apply to_agreeM_agree. Qed.

  Lemma stateMap_local_update ζ ζ' (ζ0 : stateMapUR) :
    ζ ⊆ ζ' → (toStateMapUR ζ, ζ0) ~l~> (toStateMapUR ζ', toStateMapUR ζ').
  Proof. apply to_agreeM_local_update. Qed.
End CMRAs.

Arguments gpsR _ : clear implicits.

(* Full GPS ghosts *)
Class gpsG Σ Prtcl := {
  gps_inG : inG Σ (gpsR Prtcl);
}.
Local Existing Instance gps_inG.

Definition gpsΣ Prtcl : gFunctors :=
  #[ GFunctor (constRF (gpsR Prtcl)) ].
Global Instance subG_gpsΣ {Σ} Prtcl : subG (gpsΣ Prtcl) Σ → gpsG Σ Prtcl.
Proof. solve_inG. Qed.
