From gpfsl.lang Require Export notation.
From gpfsl.logic Require Import repeat_loop new_delete.

Require Import iris.prelude.options.

(** Arc implementation is based on the paper `RustBelt Meets Relaxed Memory` by Dang et al.
    [https://gitlab.mpi-sws.org/iris/lambda-rust/-/blob/masters/weak_mem/theories/lang/arc.v] *)

Definition strong_count : val :=
  λ: ["l"], !ʳˡˣ"l".

Definition weak_count : val :=
  λ: ["l"], !ʳˡˣ("l" +ₗ #1).

Definition clone_arc : val :=
  rec: "clone" ["l"] :=
    let: "strong" := !ʳˡˣ"l" in
    (* fully relaxed CAS *)
    if: casʳˡˣ("l", "strong", ("strong" + #1)) then #☠ else "clone" ["l"].

Definition clone_weak : val :=
  rec: "clone" ["l"] :=
    let: "weak" := !ʳˡˣ("l" +ₗ #1) in
    if: casʳˡˣ(("l" +ₗ #1), "weak", ("weak" + #1)) then #☠ else "clone" ["l"].

(*  // the value usize::MAX acts as a sentinel for temporarily "locking" the
    // ability to upgrade weak pointers or downgrade strong ones; this is used
    // to avoid races in `make_mut` and `get_mut`.
    Her we use -1 for usize::MAX.
*)
Definition downgrade : val :=
  rec: "downgrade" ["l"] :=
    let: "weak" := !ʳˡˣ("l" +ₗ #1) in
    if: "weak" = #(-1) then
      (* -1 in weak indicates that somebody locked the counts; let's spin. *)
      "downgrade" ["l"]
    else
      (*
        // Unlike with Clone(), we need this to be an Acquire read to
        // synchronize with the write coming from `is_unique`, so that the
        // events prior to that write happen before this read.
        // Why needed? to prevent CASing weak counter from -1 to 0
      *)
      (* acquire CAS, i.e. relaxed fail read, acquire success read, relaxed write *)
      if: casᵃᶜ(("l" +ₗ #1), "weak", ("weak" + #1)) then #☠
      else "downgrade" ["l"].

Definition upgrade : val :=
  rec: "upgrade" ["l"] :=
    let: "strong" := !ʳˡˣ"l" in
    if: "strong" = #0 then #false
    else
      if: casʳˡˣ("l", "strong", ("strong" + #1)) then #true
      else "upgrade" ["l"].

Definition drop_weak : val :=
  rec: "drop" ["l"] :=
    (* This can ignore the lock because the lock is only held when there
       are no other weak refs in existence, so this code will never be called
       with the lock held. *)
    let: "weak" := !ʳˡˣ("l" +ₗ #1) in
    (* release CAS, i.e. relaxed fail read, relaxed success read, release write *)
    if: casʳᵉˡ(("l" +ₗ #1), "weak", ("weak" - #1))
    then if: "weak" = #1 then FenceAcq ;; #true else #false
    else "drop" ["l"].

Definition drop_arc : val :=
  rec: "drop" ["l"] :=
    let: "strong" := !ʳˡˣ"l" in
    if: casʳᵉˡ("l", "strong", ("strong" - #1))
    then if: "strong" = #1 then FenceAcq ;; #true else #false
    else "drop" ["l"].

Definition try_unwrap : val :=
  λ: ["l"],
    (* release CAS *)
    if: casʳᵉˡ("l", #1, #0)
    then FenceAcq ;; #true
    else #false.

(* A bug was discovered where the read of strong was relaxed.
  It can be fixed by using an acquire read.
  See https://github.com/rust-lang/rust/issues/51780 *)
Definition is_unique : val :=
  λ: ["l"],
    (* Try to acquire the lock for the last ref by CASing weak count from 1 to -1. *)
    (* acquire CAS *)
    if: casᵃᶜ(("l" +ₗ #1), #1, #(-1)) then
      let: "strong" := !ᵃᶜ"l" in
      let: "unique" := "strong" = #1 in
      "l" +ₗ #1 <-ʳᵉˡ #1;;
      "unique"
    else
      #false.

(* to be used in make_mut *)
(*// Note that we hold both a strong reference and a weak reference.
  // Thus, releasing our strong reference only will not, by itself, cause
  // the memory to be deallocated.
  //
  // Use Acquire to ensure that we see any writes to `weak` that happen
  // before release writes (i.e., decrements) to `strong`. Since we hold a
  // weak count, there's no chance the ArcInner itself could be
  // deallocated. *)
(* - Returns #2 to signal that there is another strong pointer,
    and trigger a deep copy and make a new Arc pointing to the new copy.
   - Returns #1 to signal that we have the last strong pointer and
   the main content, but there are more than 1 weak pointers left.
   So we will move the main content to a new Arc, and leave the job
   of dropping to old Arc to its remaining weak pointers.
   - Returns #0 to signal that we have collected both the last strong and weak pointer,
   so it's time to clean up everything. We reset "strong" back to 1 to unlock.
   The write "l" <- #1 seems to be good enough, but C/Rust
   uses a release write, may be because the strict distinction between atomics
   and non-atomics. (TODO: is a relaxed write enough?) *)

(* we use acquire read instead of relaxed read on weak: we do not know how to
  prove or disprove the relaxed read yet *)
Definition try_unwrap_full : val :=
  λ: ["l"; "ret"],
    (* acquire CAS *)
    if: casᵃᶜ("l", #1, #0) then
      if: !ᵃᶜ("l" +ₗ #1) = #1 then "l" <- #1;; "ret" <- #0;; #☠
      else "ret" <- #1;; #☠
    else "ret" <- #2;; #☠.
