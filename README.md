# A Proof Recipe for Linearizability in Relaxed Memory Separation Logic (COQ DEVELOPMENT)

This is the formalization for the paper "A Proof Recipe for Linearizability in Relaxed Memory Separation Logic," done on top of [iRC11] relaxed memory separation logic.

> Sunho Park, Jaewoo Kim, Ike Mulder, Jaehwang Jung, Janggun Lee, Robbert Krebbers, and Jeehoon Kang. 2024. A Proof Recipe for Linearizability in Relaxed Memory Separation Logic. Proc. ACM Program. Lang. 8, PLDI, Article 154 (June 2024), 24 pages. https://doi.org/10.1145/3656384

- Full paper: <https://drive.google.com/file/d/1XhEQz5khMmTsMEyu2xn_BNgaPBAQdZga/view?usp=sharing>
- Artifact (zenodo): <https://doi.org/10.5281/zenodo.10933398>

## Building on a local machine

This version is known to compile with Coq 8.16.1 and a development version of [Iris].

To build it with opam, first install [opam](https://opam.ocaml.org/doc/Install.html) with version ≥ 2.1.2, and then run:
```sh
opam switch create . ocaml-system --no-install
opam repo add coq-released https://coq.inria.fr/opam/released
opam repo add iris-dev https://gitlab.mpi-sws.org/iris/opam.git
opam pin add -n -y coq 8.16.1

make build-dep
```

After installing dependencies, run the following to build the entire project.
```sh
eval $(opam env)
make -jN # N: number of CPU cores of your machine
```
It will take some time to compile the entire project.
In particular, the compilation of [proof_ms_history_diaframe.v](gpfsl-examples/queue/proof_ms_history_diaframe.v) may take about one and a half hour, and use about 25GB of memory.
You may safely exclude the file from the build by commenting out the line for the file (by inserting `#` in front) in [_CoqProject](_CoqProject).
In general, every proof file listed in columns `OMO` and `OMO+Diaframe` of the table in `Case Studies (§6, Table 1)` can be excluded from the compilation without causing any dependency problems in compilation.

During the compilation, you might encounter some warning messages like below:
```
Too little intro patterns were supplied! Please supply a name for:
  x1 : (history tseq_event)
  x2 : omoT
  x3 : (list tseq_state)
```
Note that these are not compilation errors. Such errors will be notified with explicit error message starting with `Error:`.

## Updating dependencies

Run:
```sh
opam update
make build-dep
make clean
```

## Using a provided Docker image

We provide a Docker image, uploaded to zenodo (<https://doi.org/10.5281/zenodo.10933398>), where the entire project has been already compiled with all dependencies installed.
To load the image, first install the [Docker engine](https://docs.docker.com/engine/install/), and then run:
```sh
sudo docker load -i artifact.tar.gz
sudo docker run -it --name artifact artifact:latest
```

After exiting the container, you can restart it from the loaded image with the following command:
```sh
sudo docker run -it --entrypoint=/bin/bash artifact:latest
```

To rebuild the project, you can clean the project first and then compile it by the following command:
```sh
eval $(opam env)
make clean
make -jN # N: number of CPU cores
```
As mentioned in the section `Building on a local machine`, compiling the entire project may take some time,
and you can safely ignore some proof files without causing any problems.

## Case Studies (§6, Table 1)

| Object                          | OMO                                       | OMO+Diaframe                                      | Comparison                                                                                                            |
| ------------------------------- | ----------------------------------------- | ------------------------------------------------- | --------------------------------------------------------------------------------------------------------------------- |
| Treiber's stack                 | [proof_treiber_history.v]                 | [proof_treiber_history_diaframe.v]                | [proof_treiber_history_old.v] + [spec_history_old.v] + [event.v]<sup>1)</sup>                                         |
| Spinlock                        | [proof_spin_lock_trylock_history.v]       | [proof_spin_lock_trylock_history_diaframe.v]      | [lock.v]<sup>2)</sup> (copied version for reproducibility: [comparison/lock.v])                                       |
| Michael-Scott queue             | [proof_ms_history.v]                      | [proof_ms_history_diaframe.v]                     | [proof_ms_abs_graph.v] + [spec_abs_graph.v] + [queue/spec_graph.v]<sup>1)</sup>                                       |
| Folly's turn sequencer          | [proof_turnSequencer_composition.v]       | [proof_turnSequencer_composition_diaframe.v]      | None                                                                                                                  |
| Folly's SPSC queue              | [proof_singleElementQueue_composition.v]  | [proof_singleElementQueue_composition_diaframe.v] | None                                                                                                                  |
| Folly's MPMC queue              | [proof_mpmcqueue_composition.v]           | [proof_mpmcqueue_composition_diaframe.v]          | None                                                                                                                  |
| Exchanger                       | [exchanger/proof_composition.v]           | [exchanger/proof_composition_diaframe.v]          | [proof_graph_piggyback.v] + [proof_graph_resource.v]<sup>1)</sup>                                                     |
| Elimination stack               | [proof_elim_composition.v]                | [proof_elim_composition_diaframe.v]               | [proof_elim_graph.v] + [stack/spec_graph.v] + [event.v]<sup>1)</sup>                                                  |
| Atomic reference counting (Arc) | [arc/proof_composition.v]                 | None                                              | [arc_cmra.v] + [arc.v]<sup>2)</sup> (copied version for reproducibility: [comparison/arc_cmra.v], [comparison/arc.v]) |

The line counts in the paper are obtained by counting proof lines of the files specified in the table from `Proof.` (or `Next Obligation.`) to `Qed.` (exclusive), excluding empty lines or comments.
These can be counted automatically by using a python script [statistics.py](statistics.py).

Note that several case studies (exchanger, elimination stack, Arc) that do not appear on submitted paper will be included in the revised version after finalizing the work (especially applying Diaframe).

1. These proofs are forked from the work by Dang et al.<sup>3)</sup> but we made some modifications on them. In particular, as we simplified the ORC11 semantics a little (see below for more detail), these proofs became shorter than the original.
2. Hoang-Hai Dang, Jacques-Henri Jourdan, Jan-Oliver Kaiser, and Derek Dreyer. 2019. RustBelt Meets Relaxed Memory. Proc. ACM Program. Lang. 4, POPL, Article 34 (dec 2019), 29 pages. https://doi.org/10.1145/3371102
3. Hoang-Hai Dang, Jaehwang Jung, Jaemin Choi, Duc-Than Nguyen, William Mansky, Jeehoon Kang, and Derek Dreyer. 2022. Compass: Strong and Compositional Library Specifications in Relaxed Memory Separation Logic. In Proceedings of the 43rd ACM SIGPLAN International Conference on Programming Language Design and Implementation (San Diego, CA, USA) (PLDI 2022). Association for Computing Machinery, New York, NY, USA, 792–808. https://doi.org/10.1145/3519939.3523451

## Client proofs (§6.6)

- Treiber's stack client (Fig. 1): [stack/proof_omo_client.v](gpfsl-examples/stack/proof_omo_client.v)
- Spinlock client (§6.1): [lock/proof_omo_client.v](gpfsl-examples/lock/proof_omo_client.v)
- Arc client (§6.5): [arc/proof_omo_client.v](gpfsl-examples/arc/proof_omo_client.v)

## Project structure

- [OMO predicates and rules](gpfsl-examples/omo)
  + [omo_preds.v]: main rules for working with omo structures. (Fig. 7)
  + [omo.v]: definitions of omo structures and low-level lemmas to work around them.
  + [omo_event.v]: definition of the event type used in the omo structure.
  + [omo_history.v]: definition of the history type.
  + [append_only_loc.v]: definitions and rules of OMO points-to. (Fig. 9)
- [Diaframe hints](gpfsl/diaframe)
  + [view_hints.v]: hints for handling view-at modality.
  + [omo_hints.v]: hints for automating proofs using OMO library.
  + [omo_specs.v](gpfsl/diaframe/omo_specs.v): hints for automatic symbolic execution using OMO points-to predicates.
  + [base_hints.v](gpfsl/diaframe/base_hints.v): general hints for automating common patterns.
  + [base_specs.v](gpfsl/diaframe/base_specs.v): hints for basic specifications in iRC11
  + [proof_automation.v](gpfsl/diaframe/proof_automation.v): single file that contains necessary imports for Diaframe in iRC11
  + [atom_spec_notation.v](gpfsl/diaframe/atom_spec_notation.v): notation definitions
  + [spec_notation.v](gpfsl/diaframe/spec_notation.v): notation definitions
  + [vprop_weakestpre.v](gpfsl/diaframe/vprop_weakestpre.v): hints for automating proof of weakest precondition in iRC11
  + [vprop_weakestpre_logatom.v](gpfsl/diaframe/vprop_weakestpre_logatom.v): hints for automating proof of weakest precondition (LAT version) in iRC11
  + [inv_hints.v](gpfsl/diaframe/inv_hints.v): iRC11 version of original `iris_hints.v` of Diaframe
  + [lattice_hints.v](gpfsl/diaframe/lattice_hints.v): setting Diaframe for solving lattices
  + [mono_list_hints.v](gpfsl/diaframe/mono_list_hints.v): hints for `mono_list`
  + [ghost_map_hints.v](gpfsl/diaframe/ghost_map_hints.v): hints for `ghost_map`
- Case studies
  + [Treiber's stack](gpfsl-examples/stack)
    * [code_treiber.v](gpfsl-examples/stack/code_treiber.v): program code of Treiber's stack
    * [stack_event_omo.v](gpfsl-examples/stack/stack_event_omo.v): definition of stack events and state transition system
    * [spec_history.v](gpfsl-examples/stack/spec_history.v): linearizability specification of Treiber's stack/elimination stack
    * [spec_treiber_composition.v](gpfsl-examples/stack/spec_treiber_composition.v): composable linearizability specification of Treiber's stack
    * [spec_treiber_composition_diaframe.v](gpfsl-examples/stack/spec_treiber_composition_diaframe.v): composable linearizability specification of Treiber's stack (better compatibiltiy with Diaframe)
    * [proof_treiber_history.v](gpfsl-examples/stack/proof_treiber_history.v): manual proof of linearizability specification of Treiber's stack
    * [proof_treiber_history_diaframe.v](gpfsl-examples/stack/proof_treiber_history_diaframe.v): automated proof (with Diaframe) of linearizability specification of Treiber's stack
    * [proof_treiber_composition.v](gpfsl-examples/stack/proof_treiber_composition.v): manual proof of composable linearizability specification of Treiber's stack
    * [proof_treiber_composition_diaframe.v](gpfsl-examples/stack/proof_treiber_composition_diaframe.v): automated proof (with Diaframe) of composable linearizability specification of Treiber's stack
    * [proof_omo_client.v](gpfsl-examples/stack/proof_omo_client.v): proof of Treiber's stack client (Fig. 1)
  + [Spinlock](gpfsl-examples/lock)
    * [code_spin_lock.v](gpfsl-examples/lock/code_spin_lock.v): program code of spinlock
    * [spec_trylock_history.v](gpfsl-examples/lock/spec_trylock_history.v): linearizability specification of spinlock
    * [spec_trylock_composition.v](gpfsl-examples/lock/spec_trylock_composition.v): composable linearizability specification of spinlock
    * [proof_spin_lock_trylock_history.v](gpfsl-examples/lock/proof_spin_lock_trylock_history.v): manual proof of linearizability specification of spinlock
    * [proof_spin_lock_trylock_history_diaframe.v](gpfsl-examples/lock/proof_spin_lock_trylock_history_diaframe.v): automated proof (with Diaframe) of linearizability specification of spinlock
    * [proof_spin_lock_trylock_composition.v](gpfsl-examples/lock/proof_spin_lock_trylock_composition.v): manual proof of composable linearizability specification of spinlock
    * [proof_omo_client.v](gpfsl-examples/lock/proof_omo_client.v): proof of spinlock client (§6.1)
    * [comparison](gpfsl-examples/lock/comparison/): a folder containing a proof for comparison (used for counting proof lines, not compiled)
  + [Michael-Scott queue](gpfsl-examples/queue)
    * [code_ms_tailcas.v](gpfsl-examples/queue/code_ms_tailcas.v): program code of Michael-Scott queue
    * [spec_history.v](gpfsl-examples/queue/spec_history.v): linearizability specification of Michael-Scott queue
    * [spec_composition.v](gpfsl-examples/queue/spec_composition.v): composable linearizability specification of Michael-Scott queue
    * [proof_ms_history.v](gpfsl-examples/queue/proof_ms_history.v): manual proof of linearizability specification of Michael-Scott queue
    * [proof_ms_history_diaframe.v](gpfsl-examples/queue/proof_ms_history_diaframe.v): automated proof (with Diaframe) of linearizability specification of Michael-Scott queue
    * [proof_ms_composition.v](gpfsl-examples/queue/proof_ms_composition.v): manual proof of composable linearizability specification of Michael-Scott queue
  + [Folly](gpfsl-examples/folly)
    * [code_turnSequencer.v](gpfsl-examples/folly/code_turnSequencer.v): program code of turn sequencer
    * [code_singleElementQueue.v](gpfsl-examples/folly/code_singleElementQueue.v): program code of SPSC queue
    * [code_mpmcqueue.v](gpfsl-examples/folly/code_mpmcqueue.v): program code of MPMC queue
    * [spec_turnSequencer_history.v](gpfsl-examples/folly/spec_turnSequencer_history.v): linearizability specification of turn sequencer
    * [spec_turnSequencer_composition.v](gpfsl-examples/folly/spec_turnSequencer_composition.v): composable linearizability specification of turn sequencer
    * [spec_singleElementQueue_history.v](gpfsl-examples/folly/spec_singleElementQueue_history.v): linearizability specification of SPSC queue
    * [spec_singleElementQueue_composition.v](gpfsl-examples/folly/spec_singleElementQueue_composition.v): composable linearizability specification of SPSC queue
    * [spec_mpmcqueue_history.v](gpfsl-examples/folly/spec_mpmcqueue_history.v): linearizability specification of MPMC queue
    * [spec_mpmcqueue_composition.v](gpfsl-examples/folly/spec_mpmcqueue_compostion.v): composable linearizability specification of MPMC queue
    * [proof_turnSequencer_history.v](gpfsl-examples/folly/proof_turnSequencer_history.v): manual proof of linearizability specification of turn sequencer
    * [proof_turnSequencer_composition.v](gpfsl-examples/folly/proof_turnSequencer_composition.v): manual proof of composable linearizability specification of turn sequencer
    * [proof_turnSequencer_composition_diaframe.v](gpfsl-examples/folly/proof_turnSequencer_composition_diaframe.v): automated proof (with Diaframe) of composable linearizability specification of turn sequencer
    * [proof_singleElementQueue_history.v](gpfsl-examples/folly/proof_singleElementQueue_history.v): manual proof of linearizability specification of SPSC queue
    * [proof_singleElementQueue_composition.v](gpfsl-examples/folly/proof_singleElementQueue_composition.v): manual proof of composable linearizability specification of SPSC queue
    * [proof_singleElementQueue_composition_diaframe.v](gpfsl-examples/folly/proof_singleElementQueue_composition_diaframe.v): automated proof (with Diaframe) of composable linearizability specification of SPSC queue
    * [proof_mpmcqueue_history.v](gpfsl-examples/folly/proof_mpmcqueue_history.v): manual proof of linearizability specification of MPMC queue
    * [proof_mpmcqueue_composition.v](gpfsl-examples/folly/proof_mpmcqueue_composition.v): manual proof of composable linearizability specification of MPMC queue
    * [proof_mpmcqueue_composition_diaframe.v](gpfsl-examples/folly/proof_mpmcqueue_composition_diaframe.v): automated proof (with Diaframe) of composable linearizability specification of MPMC queue
  + [Exchanger](gpfsl-examples/exchanger)
    * [code.v](gpfsl-examples/exchanger/code.v): program code of exchanger used by Dang et al.<sup>1)</sup>
    * [code_split.v](gpfsl-examples/exchanger/code_split.v): program code of exchanger used by our work (it splits `exchange` function into three small parts so that user can freely set waiting time after registering an offer)
    * [spec_composition.v](gpfsl-examples/exchanger/spec_composition.v): composable linearizability specification of exchanger
    * [spec_composition_diaframe.v](gpfsl-examples/exchanger/spec_composition_diaframe.v): composable linearizability specification of exchanger (better compatibility with Diaframe)
    * [proof_composition.v](gpfsl-examples/exchanger/proof_composition.v): manual proof of composable linearizability specification of exchanger
    * [proof_composition_diaframe.v](gpfsl-examples/exchanger/proof_composition_diaframe.v): automated proof (with Diaframe) of composable linearizability specification of exchanger
  + [Elimination stack](gpfsl-examples/stack)
    * [code_elimination.v](gpfsl-examples/stack/code_elimination.v): program code of elimination stack used by Dang et al.<sup>1)</sup>
    * [code_elim.v](gpfsl-examples/stack/code_elim.v): program code of elimination stack used by our work (which uses [code_split.v](gpfsl-examples/exchanger/code_split.v))
    * [spec_elim_composition.v](gpfsl-examples/stack/spec_elim_composition.v): composable linearizability specification of elimination stack
      (Note: This is almost the same as specification of Treiber's stack ([spec_treiber_composition.v](gpfsl-examples/stack/spec_treiber_composition.v)). The only difference is that specification of Treiber's stack exposes the fact that all write events are totally ordered to reduce proof burden.)
    * [spec_elim_composition_diaframe.v](gpfsl-examples/stack/spec_elim_composition_diaframe.v): composable linearizability specification of elimination stack (better compatibility with Diaframe)
    * [proof_elim_history.v](gpfsl-examples/stack/proof_elim_history.v): manual proof of linearizability specification of elimination stack
    * [proof_elim_composition.v](gpfsl-examples/stack/proof_elim_composition.v): manual proof of composable linearizability specification of elimination stack
    * [proof_elim_composition_diaframe.v](gpfsl-examples/stack/proof_elim_composition_diaframe.v): automated proof (with Diaframe) of composable linearizability specification of elimination stack
  + [Arc](gpfsl-examples/arc)
    * [code.v](gpfsl-examples/arc/code.v): program code of Arc
    * [spec_composition.v](gpfsl-examples/arc/spec_composition.v): composable linearizability specification of Arc
    * [proof_composition.v](gpfsl-examples/arc/proof_composition.v): manual proof of composable linearizability specification of Arc
    * [proof_omo_client.v](gpfsl-examples/arc/proof_omo_client.v): proof of Arc client (§6.5)
    * [comparison](gpfsl-examples/arc/comparison/): a folder containing a proof for comparison (used for counting proof lines, not compiled)

1. Hoang-Hai Dang, Jaehwang Jung, Jaemin Choi, Duc-Than Nguyen, William Mansky, Jeehoon Kang, and Derek Dreyer. 2022. Compass: Strong and Compositional Library Specifications in Relaxed Memory Separation Logic. In Proceedings of the 43rd ACM SIGPLAN International Conference on Programming Language Design and Implementation (San Diego, CA, USA) (PLDI 2022). Association for Computing Machinery, New York, NY, USA, 792–808. https://doi.org/10.1145/3519939.3523451

## [Object Modification Order (OMO) Library](gpfsl-examples/omo) (§3, §4)

The table below describes how the important concepts in our paper are modeled in this repository.
| Paper                                                                                   | Coq                                                                                                                                                                                                 |
| --------------------------------------------------------------------------------------- | ----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------|
| OMO has a type of `list (list EventId)`.                                                | OMO is a list of a pair of a write event and a list of read-only events, denoted by `list (event_id * list event_id)`. This enforces each generation has at least one write event.                  |
| Event history `H is a mapping from EventId to Event(T)` where T is a type of event.     | Event history `E is a list of events which has type omo_event T` where each event is ordered in execution order.                                                                                    |
| Event(T) is a record of `type, sync-view, eview.`                                       | omo_event T is a record of `type, sync-view, eview`, which directly matches with the Event(T).                                                                                                      |
| `EventId is an abstract type.`                                                          | `EventId is a natural number` denoting an index of each event in the event history E.                                                                                                               |
| Object's sequential specification is given as a tuple `(T, S, σ₀, →).`                  | Object's sequential specification is given as the `Interpretable T S` typeclass which contains `init` (initial state, σ₀) and `step` (state transition, →).                                         |


The table below compares the definitions and predicates used in the paper with those in the Coq mechanization.
| Paper                                        | Coq                                            | Note                                                                                                                                                                                          |
| -------------------------------------------- | ---------------------------------------------- | --------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- |
| OmoAuth(γₒ,γₛ,H,omo,Σ)                       | OmoAuth γₒ γₛ q E omo Σ                         | `q` denotes fractional ownership which allows splitting ownership of OmoAuth.                                                                                                                |
| ⊒<sub>γo</sub>M                              | OmoEview γₒ M                                 |                                                                                                                                                                                               |
| OmoSnap(γₒ,γₛ,e,σ)                           | OmoSnap γₒ γₛ e σ                              |                                                                                                                                                                                                 |
| interp<sub>omo</sub>(H,omo,σ₀,Σ)             | interp_omo E omo σ₀ Σ                          | Encoded in `Linearizability_omo`, a predicate for well-formedness of OMO structure guaranteed by OmoAuth.                                                                                    |
| lhb(H,π)                                     | lhb E lin                                      | `lin` is a list of event id, in contrast to π being a permutation.                                                                                                                            |
| lhb<sub>omo</sub>(H,omo)                     | lhb_omo E omo                                  | Encoded in `Linearizability_omo`, a predicate for well-formedness of OMO structure guaranteed by OmoAuth.                                                                                     |
| Token(γₒ,e)                                  | OmoToken(R\|W) γₒ e                            | `OmoTokenR` corresponds to Token<sup>r</sup> and `OmoTokenW` corresponds to Token<sup>w</sup> (§5).                                                                                           |
| maxGen(omo,M) ≤ n                            | OmoUBgen omo M n                               | `OmoUB` is vProp version of `OmoUBgen` where comparison of generations is asserted by `OmoLe` predicates.                                                                                     |
| commit-with relation from e (γₒ) to e' (γₒ') | OmoCW γₒ γₒ' e e'                              |                                                                                                                                                                                               |
| OMO points-to predicate                      | append_only_loc + OmoAuth + (swriter_token)    | Supports two protocols that ensure `append-only` properties (no insertion of write event in the middle): single writer, cas-only.                                                             |
| LocSeen ℓ γₒ M                               | OmoEview γₒ M                                  |                                                                                                                                                                                               |
| Omo<sub>≤</sub>(γₒ,e,e')                     | OmoLe γₒ e e'                                  | Similar predicates `OmoEq`, `OmoLt` are also provided.                                                                                                                              |
| CWMono(γₒ,H)                                 | CWMono γₒ γₒ' γₘ M                             | Coq version asserts monotonicity for all commit-with relations with upper-level events in M between upper-level (γₒ) and lower-level (γₒ') objects. γₘ is a ghost name for the ghost set on M. |

The table below highlights the locations of important lemmas.
| Rule                 | File                | Lemma                                                                  |
| -------------------- | ------------------- | ---------------------------------------------------------------------- |
| OmoAuth-Linearizable | [omo_preds.v]       | `OmoAuth_Linearizable`<sup>1)</sup>                                    |
| Omo-Compatible       | [omo.v]             | `omo_compatible`                                                       |
| OmoSnap-Get          | [omo_preds.v]       | `OmoSnap_get`                                                          |
| OmoAuth-OmoSnap      | [omo_preds.v]       | `OmoAuth_OmoSnap`                                                      |
| OmoAuth-Alloc        | [omo_preds.v]       | `OmoAuth_alloc`                                                        |
| OmoAuth-Insert-Ro    | [omo_preds.v]       | `OmoAuth_insert_ro_gen` (`OmoAuth_insert_ro` is also used often)       |
| OmoAuth-Insert-Last  | [omo_preds.v]       | `OmoAuth_insert_last`                                                  |
| OmoAuth-Insert       | [omo_preds.v]       | `OmoAuth_insert`                                                       |
| Omo-Points-To-Alloc  | [append_only_loc.v] | `append_only_loc_(cas_only\|swriter)_from_na`<sup>2)</sup>             |
| Omo-Points-To-Load   | [append_only_loc.v] | `append_only_loc_read`<sup>2)</sup>                                    |
| Omo-Points-To-Store  | [append_only_loc.v] | `append_only_loc_write`<sup>2)</sup>                                   |
| Omo-Points-To-CAS    | [append_only_loc.v] | `append_only_loc_cas_general`<sup>2)</sup>                             |
| OmoLe-Get            | [omo_preds.v]       | `OmoLe_get`                                                            |
| OmoLe-Le             | [omo_preds.v]       | `OmoLe_Le`                                                             |


1. Definition of `Linearizability_omo` used in the lemma `OmoAuth_Linearizable` can be found in [omo.v]. Note that the definition of `Linearizability_omo` directly matches with conclusion of the rule in the paper.
2. In the paper, composable linearizability specification for shared location strictly follows the style of the specification by encoding semantics of memory accesses with abstract state transitions. The rules in Coq, instead expose the semantics explicitly in the specification. This helps simplify the proof process. Note that, both encodings are equivalent.

Stack predicates in paper and in [Coq](gpfsl-examples/stack/proof_treiber_history.v) have some differences. Notable ones are:
- Coq version starts with the `meta` predicate, which persistently associates a location to a list of values, while the paper version simply omitted such detail.
- `PhysList` in the paper corresponds to `StackNodes` in Coq. While PhysList is asserted for every location event, StackNodes is asserted only for the latest write event, which is sufficient and more convenient to establish the invariant.
  Note that although paper version uses persistent points-to assertion (↦□), Coq version does not use it. Instead, we *mimic* the characteristic of persistency by taking out fractional ownership of points-to assertion from `PhysList` and keeping it in the proof context for later use of read operations.
- The ∀-quantified part in the paper corresponds to `AllLinks` in Coq. While the paper version maintains it for *all* location events, the Coq version maintains it only for all *write events* of a location, which also simplifies the proof.
- **Stk3** asserted in `SeenStack` in the paper corresponds to `seen_event_info` in Coq. It uses the `OmoHb` predicate, which is a generalization of **Stk3** but only in one-direction: observation of a upper-level object event implies observation of lower-level object event.
- `CWMono` in the paper corresponds to `CWMono` in Coq.

## [Diaframe Automation](gpfsl/diaframe) (§5)

We construted a hint database for Diaframe to extend it into RMC separation logic and to make it usable with OMO predicates and rules.
The interesting files are as follows:
- [view_hints.v]: hints for handling view-at modality (§5.2, in particular the idea of 'applying VA-Intro rule whenever possible' is represented by the hints `mergable_consume_always_intro_view_at_first` and `mergable_consume_always_intro_view_at_step`).
- [omo_hints.v]: hints for automating proofs using the OMO library (§5.3).
- [omo_specs.v](gpfsl/diaframe/omo_specs.v): special hints for automatic symbolic execution for proofs using the using OMO points-to predicates (§5.3).
- [base_hints.v](gpfsl/diaframe/base_hints.v): general hints for Diaframe (related to §5.3, in particular hints for *ask_for* mechanism are written in this file).

Below, we briefly explain several useful tactics.
For more information, please refer to the [repository of Diaframe](https://gitlab.mpi-sws.org/iris/diaframe/-/tree/3fb3d7ca0de57118c9c0a3d5f841820da13ba093).
- `iStep`, `iSteps`:
  These are main tactics provided by Diaframe.
  It takes multiple automatic steps based on primitive rules of Diaframe and Diaframe hints.
  `iStep` performs a single chunk of automation step, while `iSteps` repeats `iStep` whenever possible.
- `iStepSafest`, `iStepsSafest`:
  These tactics are more conservative then `iStep` and `iSteps` in the sense that former ones stop when a goal is a disjunction.
  As previous, `iStepsSafest` repeats `iStepSafest` whenever possible.
- `iStepDebug`, `solveStep`:
  These are for debugging steps.
  `iStepDebug` turns current goal into the form that Diaframe can understand,
  and `solveStep` takes a single basic step, which is much smaller than the step that `iStep` takes.
- `oSteps`:
  This is a tactic defined by our work (see its definition in [omo_hints.v]).
  It automatically applies a collection of rewrite rules that are widely used in our recipe while repeatedly performing `iStepsSafest`.

## Change in Semantics

This project is built upon [iRC11], a separation logic for the ORC11 memory model.
For better support for automation, we simplified the semantics of ORC11 that does not change the core part of the memory model, which are explained below. Note that we did not touch the race detector of ORC11.
- The comparison of two locations with different addresses [can be true if either one of them is deallocated](https://gitlab.mpi-sws.org/iris/gpfsl/-/blob/fdf1fcba85da1df81b3e1b632763b87c95336ec0/gpfsl/lang/lang.v#L223-228).
  This leads to complexity in the CAS rule where we need to check the liveness of each location stored in location history before performing the CAS.
  We believe this semantics creates complexities orthogonal to our work, hence have removed it.
- [Arbitrary comparison between non-zero integers and locations is not allowed](https://gitlab.mpi-sws.org/iris/gpfsl/-/blob/fdf1fcba85da1df81b3e1b632763b87c95336ec0/gpfsl/lang/lang.v#L247-251).
  Since we did not have any case study where we performed a comparison between arbitrary locations and integers, we made arbitrary comparison of locations with integers to simply be false.

[iRC11]: https://gitlab.mpi-sws.org/iris/gpfsl
[Iris]: https://gitlab.mpi-sws.org/iris/iris
[view_hints.v]: gpfsl/diaframe/view_hints.v
[omo_preds.v]: gpfsl-examples/omo/omo_preds.v
[omo.v]: gpfsl-examples/omo/omo.v
[omo_event.v]: gpfsl-examples/omo/omo_event.v
[omo_hints.v]: gpfsl/diaframe/omo_hints.v
[omo_history.v]: gpfsl-examples/omo/omo_history.v
[append_only_loc.v]: gpfsl-examples/omo/append_only_loc.v
[proof_treiber_history_old.v]: gpfsl-examples/stack/proof_treiber_history_old.v
[proof_treiber_history.v]: gpfsl-examples/stack/proof_treiber_history.v
[proof_treiber_history_diaframe.v]: gpfsl-examples/stack/proof_treiber_history_diaframe.v
[lock.v]: https://gitlab.mpi-sws.org/iris/lambda-rust/-/blob/masters/weak_mem/theories/lang/lock.v
[comparison/lock.v]: gpfsl-examples/lock/comparison/lock.v
[proof_spin_lock_trylock_history.v]: gpfsl-examples/lock/proof_spin_lock_trylock_history.v
[proof_spin_lock_trylock_history_diaframe.v]: gpfsl-examples/lock/proof_spin_lock_trylock_history_diaframe.v
[proof_ms_history.v]: gpfsl-examples/queue/proof_ms_history.v
[proof_ms_history_diaframe.v]: gpfsl-examples/queue/proof_ms_history_diaframe.v
[proof_turnSequencer_composition.v]: gpfsl-examples/folly/proof_turnSequencer_composition.v
[proof_singleElementQueue_composition.v]:  gpfsl-examples/folly/proof_singleElementQueue_composition.v
[proof_mpmcqueue_composition.v]:  gpfsl-examples/folly/proof_mpmcqueue_composition.v
[spec_history_old.v]: gpfsl-examples/stack/spec_history_old.v
[proof_ms_abs_graph.v]: gpfsl-examples/queue/proof_ms_abs_graph.v
[spec_abs_graph.v]: gpfsl-examples/queue/spec_abs_graph.v
[queue/spec_graph.v]: gpfsl-examples/queue/spec_graph.v
[stack/spec_graph.v]: gpfsl-examples/stack/spec_graph.v
[event.v]: gpfsl-examples/stack/event.v
[exchanger/proof_composition.v]: gpfsl-examples/exchanger/proof_composition.v
[exchanger/proof_composition_diaframe.v]: gpfsl-examples/exchanger/proof_composition_diaframe.v
[proof_graph_piggyback.v]: gpfsl-examples/exchanger/proof_graph_piggyback.v
[proof_graph_resource.v]: gpfsl-examples/exchanger/proof_graph_resource.v
[proof_elim_graph.v]: gpfsl-examples/stack/proof_elim_graph.v
[arc_cmra.v]: https://gitlab.mpi-sws.org/iris/lambda-rust/-/blob/masters/weak_mem/theories/lang/arc_cmra.v
[arc.v]: https://gitlab.mpi-sws.org/iris/lambda-rust/-/blob/masters/weak_mem/theories/lang/arc.v
[comparison/arc_cmra.v]: gpfsl-examples/arc/comparison/arc_cmra.v
[comparison/arc.v]: gpfsl-examples/arc/comparison/arc.v
[proof_elim_composition.v]: gpfsl-examples/stack/proof_elim_composition.v
[proof_elim_composition_diaframe.v]: gpfsl-examples/stack/proof_elim_composition_diaframe.v
[arc/proof_composition.v]: gpfsl-examples/arc/proof_composition.v
[proof_turnSequencer_composition_diaframe.v]: gpfsl-examples/folly/proof_turnSequencer_composition_diaframe.v
[proof_singleElementQueue_composition_diaframe.v]: gpfsl-examples/folly/proof_singleElementQueue_composition_diaframe.v
[proof_mpmcqueue_composition_diaframe.v]: gpfsl-examples/folly/proof_mpmcqueue_composition_diaframe.v
