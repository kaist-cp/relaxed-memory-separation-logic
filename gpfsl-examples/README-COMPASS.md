# Compass Coq Development

## Extensions to iRC11

The Compass framework is built on top of the [iRC11] separation logic, which is
sound for the [ORC11] memory model, an operational variant of [RC11] that has
non-atomic, release-acquire, and relaxed accesses, and fences, and forbids
*load buffering* behaviors, i.e. po ∪ rf is acyclic.

Our verifications depend on the following new additions to [iRC11].
These were not discussed at all in the submitted draft, due to space restriction.
We will extend the paper in the camera-ready version to include more explanation
about them.

* The *view at* modality `@{V} P` ([`base_logic/vprop.v`](../gpfsl/base_logic/vprop.v))
  makes explicit the view of an assertion `P` in the logic.
  This logical construct was already developed in [iRC11] and is similar to
  Cosmo's `P@V` assertion, but is now given a more thorough theory.
* General *objective invariants* ([`logic/invariants.v`](../gpfsl/logic/invariants.v))
  allow arbitrary objective resources to be shared.
  Objective resources include unsynchronized ghost state and view-at assertions
  `@{V} P`. General invariants lift the *single-location* restriction of
  [iRC11]'s GPS protocols, and thus can be used to compose ownership of multiple
  locations and multiple data structures. This allows combining general
  invariants with logical atomicity in almost the same way as in a SC logic.
  The only difference is the extra side condition of that only objective
  resources can be put inside general invariants.
* *Atomic points-to* ([`logic/atomic_ops.v`](../gpfsl/logic/atomic_ops.v))
  expose the middle-level rules, between the base logic's histories and
  the surface logic's [iRC11] protocols, for handling atomic locations directly
  with histories and views, but more abstractly than in the base logic.
  The rules for atomic operations (atomic reads, writes, or CASes) only the
  atomic points-to of the accessed location only under a view-at modality.
  Therefore, atomic points-to can be easily put inside general invariants.

  | Paper     | Coq definition                |
  |-----------|-------------------------------|
  | Rel-Write | `AtomicSWriter_release_write` |
  | Acq-Read  | `AtomicSeen_acquire_read`     |

* Logical atomic triples (LATs) [`logic/logatom.v`](../gpfsl/logic/logatom.v)
  are directly reused from Iris, without change, in the same way as Cosmo.
  This is because Iris support for LATs (through the concept *atomic updates*)
  is quite general, and the relaxed memory effects can be handled orthogonally
  through the use of the view-at modality and general invariants.
  The proofs in [`logic/logatom.v`](../gpfsl/logic/logatom.v) simply show that
  LATs imply iRC11 Hoare triples, as a sanity check.

## Compass Framework (§3)
* [`event/`](event)
  * [`event.v`](event/event.v): the event type, and
    the physical interpretation of logical view (`seen_logview`).

    | Paper                  | Coq           | notes                                                                    |
    |------------------------|---------------|--------------------------------------------------------------------------|
    | event tuple            | `graph_event` |                                                                          |
    | physical view of event | `dataView`    | Coq version consists of 3 views: input view, commit view, and write view |
    | logical view of event  | `logView`     |                                                                          |

  * [`ghost.v`](event/ghost.v): view-dependent assertions,
    built with Iris ghost state, and are needed to build "local" assertions like
    `SeenQueue` in the paper.
* [`graph/`](graph): the ingredients for
  LAT<sup>abs</sup><sub>hb</sub>- and LAT<sub>hb</sub>-style specification.
  * [`graph.v`](graph/graph.v): the definition of
    Yacovet-style event-graph.

    | Paper | Coq     | notes                                                                                                                    |
    |-------|---------|--------------------------------------------------------------------------------------------------------------------------|
    | graph | `graph` | Coq version has additional edge `com` to faithfully encode Yacovet, but it is identical to `so` in all the case studies. |

  * [`ghost.v`](graph/ghost.v): the master-snapshot
    ghost state for event-graph.
* [`history/`](history): similar to above, but for
  LAT<sup>hist</sup><sub>hb</sub>-style specification.

## Library Specifications and Proofs

### [Queue](queue) (§3.1-§3.2)
* implementations
  * [`code_ms.v`](queue/code_ms.v): Michael-Scott queue.
  * [`code_hw.v`](queue/code_hw.v): Herlihy-Wing queue.
* specs
  * [`spec_abs.v`](queue/spec_abs.v):
    LAT<sup>abs</sup><sub>so</sub> spec. (Figure 2)

    | Paper            | Coq                       |
    |------------------|---------------------------|
    | Abs-So-{Enq,Deq} | `{enqueue,dequeue}_spec'` |

  * [`spec_abs_graph.v`](queue/spec_abs_graph.v):
    LAT<sup>abs</sup><sub>hb</sub> spec. (Figure 2 and 7)

    | Paper                    | Coq                        | Related Coq definitions and notes                                                                                            |
    |--------------------------|----------------------------|------------------------------------------------------------------------------------------------------------------------------|
    | Abs-Hb-New-Stack         | `new_stack_spec`           | `new_stack_spec'`                                                                                                            |
    | Abs-Hb-Try-{Enq,Deq}     | `try_{enq,deq}_spec`       | `try_{enq,deq}_spec'`                                                                                                        |
    | Abs-Hb-{Enq,Deq}         | `{enqueue,dequeue}_spec`   | `{enqueue,dequeue}_spec'`                                                                                                    |
    | Abs-Hb-Queue-Consistency | `QueueInv_QueueConsistent` |                                                                                                                              |
    | QueueConsistent          |                            | See `spec_graph.v`                                                                                                           |
    | `SeenQueue(q, G, M)`     | `QueueLocal N γg q G M`    | `N`: namespace for queue invariant, `γg`: ghost variable for event-graph. This naming scheme applies to other libraries too. |
    | `Queue(q, vs, G)`        | `QueueInv γg q Q G`        | `Q` = `vs`                                                                                                                   |

  * [`spec_graph.v`](queue/spec_graph.v):
    LAT<sub>hb</sub> spec. (Figure 7)

    | Paper                  | Coq                                | Related Coq definitions                 |
    |------------------------|------------------------------------|-----------------------------------------|
    | QueueConsistent        | `BasicQueueConsistent`             | See also `{Weak,Strong}QueueConsistent` |
    | Queue-Matches          | `bsq_cons_matches`                 | `queue_matches_value`                   |
    | Queue-So-Functional    | `bsq_cons_com_functional`          | `functional_pair` in `graph/graph.v`    |
    | Queue-Unmatched-EmpDeq | `bsq_cons_unmatched_dequeue_empty` | `queue_unmatched_deq_empty`             |
    | Queue-FIFO             | `bsq_cons_FIFO_b`                  | `queue_FIFO{,_strong,_weak}`            |
    | Queue-EmqDeq           | `bsq_cons_non_empty`               | `queue_empty_unmatched_enq{,_strong}`   |

  * [`spec_spsc.v`](queue/spec_spsc.v):
    LAT<sub>hb</sub> spec for
    single-producer-single-consumer (SPSC) client. (Figure 8)
  * [`spec_per_elem.v`](queue/spec_per_elem.v): Simple "bag"
    specification with resource transfer, but without FIFO property and
    logical atomicity.
* library verifications
  * [`proof_ms_abs_graph.v`](queue/proof_ms_abs_graph.v):
    Michael-Scott queue satisfies LAT<sup>abs</sup><sub>hb</sub> spec.
  * [`proof_hw_graph.v`](queue/proof_hw_graph.v):
    Herlihy-Wing queue satisfies LAT<sub>hb</sub> spec.
* relations of specs
  * [`proof_abs_graph_abs.v`](queue/proof_abs_graph_abs.v):
    LAT<sup>abs</sup><sub>hb</sub> spec implies LAT<sup>abs</sup><sub>so</sub> spec.
  * [`proof_abs_graph_graph.v`](queue/proof_abs_graph_graph.v):
    LAT<sup>abs</sup><sub>hb</sub> spec implies LAT<sub>hb</sub> spec.
  * [`proof_per_elem_graph.v`](queue/proof_per_elem_graph.v):
    LAT<sub>hb</sub> spec implies bag spec.
  * [`proof_spsc_graph.v`](queue/proof_spsc_graph.v):
    LAT<sub>hb</sub> spec implies SPSC LAT<sub>hb</sub> spec.
  * [`proof_sequential_client.v`](queue/proof_sequential_client.v):
    LAT<sub>hb</sub> spec implies sequential spec.
* client verifications
  * [`proof_mp_graph.v`](queue/proof_mp_graph.v): Proof that
    a dequeue cannot return empty if the dequeue has seen an unmatched enqueue,
    proved with LAT<sub>hb</sub>.
  * [`proof_mp2_graph.v`](queue/proof_mp2_graph.v): Similar
    to the above, but with two concurrent dequeuers. (Figure 1 and 3)
  * [`proof_producer_consumer.v`](queue/proof_producer_consumer.v):
    Simple SPSC client verification using SPSC LAT<sub>hb</sub>
    spec. (§3.2)


### [Stack](stack) (§3.3-§4.1)
* implementations
  * [`code_treiber.v`](stack/code_treiber.v): Treiber stack
  * [`code_elim.v`](stack/code_elim.v): elimination stack that
    takes implementations of a stack and an exchanger as parameters.
* specs
  * [`spec_abs.v`](stack/spec_abs.v):
    LAT<sup>abs</sup><sub>so</sub> spec.
  * [`spec_graph.v`](stack/spec_graph.v):
    LAT<sub>hb</sub> spec. (Figure 5 and 10)

    | Paper                  | Coq                        | Related Coq definitions and notes    |
    |------------------------|----------------------------|--------------------------------------|
    | Hb-New-Stack           | `new_stack_spec`           | `new_stack_spec'`                    |
    | Hb-Try-{Push,Pop}      | `try_{push,pop}_spec`      | `try_{push,pop}_spec'`               |
    | Hb-{Push,Pop}          | `{push,pop}_spec`          | `{push,pop}_spec'`                   |
    | Hb-Stack-Consistency   | `StackInv_StackConsistent` |                                      |
    | StackConsistent        | `StackConsistent`          | See also `ExtendedStackConsistent`   |
    | Stack-Matches          | `stk_cons_matches`         | `stack_matches_value`                |
    | Stack-So-Functional    | `stk_cons_com_functional`  | `functional_pair` in `graph/graph.v` |
    | Stack-Unmatched-EmpPop | `stk_cons_empty_pop`       | `stack_unmatched_pop_empty`          |
    | Stack-LIFO             | `stk_cons_LIFO`            | `stack_LIFO`                         |
    | Stack-EmpPop           | `stk_cons_non_empty`       | `stack_empty_unmatched_push`         |

  * [`spec_history.v`](stack/spec_history.v):
    LAT<sup>hist</sup><sub>hb</sub> spec. (Figure 4 and 9)

    | Paper                      | Coq                             | Related Coq definitions                                        |
    |----------------------------|---------------------------------|----------------------------------------------------------------|
    | Hist-Hb-New-Stack          | `new_stack_spec`                | `new_stack_spec'`                                              |
    | Hist-Hb-Try-{Push,Pop}     | `try_{push,pop}_spec`           | `try_{push,pop}_spec'`                                         |
    | Hist-Hb-{Push,Pop}         | `{push,pop}_spec`               | `{push,pop}_spec'`                                             |
    | Hist-Hb-Stack-Linearizable | `StackInv_StackLinearizability` |                                                                |
    | StackLinearizable          | `StackLinearizability`          |                                                                |
    | Stack-Lin-Perm             | `LIN_PERM`                      | `≡ₚ` is a notation for `Permutation` from Coq standard library |
    | Stack-Lin-Reorder-EmpPop   | `XO_LIN_AGREE`                  |                                                                |
    | Stack-Lin-Hb-To            | `HB_LIN`                        | `hb_ord` in `history/history.v`                                |
    | Stack-Lin-Interp           | `INTERP_LIN`                    |                                                                |
    | `interp`                   | `stack_run`, `stack_interp`     |                                                                |

* library verifications
  * [`proof_treiber_graph.v`](stack/proof_treiber_graph.v):
    Treiber stack satisfies LAT<sub>hb</sub> spec.
  * [`proof_treiber_history.v`](stack/proof_treiber_history.v):
    Treiber stack satisfies LAT<sup>hist</sup><sub>hb</sub> spec (§3.3).
  * [`proof_elim_graph.v`](stack/proof_elim_graph.v):
    Elimination stack satisfies LAT<sub>hb</sub> (assuming LAT<sub>hb</sub>
    specs of stack and exchanger) (§4.1).
* relations of specs
  * [`proof_history_abs.v`](stack/proof_history_abs.v):
    LAT<sup>hist</sup><sub>hb</sub> spec implies LAT<sup>abs</sup><sub>so</sub> spec.
* client verifications
  * [`proof_mp_client_graph.v`](stack/proof_mp_client_graph.v):
    Proof that a pop cannot return empty if the popper has seen an unmatched
    push, proved with LAT<sub>hb</sub>.
  * [`proof_mp_client_history.v`](stack/proof_mp_client_history.v):
    The same client as above, but using LAT<sup>hist</sup><sub>hb</sub>.


### [Exchanger](exchanger) (§4.2)
* implementation
  * [`code.v`](exchanger/code.v): A simple elimination-based exchanger
* specs
  * [`spec_graph.v`](exchanger/spec_graph.v): Simplified
    LAT<sub>hb</sub> spec. (Figure 5 and 10)

    | Paper                    | Coq                                 | Related Coq definitions                                    |
    |--------------------------|-------------------------------------|------------------------------------------------------------|
    | Hb-Exchange              | `exchange_spec`                     | `exchange_spec'`                                           |
    | Hb-Exchanger-Consistency | `ExchangerInv_ExchangerConsistent'` |                                                            |
    | ExchangerConsistent      | `ExchangerConsistent`               |                                                            |
    | Exchanger-Matches        | `xchg_cons_matches`                 |                                                            |
    | Exchanger-So-Sym-Irrefl  | `xchg_cons_com`                     | `symmetric_pair` and `irreflexive_pair` in `graph/graph.v` |
    | Exchanger-So-Functional  | `xchg_cons_com_functional`          | `functional_pair` in `graph/graph.v`                       |
    | Exchanger-Unmatched      | `xchg_cons_unmatched`               |                                                            |

  * [`spec_graph_piggyback.v`](exchanger/spec_graph_piggyback.v):
    The full LAT<sub>hb</sub> spec that exposes inconsistent states between
    matching exchange pairs.
  * [`spec_graph_resource.v`](exchanger/spec_graph_resource.v):
    LAT<sub>hb</sub> spec with resource exchanges.
* library verifications
  * [`proof_graph_piggyback.v`](exchanger/proof_graph_piggyback.v):
    The elimination-based exchanger satisfies the full LAT<sub>hb</sub> spec.
* relations of specs
  * [`proof_graph.v`](exchanger/proof_graph.v):
    The full LAT<sub>hb</sub> spec implies the simplified LAT<sub>hb</sub> spec.
  * [`proof_graph_resource.v`](exchanger/proof_graph_resource.v):
    The full LAT<sub>hb</sub> spec implies the LAT<sub>hb</sub> spec with
    resource exchanges.
* client verifications
  * [`proof_sequential_client.v`](exchanger/proof_sequential_client.v):
    Sequential exchange always fails.
  * [`proof_mp_client.v`](exchanger/proof_mp_client.v):
    Demonstrates successful exchange.


[iRC11]: https://gitlab.mpi-sws.org/iris/gpfsl
[ORC11]: https://gitlab.mpi-sws.org/iris/gpfsl/-/tree/master/orc11
[RC11]: https://plv.mpi-sws.org/scfix/
[Iris]: https://gitlab.mpi-sws.org/iris/iris
