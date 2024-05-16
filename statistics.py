'''
DESCRIPTION:
This program counts the LOC of proof lines in the `files`.
Specifically, it counts the number of lines between `Proof.` (or `Next Obligation`) and `Qed.` (exclusive)
without comment lines and empty lines.

ASSUMPTION:
* Each file must be successfully compiled.
* Any line starting with `Proof` (or `Next Obligation`) keyword (excluding comments) will be counted as beginning of proof.
* Keyword `Qed` (case sensitive) should not be used for other purposes outside the comments.
* If any line that starts/ends a proof contains other stuffs, then it will be counted as proof lines.
  e.g.
    ```Proof using All.```        : beginning of proof. not a proof line
    ```Proof. apply _. ```        : beginning of proof. counted as a proof line
    ```Proof. (* comments *)```   : beginning of proof. counted as a proof line
* No `comments in comments` (e.g. (* comments... (* old comments. *) comments. *))
* No nested proofs
* Any lines that contain multiple line comments should not contain valid proof lines.
  e.g.
    What's incorrect:
    ```
    apply abcd. (* Comments
        are continued
        until here. *) rewrite efgh.
    ```
    which should be:
    ```
    apply abcd.
    (** Comments
        are continued
        until here. *)
    rewrite efgh.
    ```

EXAMPLES:
```
Proof.
    appy abcd.

    (* rewrite... *)
    rewrite abcd'.

    have ? : 1 < 2. {
        lia.
    }
    apply cd.
Qed.
```
proof LOC: 6

```
Proof. oSteps. Unshelve. apply abcd. Qed.
```
proof LOC: 1
'''

files = [
    # Treiber's stack
    './gpfsl-examples/stack/proof_treiber_history.v',
    './gpfsl-examples/stack/proof_treiber_history_diaframe.v',
    './gpfsl-examples/stack/proof_treiber_history_old.v',
    './gpfsl-examples/stack/spec_history_old.v',
    './gpfsl-examples/stack/event.v',

    # Spinlock
    './gpfsl-examples/lock/proof_spin_lock_trylock_history.v',
    './gpfsl-examples/lock/proof_spin_lock_trylock_history_diaframe.v',
    './gpfsl-examples/lock/comparison/lock.v',

    # Michael-Scott queue
    './gpfsl-examples/queue/proof_ms_history.v',
    './gpfsl-examples/queue/proof_ms_history_diaframe.v',
    './gpfsl-examples/queue/proof_ms_abs_graph.v',
    './gpfsl-examples/queue/spec_abs_graph.v',
    './gpfsl-examples/queue/spec_graph.v',

    # Folly
    './gpfsl-examples/folly/proof_turnSequencer_composition.v',
    './gpfsl-examples/folly/proof_turnSequencer_composition_diaframe.v',
    './gpfsl-examples/folly/proof_singleElementQueue_composition.v',
    './gpfsl-examples/folly/proof_singleElementQueue_composition_diaframe.v',
    './gpfsl-examples/folly/proof_mpmcqueue_composition.v',
    './gpfsl-examples/folly/proof_mpmcqueue_composition_diaframe.v',

    # Exchanger
    './gpfsl-examples/exchanger/proof_composition.v',
    './gpfsl-examples/exchanger/proof_composition_diaframe.v',
    './gpfsl-examples/exchanger/proof_graph_piggyback.v',
    './gpfsl-examples/exchanger/proof_graph_resource.v',

    # Elimination stack
    './gpfsl-examples/stack/proof_elim_composition.v',
    './gpfsl-examples/stack/proof_elim_composition_diaframe.v',
    './gpfsl-examples/stack/proof_elim_graph.v',
    './gpfsl-examples/stack/spec_graph.v',

    # Arc
    './gpfsl-examples/arc/proof_composition.v',
    './gpfsl-examples/arc/comparison/arc.v',
    './gpfsl-examples/arc/comparison/arc_cmra.v',
]

def count_proof_loc(file, print_proof_lines = False):
    fd = open(file, 'r')
    lines = fd.readlines()
    fd.close()

    ret = 0
    is_proving = False
    is_comment = False

    for line in lines:
        line = line.strip()

        # Skip empty lines
        if line == '': continue

        # Processing comment lines
        if is_comment or line.startswith('(*'):
            is_comment = not ('*)' in line)
            continue

        # Processing of lines signaling start/end of proof
        proof_start = line.startswith('Proof') or line.startswith('Next Obligation')
        proof_end = 'Qed.' in line
        split_by_period = [x for x in line.split('.') if x]

        if proof_start and proof_end: # Single line proof
            ret += 1
            if print_proof_lines: print(line)
            continue

        if proof_start:
            is_proving = True
            if len(split_by_period) > 1:
                # If proof starting line contains more than `Proof.` or `Proof using ....`,
                # then count it as proof line
                ret += 1
                if print_proof_lines: print(line)
            continue

        if proof_end:
            is_proving = False
            if len(split_by_period) > 1:
                # If proof ending line contains more than `Proof.` or `Proof using ....`,
                # then count it as proof line
                ret += 1
                if print_proof_lines: print(line)
            continue

        # General case
        if is_proving:
            ret += 1
            if print_proof_lines: print(line)

    return ret

for file in files:
    print('%s: %d' % (file, count_proof_loc(file)))
