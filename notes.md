## Notes on reclaiming the interpretation of GPFSL protocols

This is used in atomic-borrow-based protocols. The initialization of the atomic-borrow-based protocol requires to prove the inheritance.
In particular, we turn `&{κ} (∃ v, l ↦ v ∗ P v)` (a unique borrow) into an atomic-borrow-based protocol with an interpretation `I`, and we have to guarantee that when inheritance of the unique borrow happens we can still reclaim `∃ v, l ↦ v ∗ P v`.
Thus we have to show that the content of the atomic-borrow-based protocol implies `∃ v, l ↦ v ∗ P v`.
The content of the atomic-borrow-based protocol does contain the ownership of `l`, *and* the iGPS construction `GPS_INV` that wraps around `I(v)`.
So we rely on the fact that we can extract `I(v)` from `GPS_INV`.
Furthermore, we need that `I(v)` contains at least `P v`.

This particular pattern is useful in `mutex`, and is important in `rwlock`.
