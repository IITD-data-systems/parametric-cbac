#ifndef MEMENTO_ITERATOR_ISOLATION_H
#define MEMENTO_ITERATOR_ISOLATION_H
// GCC noipa forbids interprocedural optimization across these boundaries,
// including LTO inlining/cloning and caller/callee propagation. They remain
// cold out-of-line islands; ordinary V4 methods retain their original flags.
#define MEMENTO_ITERATOR_COLD __attribute__((noipa,noinline,noclone,cold,optimize("no-inline")))
// Ordinary node arrivals use this too: do not change V4's miss-path branch
// probabilities by incorrectly marking the neutral dispatch itself cold.
#define MEMENTO_DISPATCH_ISLAND __attribute__((noipa,noinline,noclone))
#endif
