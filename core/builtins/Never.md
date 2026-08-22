The uninhabited type of computations that cannot return normally.

A `Never` result can satisfy any expected result type because no value reaches that boundary. Trapping, abortive effects, and other divergent control flow may therefore type-check where a concrete result is expected.
