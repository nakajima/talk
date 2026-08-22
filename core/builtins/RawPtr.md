An opaque machine pointer for unsafe memory operations.

`RawPtr` does not encode pointee type, allocation bounds, initialization, ownership, or lifetime. Creating, offsetting, loading from, or storing through one requires the unsafe memory contracts exposed by Core; safe containers should retain typed storage instead.
