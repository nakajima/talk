/* Shared native runtime (talk-native-runtime).
 *
 * Emitted verbatim at the top of every generated translation unit, so the
 * output is one self-contained file: `talk c x.tlk | cc -O2 -x c -`.
 *
 * Values are unchecked here on purpose. MIR's `scalar_ty` gate has already
 * typed every operand, and unlike bytecode -- which the VM may decode from
 * untrusted bytes and therefore must verify (Leroy 2003) -- generated C is
 * produced by this compiler in the same process. The differential tests in
 * tests/c_backend_tests.rs are what pin the semantics.
 *
 * Value aggregates -- records, tuples, enum payloads, cells -- live in a
 * bump arena released at exit. That is a representation choice, not a
 * missing lifetime: `needs_drop` is false for a struct that owns nothing,
 * so MIR emits no release because there is no resource. The VM makes the
 * same choice differently, boxing them in `Rc` for O(1) value copies. The
 * arena's cost is that it never reclaims during a run; the fix is to stop
 * boxing non-escaping aggregates, which needs typed MIR locals.
 *
 * Buffers, `'heap` objects, and regions are real resources with explicit
 * MIR instructions, and they are reclaimed exactly -- the generated
 * program fails its own exit balance check otherwise.
 */

/* `-std=c11` is strict ISO, so the POSIX declarations the host IO
 * operations use are only visible with the feature test macros. They
 * have to precede every include. `_XOPEN_SOURCE` is what exposes
 * realpath(3), which is XSI rather than base POSIX. */
#ifndef _POSIX_C_SOURCE
#define _POSIX_C_SOURCE 200809L
#endif
#ifndef _XOPEN_SOURCE
#define _XOPEN_SOURCE 700
#endif

#include <float.h>
#include <inttypes.h>
#include <limits.h>
#include <stdatomic.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

/* Platform detection first: later sections test TALK_HAS_POSIX_IO,
 * and a definition that arrived after them would silently compile the
 * host-aware branches out. */
#if defined(__unix__) || defined(__APPLE__)
#include <arpa/inet.h>
#include <dirent.h>
#include <errno.h>
#include <fcntl.h>
#include <netinet/in.h>
#include <poll.h>
#include <sys/ioctl.h>
#include <sys/resource.h>
#include <sys/socket.h>
#include <sys/stat.h>
#include <time.h>
#include <unistd.h>
#define TALK_HAS_POSIX_IO 1
#include <pthread.h>
#endif

/* The ABI this translation unit assumes. A target that broke one of these
 * would compile and then misbehave, which is the one failure mode the
 * backend otherwise avoids -- so it fails here instead. Pointers only have
 * to *fit* a slot: MIR sizes every non-byte memory element at 8 bytes, and
 * a narrower pointer simply leaves the rest of its slot unused. */
_Static_assert(CHAR_BIT == 8, "Talk assumes 8-bit bytes");
_Static_assert(sizeof(int64_t) == 8, "Talk's Int is 64 bits");
_Static_assert(sizeof(double) == 8, "Talk's Float is an IEEE double");
_Static_assert(sizeof(void *) <= 8, "a pointer must fit an 8-byte memory slot");

/* Blocks the C compiler proves unreachable still get a label emitted, and
 * MIR keeps every function after inlining just as the bytecode backend
 * keeps every chunk. Both are the C compiler's to discard. */
#pragma GCC diagnostic ignored "-Wunused-label"
#pragma GCC diagnostic ignored "-Wunused-function"

enum {
    TALK_UNIT = 0,
    TALK_BOOL = 1,
    TALK_INT = 2,
    TALK_AGG = 3,
    /* A reified return continuation: the frame it returns from, as the
     * pair (depth, id) the VM's `Value::Cont` carries. */
    TALK_CONT = 4,
    /* A function value: the aggregate's `tag` is the target function and
     * its fields are the captured environment. */
    TALK_CLOSURE = 5,
    /* A raw pointer into managed or static bytes. Unlike the VM's
     * `(address, provenance)` pair this is a machine pointer: the C
     * backend does not simulate a byte memory. */
    TALK_PTR = 6,
    TALK_BYTE = 7,
    TALK_FLOAT = 8,
    /* A `'heap` object handle. Copies alias; the region owns the
     * storage, not the handle. */
    TALK_OBJECT = 9,
    /* A shared mutable box for a captured local. Tagged apart from
     * `TALK_AGG` so the region handle scan skips it. */
    TALK_CELL = 10,
    /* A boxed aggregate stored in its NATIVE layout (ADR 0045): the box
     * header names the published layout, and the payload is the layout's
     * untagged C struct. Boxing and unboxing are copies, not per-field
     * re-tagging. */
    TALK_NATIVE = 11
};

typedef struct TalkAgg TalkAgg;
typedef struct TalkNative TalkNative;

typedef struct {
    uint8_t tag;
    union {
        int64_t i;
        double f;
        TalkAgg *agg;
        TalkNative *native;
        unsigned char *ptr;
        struct TalkObject *obj;
    } v;
} TalkValue;

/* The native box header: the published layout id (indexing the generated
 * accessors below) and the display identity rendering uses. The payload
 * (the layout's TalkL struct) follows immediately. */
struct TalkNative {
    uint32_t layout;
    uint32_t display;
};

#define TALK_NATIVE_PAYLOAD(value) ((void *)((value).v.native + 1))

/* The VM's flat aggregate, verbatim (ADR 0046): `len` slots under the
 * published layout `layout`, a sum's tag in slot 0, spliced children
 * inline. `symbol` is a display identity the emitter assigns: zero for
 * tuples and anonymous products, otherwise an index into `talk_types`.
 * `meta` is runtime-representation metadata for the layout-less
 * containers (a closure's function index); layout-governed values
 * leave it zero. */
struct TalkAgg {
    uint32_t layout;
    uint32_t symbol;
    uint32_t meta;
    uint32_t len;
    TalkValue fields[];
};

/* The sentinel layout of the runtime's own containers — closures,
 * cells, existentials — whose slots are all single values, so element
 * index and slot offset coincide. */
#define TALK_DYN UINT32_MAX

enum {
    TALK_TYPE_TUPLE = 0,
    TALK_TYPE_RECORD = 1,
    TALK_TYPE_ENUM = 2,
    TALK_TYPE_STRING = 3,
    /* A protocol existential: the payload at slot 0, witnesses after.
     * The runtime renders the payload alone, so the witness table must
     * not show up in the output. */
    TALK_TYPE_EXISTENTIAL = 4
};

/* Type names and member names, emitted from the program's catalogs. */
typedef struct {
    const char *name;
    uint8_t kind;
    uint32_t member_count;
    const char *const *members;
} TalkTypeInfo;

/* Set by the generated `main` from a table the emitter writes out. */
static const TalkTypeInfo *talk_types;
static uint32_t talk_type_count;

/* The published layout table as data (ADR 0046): one row per layout id,
 * mirroring the wire descriptors, so the logical operations — the
 * existential boundary's member access, rendering — walk structure the
 * same way the VM does. `child` is UINT32_MAX for a one-slot member. */
typedef struct {
    uint16_t offset;
    uint16_t width;
    uint32_t child;
    uint32_t child_symbol;
} TalkField;

typedef struct {
    uint16_t width;
    uint8_t is_sum;
    const TalkField *fields;
    uint32_t field_count;
    /* Sums: variant v's fields are fields[variant_starts[v] ..
     * variant_starts[v + 1]); variant_starts has variant_count + 1
     * entries. NULL for products. */
    const uint32_t *variant_starts;
    uint32_t variant_count;
} TalkLayoutInfo;

/* Set by the generated `main` from a table the emitter writes out. */
static const TalkLayoutInfo *talk_layouts;
static uint32_t talk_layout_count;

#if defined(TALK_LIBRARY)
/* ---- library boundary (ADR 0048) -----------------------------------
 *
 * A library artifact may not terminate its host. Wrappers arm the
 * boundary before entering generated Talk code; a trap or an exit
 * request longjmps back to the wrapper, which returns it as an error
 * status after complete invocation cleanup. All runtime state is
 * file-scope, so one invocation is active at a time and the owner
 * serializes calls.
 */
#include <setjmp.h>

static jmp_buf talk_lib_boundary;
static int talk_lib_boundary_armed;
static char talk_lib_message[512];
static int talk_lib_exit_status;
static int talk_lib_initialized;
/* Live-resource lists, so teardown after a result was handed out -- or
 * after a trap left arbitrary state -- reclaims everything without
 * running Talk code. */
static struct TalkHeader *talk_lib_allocations;
static struct TalkObject *talk_lib_objects;
static struct TalkRegion *talk_lib_regions;
#endif

/* Noreturn so the C compiler knows a trapping block ends control flow and
 * does not report the function as falling off its end. */
static _Noreturn void talk_trap(const char *message) {
#if defined(TALK_LIBRARY)
    if (talk_lib_boundary_armed) {
        snprintf(talk_lib_message, sizeof talk_lib_message, "%s", message);
        talk_lib_boundary_armed = 0;
        longjmp(talk_lib_boundary, 1);
    }
#endif
    fprintf(stderr, "talk: %s\n", message);
    exit(1);
}

/* ---- aggregate arena ----------------------------------------------
 *
 * Worker-local (ADR 0050): each thread bump-allocates its own chunks, so
 * aggregate construction never contends. A worker that runs Talk code
 * must release its own arena when it retires; `main`'s release stays at
 * process exit.
 */

#define TALK_ARENA_CHUNK ((size_t)1 << 20)

static _Thread_local unsigned char *talk_arena_chunk = NULL;
static _Thread_local size_t talk_arena_used = 0;
static _Thread_local size_t talk_arena_cap = 0;
static _Thread_local unsigned char **talk_arena_chunks = NULL;
static _Thread_local size_t talk_arena_count = 0;
static _Thread_local size_t talk_arena_capacity = 0;

static void *talk_arena_alloc(size_t bytes) {
    size_t aligned = (bytes + 15u) & ~(size_t)15u;
    if (talk_arena_chunk == NULL || talk_arena_used + aligned > talk_arena_cap) {
        size_t size = aligned > TALK_ARENA_CHUNK ? aligned : TALK_ARENA_CHUNK;
        unsigned char *chunk = (unsigned char *)malloc(size);
        if (chunk == NULL) {
            talk_trap("out of memory");
        }
        if (talk_arena_count == talk_arena_capacity) {
            size_t grown = talk_arena_capacity == 0 ? 8 : talk_arena_capacity * 2;
            unsigned char **chunks =
                (unsigned char **)realloc(talk_arena_chunks, grown * sizeof(*chunks));
            if (chunks == NULL) {
                talk_trap("out of memory");
            }
            talk_arena_chunks = chunks;
            talk_arena_capacity = grown;
        }
        talk_arena_chunks[talk_arena_count++] = chunk;
        talk_arena_chunk = chunk;
        talk_arena_cap = size;
        talk_arena_used = 0;
    }
    void *result = talk_arena_chunk + talk_arena_used;
    talk_arena_used += aligned;
    return result;
}

static void talk_arena_release(void) {
    for (size_t index = 0; index < talk_arena_count; index++) {
        free(talk_arena_chunks[index]);
    }
    free(talk_arena_chunks);
    talk_arena_chunks = NULL;
    talk_arena_chunk = NULL;
    talk_arena_count = 0;
    talk_arena_capacity = 0;
    talk_arena_used = 0;
    talk_arena_cap = 0;
}

/* ---- constructors -------------------------------------------------- */

static inline TalkValue talk_unit(void) {
    TalkValue value;
    value.tag = TALK_UNIT;
    value.v.i = 0;
    return value;
}

static inline TalkValue talk_bool(int64_t bit) {
    TalkValue value;
    value.tag = TALK_BOOL;
    value.v.i = bit != 0;
    return value;
}

static inline TalkValue talk_int(int64_t number) {
    TalkValue value;
    value.tag = TALK_INT;
    value.v.i = number;
    return value;
}

static inline TalkValue talk_agg(uint32_t layout, uint32_t symbol, uint32_t meta, uint32_t len) {
    TalkAgg *agg = (TalkAgg *)talk_arena_alloc(sizeof(TalkAgg) + (size_t)len * sizeof(TalkValue));
    agg->layout = layout;
    agg->symbol = symbol;
    agg->meta = meta;
    agg->len = len;
    TalkValue value;
    value.tag = TALK_AGG;
    value.v.agg = agg;
    return value;
}

/* A tagged aggregate with process lifetime, for static values crossing
 * runtimes whose uniform representation is TALK_AGG. */
static inline TalkValue talk_static_agg(uint32_t layout, uint32_t symbol, uint32_t meta, uint32_t len) {
    TalkAgg *agg = (TalkAgg *)malloc(sizeof(TalkAgg) + (size_t)len * sizeof(TalkValue));
    if (agg == NULL) {
        talk_trap("out of memory");
    }
    agg->layout = layout;
    agg->symbol = symbol;
    agg->meta = meta;
    agg->len = len;
    TalkValue value;
    value.tag = TALK_AGG;
    value.v.agg = agg;
    return value;
}

/* A native String-shaped aggregate with process lifetime. Static-value
 * caches build each descriptor once; unlike arena boxes these survive
 * library-call cleanup and are never part of dynamic allocation balance. */
static inline TalkValue talk_static_string_value(uint32_t layout, uint32_t display,
                                                 unsigned char *base, int64_t len) {
    TalkNative *native = (TalkNative *)malloc(sizeof(TalkNative) + 24u);
    if (native == NULL) {
        talk_trap("out of memory");
    }
    native->layout = layout;
    native->display = display;
    unsigned char *payload = (unsigned char *)(native + 1);
    memset(payload, 0, 24u);
    memcpy(payload, &base, sizeof base);
    memcpy(payload + 8u, &len, sizeof len);
    memcpy(payload + 16u, &len, sizeof len);
    TalkValue value;
    value.tag = TALK_NATIVE;
    value.v.native = native;
    return value;
}

/* An aggregate in caller-provided storage: the frame's, for a
 * construction the escape analysis proved cannot outlive it. One slot per
 * site, reused on each execution, so a loop allocates nothing. */
static inline TalkValue talk_agg_in(void *storage, uint32_t layout, uint32_t symbol, uint32_t meta, uint32_t len) {
    TalkAgg *agg = (TalkAgg *)storage;
    agg->layout = layout;
    agg->symbol = symbol;
    agg->meta = meta;
    agg->len = len;
    TalkValue value;
    value.tag = TALK_AGG;
    value.v.agg = agg;
    return value;
}

static inline TalkValue talk_native_box(uint32_t layout, uint32_t display, size_t size) {
    TalkValue value;
    value.tag = TALK_NATIVE;
    value.v.native = (TalkNative *)talk_arena_alloc(sizeof(TalkNative) + size);
    value.v.native->layout = layout;
    value.v.native->display = display;
    return value;
}

/* A native box in caller-provided storage (a frame buffer). */
static inline TalkValue talk_native_box_in(void *storage, uint32_t layout, uint32_t display) {
    TalkValue value;
    value.tag = TALK_NATIVE;
    value.v.native = (TalkNative *)storage;
    value.v.native->layout = layout;
    value.v.native->display = display;
    return value;
}

/* Generated per program, after the layout declarations: the flat form
 * of a native box (rendering, the logical boundary) and the region
 * scan's walk over native boxes. */
static TalkValue talk_native_retag(TalkValue value);
static TalkValue talk_rebox(uint32_t layout, TalkValue flat);
struct TalkObject;
static void talk_native_scan(TalkValue value, struct TalkObject ***out, size_t *count,
                             size_t *capacity);

/* A spliced child copied out of its parent's slots, as the VM's
 * `read_slots` does for an inline member. */
static inline TalkValue talk_slice(TalkValue value, uint32_t offset, uint32_t width,
                                   uint32_t layout, uint32_t symbol) {
    TalkValue child = talk_agg(layout, symbol, 0, width);
    memcpy(child.v.agg->fields, value.v.agg->fields + offset,
           (size_t)width * sizeof(TalkValue));
    return child;
}

/* Replace `span` slots. The VM's `SetField` is copy-on-write over an
 * `Rc`; with no counts to consult, copying unconditionally is the same
 * observable behaviour at a worse constant. A spliced write flattens
 * the source's slots into the span. */
static inline TalkValue talk_set_slots(TalkValue record, uint32_t offset, uint32_t span,
                                       TalkValue field) {
    TalkAgg *from = record.v.agg;
    TalkValue copy = talk_agg(from->layout, from->symbol, from->meta, from->len);
    memcpy(copy.v.agg->fields, from->fields, (size_t)from->len * sizeof(TalkValue));
    if (span == 1) {
        copy.v.agg->fields[offset] = field;
    } else {
        if (field.tag == TALK_NATIVE) {
            field = talk_native_retag(field);
        }
        memcpy(copy.v.agg->fields + offset, field.v.agg->fields,
               (size_t)span * sizeof(TalkValue));
    }
    return copy;
}

/* One member of a flat value, by its table row: a slot, a reconstructed
 * spliced child, or Unit for a zero-width member. */
static TalkValue talk_field_at(TalkValue value, const TalkField *field) {
    if (field->child == UINT32_MAX) {
        return value.v.agg->fields[field->offset];
    }
    if (field->width == 0) {
        return talk_unit();
    }
    return talk_rebox(
        field->child,
        talk_slice(value, field->offset, field->width, field->child, field->child_symbol));
}

/* The logical member operations the existential boundary needs: the
 * container's layout is dynamic, so structure comes from the value's
 * own layout row — exactly the VM's `FieldIndex`/`SetFieldIndex`. */
static TalkValue talk_native_field(TalkValue value, uint32_t index) {
    if (value.tag == TALK_NATIVE) {
        value = talk_native_retag(value);
    }
    uint32_t layout = value.v.agg->layout;
    if (layout == TALK_DYN || layout >= talk_layout_count) {
        return value.v.agg->fields[index];
    }
    return talk_field_at(value, &talk_layouts[layout].fields[index]);
}

static TalkValue talk_native_set_field(TalkValue record, uint32_t index, TalkValue field) {
    if (record.tag == TALK_NATIVE) {
        record = talk_native_retag(record);
    }
    uint32_t layout = record.v.agg->layout;
    if (layout == TALK_DYN || layout >= talk_layout_count) {
        return talk_set_slots(record, index, 1, field);
    }
    const TalkField *site = &talk_layouts[layout].fields[index];
    if (site->child != UINT32_MAX && site->width == 0) {
        return record;
    }
    return talk_set_slots(record, site->offset,
                          site->child == UINT32_MAX ? 1 : site->width, field);
}

/* ---- managed memory -------------------------------------------------
 *
 * The VM models a buffer as an offset into a simulated `Vec<u8>` with a
 * provenance tag, and validates every access against an allocation
 * record. Generated C uses machine pointers instead: an allocation is one
 * `malloc` carrying a reference-counted header, and a pointer into it is
 * just a pointer. The count and the free-at-zero rule are the same, so
 * the exit balance the VM checks is reproduced exactly; what is given up
 * is the VM's bounds and provenance checking, which is a safety net for
 * `unsafe` Talk rather than part of the language semantics.
 *
 * Immortal static data (string and byte literals) lives in one blob the
 * emitter appends. Retaining or freeing a pointer into it is a no-op, the
 * way the VM treats provenance zero.
 *
 * Owner counts are atomic (ADR 0050): a retain is a relaxed increment, a
 * release an acquire-release decrement that frees on the transition to
 * zero, and a uniqueness check an acquire load -- the Arc discipline, so
 * independent owners of one buffer may live on different workers. Atomic
 * ownership protects the count only; whether the payload may cross or be
 * shared between workers is decided by the checked Send/Sync capabilities
 * in the type system, never here.
 */

#define TALK_ALLOC_MAGIC 0x7401C0DEu

typedef struct TalkHeader {
    uint32_t magic;
    _Atomic uint32_t rc;
    uint64_t len;
#if defined(TALK_LIBRARY)
    struct TalkHeader *lib_prev;
    struct TalkHeader *lib_next;
#endif
} TalkHeader;

/* Written once at startup, before any worker exists. */
static const unsigned char *talk_statics_base;
static size_t talk_statics_len;
static _Atomic size_t talk_live_allocations;

/* Through `uintptr_t`: relational comparison of pointers into different
 * objects is undefined in C, and every retain, free, and uniqueness check
 * on managed memory passes through here. Integer addresses compare
 * legally, and the subtraction is done after the lower-bound test so it
 * cannot wrap. */
static inline int talk_is_static(const unsigned char *pointer) {
    uintptr_t address = (uintptr_t)pointer;
    uintptr_t base = (uintptr_t)talk_statics_base;
    return address >= base && (address - base) < (uintptr_t)talk_statics_len;
}

static inline TalkValue talk_pointer(unsigned char *pointer) {
    TalkValue value;
    value.tag = TALK_PTR;
    value.v.ptr = pointer;
    return value;
}

/* The header sits immediately before the payload, so only a base pointer
 * can be freed -- the VM rejects an interior free too, and the magic word
 * turns an emitter bug into a trap instead of heap corruption. */
static inline TalkHeader *talk_header(unsigned char *pointer) {
#if defined(__GNUC__)
    /* Launder provenance: native string literals hand callers a pointer
     * the compiler can trace to `talk_statics`, and constant propagation
     * into inlined retain/free then "proves" a negative offset on the
     * branch `talk_is_static` already made unreachable —
     * -Werror=array-bounds rejects the unit. A register-constraint
     * no-op severs the trace at zero runtime cost. */
    __asm__("" : "+r"(pointer));
#endif
    TalkHeader *header = (TalkHeader *)(void *)(pointer - sizeof(TalkHeader));
    if (header->magic != TALK_ALLOC_MAGIC) {
        talk_trap("free or retain of a pointer that is not an allocation base");
    }
    return header;
}

static TalkValue talk_alloc(TalkValue bytes) {
    if (bytes.v.i < 0) {
        talk_trap("negative allocation size");
    }
    size_t count = (size_t)bytes.v.i;
    /* A zero-length allocation still needs a distinct address. */
    unsigned char *block = (unsigned char *)calloc(sizeof(TalkHeader) + (count == 0 ? 1 : count), 1);
    if (block == NULL) {
        talk_trap("out of memory");
    }
    TalkHeader *header = (TalkHeader *)(void *)block;
    header->magic = TALK_ALLOC_MAGIC;
    /* Unpublished until the pointer is returned, so plain initialization
     * needs no ordering. */
    atomic_init(&header->rc, 1u);
    header->len = count;
#if defined(TALK_LIBRARY)
    header->lib_next = talk_lib_allocations;
    if (talk_lib_allocations != NULL) {
        talk_lib_allocations->lib_prev = header;
    }
    talk_lib_allocations = header;
#endif
    atomic_fetch_add_explicit(&talk_live_allocations, 1u, memory_order_relaxed);
    return talk_pointer(block + sizeof(TalkHeader));
}

static void talk_free(TalkValue value) {
    if (talk_is_static(value.v.ptr)) {
        return;
    }
    TalkHeader *header = talk_header(value.v.ptr);
    /* Acquire-release: the release half orders this owner's writes before
     * the count drop; the acquire half orders the freeing thread after
     * every other owner's drop, so the payload teardown observes them. */
    uint32_t previous = atomic_fetch_sub_explicit(&header->rc, 1u, memory_order_acq_rel);
    if (previous == 0) {
        talk_trap("double free");
    }
    if (previous == 1) {
        header->magic = 0;
        atomic_fetch_sub_explicit(&talk_live_allocations, 1u, memory_order_relaxed);
#if defined(TALK_LIBRARY)
        if (header->lib_prev != NULL) {
            header->lib_prev->lib_next = header->lib_next;
        } else {
            talk_lib_allocations = header->lib_next;
        }
        if (header->lib_next != NULL) {
            header->lib_next->lib_prev = header->lib_prev;
        }
#endif
        free(header);
    }
}

static void talk_retain(TalkValue value) {
    if (talk_is_static(value.v.ptr)) {
        return;
    }
    /* A new owner can only be minted by an existing owner, so relaxed
     * ordering suffices -- the Arc clone rule. */
    atomic_fetch_add_explicit(&talk_header(value.v.ptr)->rc, 1u, memory_order_relaxed);
}

/* Static data is shared forever, so it is never unique -- the VM says the
 * same, which is what keeps copy-on-write correct for literals. */
static TalkValue talk_is_unique(TalkValue value) {
    if (talk_is_static(value.v.ptr)) {
        return talk_bool(0);
    }
    /* Acquire pairs with the release in `talk_free`: observing 1 means
     * every other owner's writes happened-before this in-place mutation
     * decision -- the Arc::get_mut rule that keeps copy-on-write sound. */
    return talk_bool(
        atomic_load_explicit(&talk_header(value.v.ptr)->rc, memory_order_acquire) == 1);
}

static inline TalkValue talk_ptr_add(TalkValue pointer, TalkValue offset, uint32_t size) {
    return talk_pointer(pointer.v.ptr + offset.v.i * (int64_t)size);
}

static inline void talk_mem_copy(TalkValue from, TalkValue to, TalkValue len) {
    memmove(to.v.ptr, from.v.ptr, (size_t)len.v.i);
}

/* Loads and stores. The element class is known at emit time, so each one
 * is a direct access rather than a switch. Words are host-endian; nothing
 * outside this file reads them. */
static inline TalkValue talk_load_byte(TalkValue p) {
    TalkValue v;
    v.tag = TALK_BYTE;
    v.v.i = (int64_t)*p.v.ptr;
    return v;
}

static inline TalkValue talk_load_i64(TalkValue p) {
    int64_t word;
    memcpy(&word, p.v.ptr, sizeof word);
    return talk_int(word);
}

static inline TalkValue talk_load_f64(TalkValue p) {
    TalkValue v;
    v.tag = TALK_FLOAT;
    memcpy(&v.v.f, p.v.ptr, sizeof v.v.f);
    return v;
}

static inline TalkValue talk_load_bool(TalkValue p) {
    int64_t word;
    memcpy(&word, p.v.ptr, sizeof word);
    return talk_bool(word != 0);
}

static inline TalkValue talk_load_ptr(TalkValue p) {
    unsigned char *pointer;
    memcpy(&pointer, p.v.ptr, sizeof pointer);
    return talk_pointer(pointer);
}

static inline void talk_store_byte(TalkValue p, TalkValue v) { *p.v.ptr = (unsigned char)v.v.i; }

static inline void talk_store_word(TalkValue p, int64_t word) {
    memcpy(p.v.ptr, &word, sizeof word);
}

static inline void talk_store_f64(TalkValue p, TalkValue v) {
    memcpy(p.v.ptr, &v.v.f, sizeof v.v.f);
}

static inline void talk_store_ptr(TalkValue p, TalkValue v) {
    memcpy(p.v.ptr, &v.v.ptr, sizeof v.v.ptr);
}

/* A `Boxed` slot is eight bytes holding a pointer to one `TalkValue`.
 * Overwriting reuses the cell, so a loop that stores through the same slot
 * does not grow the arena -- the VM guards the same property with
 * `boxed_store_reuses_the_cell_slot`. */
static inline TalkValue talk_load_boxed(TalkValue p) {
    TalkValue *cell;
    memcpy(&cell, p.v.ptr, sizeof cell);
    if (cell == NULL) {
        talk_trap("read of a global before its initializer ran");
    }
    return *cell;
}

static void talk_store_boxed(TalkValue p, TalkValue v) {
    TalkValue *cell;
    memcpy(&cell, p.v.ptr, sizeof cell);
    if (cell == NULL) {
        cell = (TalkValue *)talk_arena_alloc(sizeof *cell);
        memcpy(p.v.ptr, &cell, sizeof cell);
    }
    *cell = v;
}

/* ---- stack depth ----------------------------------------------------
 *
 * The VM caps live frames at `MAX_FRAMES` and reports a clean overflow.
 * Generated C runs on the machine stack, where the same program would
 * take SIGSEGV instead, so each function checks on entry.
 *
 * The bound is on stack *bytes*, not on a frame count: the VM's million
 * frames against a typical eight-megabyte stack would fault long before
 * the count was reached, and an emitted frame's size varies with the
 * function's locals. Measuring the distance from an anchor taken in
 * `main` bounds the resource that actually runs out, and costs one
 * subtraction and one compare on entry -- with nothing to undo on the way
 * out, which is what keeps it off the return paths.
 *
 * The budget is read from the process at startup rather than assumed: a
 * fixed guess crashes on any host whose stack is smaller than the guess,
 * which `ulimit -s 1024` demonstrates. `-DTALK_STACK_BUDGET=<bytes>`
 * pins it when the limit cannot be read.
 */

/* Worker-local (ADR 0050): every thread that enters Talk code measures
 * against its own stack, and must call `talk_stack_init` with an anchor
 * on that stack first — the zero budget a fresh thread starts with makes
 * an uninitialized entry trap cleanly instead of faulting. */
static _Thread_local uintptr_t talk_stack_anchor;
static _Thread_local uintptr_t talk_stack_budget;

/* An eighth of the stack, at least 64 KiB, is kept back: the frame that
 * trips the guard still has to reach `talk_trap` and format a message. */
static void talk_stack_init(uintptr_t anchor) {
    talk_stack_anchor = anchor;
#ifdef TALK_STACK_BUDGET
    talk_stack_budget = (uintptr_t)(TALK_STACK_BUDGET);
    return;
#else
    size_t available = (size_t)8 * 1024 * 1024;
#if defined(TALK_HAS_POSIX_IO)
    struct rlimit limit;
    if (getrlimit(RLIMIT_STACK, &limit) == 0 && limit.rlim_cur != RLIM_INFINITY
        && limit.rlim_cur > 0) {
        available = (size_t)limit.rlim_cur;
    }
#endif
    size_t reserve = available / 8;
    if (reserve < 64u * 1024u) {
        reserve = 64u * 1024u;
    }
    talk_stack_budget = available > reserve ? (uintptr_t)(available - reserve) : (uintptr_t)0;
#endif
}

static inline void talk_frame_enter(void) {
    char probe;
    uintptr_t here = (uintptr_t)&probe;
    /* Absolute distance, so the direction the stack grows does not
     * matter. */
    uintptr_t used = here > talk_stack_anchor ? here - talk_stack_anchor
                                              : talk_stack_anchor - here;
    if (used > talk_stack_budget) {
        talk_trap("call stack overflow");
    }
}

/* ---- frames, handlers, and unwinding -------------------------------
 *
 * Effects (ADR 0027) need three things the C stack does not provide on
 * its own: frame identity, a handler stack, and a way to leave several
 * activations at once.
 *
 * Frame identity is a shadow stack. Every generated function pushes a
 * fresh id on entry and pops on every exit, so a continuation -- which is
 * the pair (depth, id), exactly as `Value::Cont` carries it -- can be
 * tested for liveness the way the VM tests it: the frame at that depth
 * still has that id.
 *
 * Unwinding is a return-status protocol rather than `setjmp`/`longjmp`.
 * MIR already models it explicitly: calls carry an optional cleanup block
 * and `Term::UnwindRet` ends one. So `talk_unwinding` is set, each frame
 * returns, and each call site asks whether it is the continuation's target
 * (deliver the value as this frame's return) or not (run cleanup, keep
 * unwinding). Continuations here are one-shot and outward-only, so no
 * stack is ever copied or resumed.
 *
 * All of it is worker-local (ADR 0050): a worker owns one shadow stack,
 * one handler stack, one search floor, and one unwind state, exactly the
 * per-worker interpreter state the VM keeps. Handler delimiters and
 * frame identities never cross workers — a task does not inherit
 * frame-bound handlers from the worker that created it.
 */

static _Thread_local uint32_t *talk_frames = NULL;
static _Thread_local size_t talk_depth = 0;
static _Thread_local size_t talk_frame_capacity = 0;
static _Thread_local uint32_t talk_next_frame_id = 1;

static _Thread_local int talk_unwinding = 0;
static _Thread_local size_t talk_unwind_depth = 0;
static _Thread_local uint32_t talk_unwind_frame = 0;
static _Thread_local TalkValue talk_unwind_value;

typedef struct {
    uint32_t effect;
    TalkValue clause;
    TalkValue cont;
    size_t depth;
    uint32_t frame_id;
} TalkHandler;

static _Thread_local TalkHandler *talk_handlers = NULL;
static _Thread_local size_t talk_handler_count = 0;
static _Thread_local size_t talk_handler_capacity = 0;
/* `SIZE_MAX` is "no floor", matching the VM's `handler_floor` start. */
static _Thread_local size_t talk_handler_floor = SIZE_MAX;

static uint32_t talk_enter(void) {
    if (talk_depth == talk_frame_capacity) {
        size_t grown = talk_frame_capacity == 0 ? 256 : talk_frame_capacity * 2;
        uint32_t *frames = (uint32_t *)realloc(talk_frames, grown * sizeof(*frames));
        if (frames == NULL) {
            talk_trap("out of memory");
        }
        talk_frames = frames;
        talk_frame_capacity = grown;
    }
    uint32_t id = talk_next_frame_id++;
    talk_frames[talk_depth++] = id;
    return id;
}

static inline void talk_leave(void) { talk_depth--; }

static inline TalkValue talk_cont(size_t depth, uint32_t frame_id) {
    TalkValue value;
    value.tag = TALK_CONT;
    value.v.i = (int64_t)(((uint64_t)depth << 32) | (uint64_t)frame_id);
    return value;
}

static inline size_t talk_cont_depth(TalkValue cont) {
    return (size_t)((uint64_t)cont.v.i >> 32);
}

static inline uint32_t talk_cont_frame(TalkValue cont) {
    return (uint32_t)((uint64_t)cont.v.i & 0xFFFFFFFFu);
}

/* A frame is live when the shadow stack still holds its id at its depth --
 * the VM's `frames.get(depth).id == frame_id` check. */
static inline int talk_frame_live(size_t depth, uint32_t frame_id) {
    return depth < talk_depth && talk_frames[depth] == frame_id;
}

/* Whether the in-flight unwind ends at this frame, in which case the frame
 * returns the delivered value instead of propagating. */
static inline int talk_unwind_targets(size_t depth, uint32_t frame_id) {
    return talk_unwinding && talk_unwind_depth == depth && talk_unwind_frame == frame_id;
}

static inline TalkValue talk_unwind_take(void) {
    talk_unwinding = 0;
    return talk_unwind_value;
}

static void talk_push_handler(uint32_t effect, TalkValue clause, TalkValue cont, size_t depth,
                              uint32_t frame_id) {
    /* Entries whose installing frame has exited are stale; the VM drops
     * them here rather than on return, and so do we. */
    while (talk_handler_count > 0) {
        TalkHandler *top = &talk_handlers[talk_handler_count - 1];
        if (talk_frame_live(top->depth, top->frame_id)) {
            break;
        }
        talk_handler_count--;
    }
    if (talk_handler_count == talk_handler_capacity) {
        size_t grown = talk_handler_capacity == 0 ? 64 : talk_handler_capacity * 2;
        TalkHandler *grown_handlers =
            (TalkHandler *)realloc(talk_handlers, grown * sizeof(*grown_handlers));
        if (grown_handlers == NULL) {
            talk_trap("out of memory");
        }
        talk_handlers = grown_handlers;
        talk_handler_capacity = grown;
    }
    TalkHandler *entry = &talk_handlers[talk_handler_count++];
    entry->effect = effect;
    entry->clause = clause;
    entry->cont = cont;
    entry->depth = depth;
    entry->frame_id = frame_id;
}

/* Nearest installed handler for the effect, searching below the floor so a
 * clause does not re-find the handler it is running under. */
static void talk_find_handler(uint32_t effect, TalkValue *clause, TalkValue *cont,
                              TalkValue *index) {
    size_t limit = talk_handler_floor < talk_handler_count ? talk_handler_floor : talk_handler_count;
    for (size_t position = limit; position > 0; position--) {
        TalkHandler *entry = &talk_handlers[position - 1];
        if (entry->effect == effect && talk_frame_live(entry->depth, entry->frame_id)) {
            *clause = entry->clause;
            *cont = entry->cont;
            *index = talk_int((int64_t)(position - 1));
            return;
        }
    }
    talk_trap("perform with no installed handler");
}

static inline TalkValue talk_get_floor(void) {
    return talk_int(talk_handler_floor == SIZE_MAX ? INT64_MAX : (int64_t)talk_handler_floor);
}

static inline void talk_set_floor(TalkValue floor) {
    talk_handler_floor = floor.v.i < 0 ? SIZE_MAX : (size_t)floor.v.i;
}

/* Begin an unwind to `cont`. The caller has already handled the case where
 * the continuation targets the aborting frame itself. */
static void talk_abort_to(TalkValue cont, TalkValue value) {
    if (talk_unwinding) {
        talk_trap("abort during abort unwinding");
    }
    size_t depth = talk_cont_depth(cont);
    uint32_t frame_id = talk_cont_frame(cont);
    if (!talk_frame_live(depth, frame_id)) {
        /* A frame that traveled inside a suspended extent (ADR 0065)
         * resumes at a different depth; identity is the frame id, the
         * packed depth is only a hint. */
        int found = 0;
        for (size_t scan = talk_depth; scan > 0; scan--) {
            if (talk_frames[scan - 1] == frame_id) {
                depth = scan - 1;
                found = 1;
                break;
            }
        }
        if (!found) {
            talk_trap("continuation is no longer live (its scope already exited)");
        }
    }
    /* The aborted computation's handler-search floor dies with it. */
    talk_handler_floor = SIZE_MAX;
    talk_unwinding = 1;
    talk_unwind_depth = depth;
    talk_unwind_frame = frame_id;
    talk_unwind_value = value;
}

/* ---- one-shot resumptions (ADR 0064/0065) ---------------------------
 *
 * Native suspension is a return-status protocol, the sibling of the
 * abort protocol above. Resumable functions (a backend fixpoint from
 * the suspend sites) keep their locals in a heap TalkResumeFrame; a
 * suspending perform records the in-flight suspension and returns, each
 * resumable call site links its frame and returns, and the frame whose
 * identity matches the target entry roots the segment, calls the clause
 * with the stashed arguments plus the resumption slot, and returns the
 * clause's result — on first suspension that return IS the abort
 * semantics, and under talk_resume_extent's re-entry the same return
 * delivers the clause result as resume's answer. Cancellation re-enters
 * with talk_unwinding pre-set, so the emitted per-site cleanup blocks
 * (ADR 0027) unwind the extent.
 */

static TalkValue talk_dispatch(uint32_t function, const TalkValue *env, const TalkValue *args);

typedef struct TalkResumeFrame {
    TalkValue (*impl)(struct TalkResumeFrame *);
    struct TalkResumeFrame *child;
    const TalkValue *env;
    uint32_t id;
    uint32_t rpc;
    TalkValue l[];
} TalkResumeFrame;

static _Thread_local int talk_suspend_pending;
/* Set by an impl's detach-return (its frame moved into a segment),
 * consumed by whichever invoker (wrapper or re-enterer) would otherwise
 * free the frame. LIFO by construction: each level consumes before
 * setting its own. */
static _Thread_local int talk_frame_detached;
static _Thread_local TalkResumeFrame *talk_suspend_child;
static _Thread_local uint32_t talk_suspend_target_id;
static _Thread_local size_t talk_suspend_slot;
static _Thread_local TalkValue talk_resume_delivery;

typedef struct {
    TalkResumeFrame *root;
    TalkValue clause;
    TalkValue *args;
    size_t arg_count;
    TalkHandler *handlers;
    size_t handler_count;
    int live;
} TalkSegment;

static _Thread_local TalkSegment *talk_segments;
static _Thread_local size_t talk_segment_count;
static _Thread_local size_t talk_segment_capacity;

static TalkResumeFrame *talk_resume_frame_new(
    size_t n_locals, TalkValue (*impl)(TalkResumeFrame *), const TalkValue *env) {
    TalkResumeFrame *fr = (TalkResumeFrame *)calloc(
        1, sizeof(TalkResumeFrame) + n_locals * sizeof(TalkValue));
    if (fr == NULL) {
        talk_trap("out of memory");
    }
    fr->impl = impl;
    fr->env = env;
    return fr;
}

/* Re-enter the shadow stack under a frame's original identity: handler
 * entries and delimiters captured before the suspension keep naming it. */
static void talk_reenter_identity(uint32_t id) {
    if (talk_depth == talk_frame_capacity) {
        size_t grown = talk_frame_capacity == 0 ? 64 : talk_frame_capacity * 2;
        uint32_t *frames = (uint32_t *)realloc(talk_frames, grown * sizeof(*frames));
        if (frames == NULL) {
            talk_trap("out of memory");
        }
        talk_frames = frames;
        talk_frame_capacity = grown;
    }
    talk_frames[talk_depth++] = id;
}

/* Record an in-flight suspension: resolve the handler exactly as a
 * perform would, allocate the resumption slot, and stash the clause and
 * arguments for the installer's landing site. */
static void talk_suspend_begin(uint32_t effect, const TalkValue *args, size_t argc) {
    if (talk_unwinding) {
        talk_trap("suspend during an unwind");
    }
    if (talk_suspend_pending) {
        talk_trap("suspend during a suspension");
    }
    size_t limit = talk_handler_floor < talk_handler_count
        ? talk_handler_floor
        : talk_handler_count;
    size_t found = SIZE_MAX;
    for (size_t scan = limit; scan > 0; scan--) {
        TalkHandler *entry = &talk_handlers[scan - 1];
        if (entry->effect == effect && talk_frame_live(entry->depth, entry->frame_id)) {
            found = scan - 1;
            break;
        }
    }
    if (found == SIZE_MAX) {
        talk_trap("perform with no installed handler");
    }
    size_t slot = talk_segment_count;
    for (size_t scan = 0; scan < talk_segment_count; scan++) {
        if (!talk_segments[scan].live) {
            slot = scan;
            break;
        }
    }
    if (slot == talk_segment_count) {
        if (talk_segment_count == talk_segment_capacity) {
            size_t grown = talk_segment_capacity == 0 ? 8 : talk_segment_capacity * 2;
            TalkSegment *segments =
                (TalkSegment *)realloc(talk_segments, grown * sizeof(*segments));
            if (segments == NULL) {
                talk_trap("out of memory");
            }
            talk_segments = segments;
            talk_segment_capacity = grown;
        }
        talk_segment_count++;
    }
    TalkSegment *segment = &talk_segments[slot];
    memset(segment, 0, sizeof(*segment));
    segment->clause = talk_handlers[found].clause;
    segment->arg_count = argc;
    if (argc > 0) {
        segment->args = (TalkValue *)malloc(argc * sizeof(TalkValue));
        if (segment->args == NULL) {
            talk_trap("out of memory");
        }
        memcpy(segment->args, args, argc * sizeof(TalkValue));
    }
    segment->live = 1;
    talk_suspend_slot = slot;
    talk_suspend_target_id = talk_handlers[found].frame_id;
    talk_suspend_child = NULL;
    talk_suspend_pending = 1;
}

static void talk_suspend_link(TalkResumeFrame *fr) {
    fr->child = talk_suspend_child;
    talk_suspend_child = fr;
}

static inline int talk_suspend_is_mine(uint32_t frame_id) {
    return talk_suspend_pending && talk_suspend_target_id == frame_id;
}

/* The installer's landing: root the segment with the linked chain,
 * capture the handler entries of the extent (relative depths), open the
 * floor, and run the clause with the stashed arguments plus the slot.
 * The caller returns this result — abort semantics on first suspension,
 * resume's answer under re-entry. */
static TalkValue talk_suspend_finish(size_t installer_depth) {
    TalkSegment *segment = &talk_segments[talk_suspend_slot];
    size_t slot = talk_suspend_slot;
    segment->root = talk_suspend_child;
    talk_suspend_pending = 0;
    talk_suspend_child = NULL;
    /* Live entries installed by extent frames sit above the installer's
     * depth and form a suffix once stale entries are dropped. */
    size_t keep = talk_handler_count;
    while (keep > 0) {
        TalkHandler *entry = &talk_handlers[keep - 1];
        if (talk_frame_live(entry->depth, entry->frame_id)
            && entry->depth < installer_depth) {
            break;
        }
        keep--;
    }
    size_t captured = 0;
    for (size_t scan = keep; scan < talk_handler_count; scan++) {
        TalkHandler *entry = &talk_handlers[scan];
        if (talk_frame_live(entry->depth, entry->frame_id)) {
            captured++;
        }
    }
    if (captured > 0) {
        segment->handlers = (TalkHandler *)malloc(captured * sizeof(TalkHandler));
        if (segment->handlers == NULL) {
            talk_trap("out of memory");
        }
        size_t at = 0;
        for (size_t scan = keep; scan < talk_handler_count; scan++) {
            TalkHandler *entry = &talk_handlers[scan];
            if (talk_frame_live(entry->depth, entry->frame_id)) {
                segment->handlers[at] = *entry;
                segment->handlers[at].depth -= installer_depth;
                at++;
            }
        }
        segment->handler_count = captured;
    }
    talk_handler_count = keep;
    talk_handler_floor = SIZE_MAX;
    size_t argc = segment->arg_count;
    TalkValue clause = segment->clause;
    TalkValue stack_args[8];
    TalkValue *a = stack_args;
    if (argc + 1 > 8) {
        a = (TalkValue *)malloc((argc + 1) * sizeof(TalkValue));
        if (a == NULL) {
            talk_trap("out of memory");
        }
    }
    for (size_t i = 0; i < argc; i++) {
        a[i] = segment->args[i];
    }
    a[argc] = talk_int((int64_t)slot);
    free(segment->args);
    segment->args = NULL;
    segment->arg_count = 0;
    TalkValue result = talk_dispatch(clause.v.agg->meta, clause.v.agg->fields, a);
    if (a != stack_args) {
        free(a);
    }
    if (talk_suspend_pending) {
        talk_trap("a suspending handler clause is not supported on this target yet");
    }
    return result;
}

/* Re-enter one suspended frame; free it once it is done for good (a
 * frame that detached again belongs to the new segment). */
static TalkValue talk_reenter(TalkResumeFrame *fr) {
    TalkValue value = fr->impl(fr);
    if (talk_frame_detached) {
        talk_frame_detached = 0;
    } else {
        free(fr);
    }
    return value;
}

static size_t talk_segment_take(TalkValue cont) {
    /* The Resumption value is a one-int-field core struct; depending on
     * the site it arrives tagged (fields[0]), boxed native (payload's
     * first word), or already unwrapped to its slot integer. */
    int64_t raw;
    if (cont.tag == TALK_AGG) {
        raw = cont.v.agg->fields[0].v.i;
    } else if (cont.tag == TALK_NATIVE) {
        raw = *(const int64_t *)TALK_NATIVE_PAYLOAD(cont);
    } else {
        raw = cont.v.i;
    }
    size_t slot = (size_t)raw;
    if (raw < 0 || slot >= talk_segment_count || !talk_segments[slot].live) {
        talk_trap("resumption already spent (one-shot)");
    }
    talk_segments[slot].live = 0;
    return slot;
}

/* resume(k, v): splice by re-entry. Handler entries re-install under
 * the root's unchanged identity at the current depth; the emitted
 * case-paths recurse to the suspended perform, which reads the
 * delivered value and continues. */
static TalkValue talk_resume_extent(TalkValue cont, TalkValue value) {
    if (talk_unwinding) {
        talk_trap("resume during an unwind");
    }
    size_t slot = talk_segment_take(cont);
    TalkSegment segment = talk_segments[slot];
    size_t base = talk_depth;
    for (size_t i = 0; i < segment.handler_count; i++) {
        TalkHandler entry = segment.handlers[i];
        entry.depth += base;
        if (talk_handler_count == talk_handler_capacity) {
            size_t grown = talk_handler_capacity == 0 ? 8 : talk_handler_capacity * 2;
            TalkHandler *handlers =
                (TalkHandler *)realloc(talk_handlers, grown * sizeof(*handlers));
            if (handlers == NULL) {
                talk_trap("out of memory");
            }
            talk_handlers = handlers;
            talk_handler_capacity = grown;
        }
        talk_handlers[talk_handler_count++] = entry;
    }
    free(segment.handlers);
    talk_segments[slot].handlers = NULL;
    /* The resumed extent runs under the handlers live HERE plus its own
     * (the dynamic-extent rule, ADR 0064). */
    talk_handler_floor = SIZE_MAX;
    talk_resume_delivery = value;
    TalkValue result = talk_reenter(segment.root);
    if (talk_suspend_pending) {
        talk_trap(
            "a suspension crossed a resumption boundary on this target (not supported yet)");
    }
    return result;
}

static TalkValue talk_resume_take(void) {
    TalkValue value = talk_resume_delivery;
    talk_resume_delivery = talk_unit();
    return value;
}

/* cancel(k): re-enter with the unwind status pre-set and a target no
 * frame claims; the suspended perform jumps to its cleanup edge and
 * every parent's existing unwind check unwinds it in turn. */
static void talk_cancel_extent(TalkValue cont) {
    if (talk_unwinding) {
        talk_trap("cancel during an unwind");
    }
    size_t slot = talk_segment_take(cont);
    TalkSegment segment = talk_segments[slot];
    free(segment.handlers);
    talk_segments[slot].handlers = NULL;
    talk_unwinding = 1;
    talk_unwind_depth = SIZE_MAX;
    talk_unwind_frame = 0;
    talk_unwind_value = talk_unit();
    (void)talk_reenter(segment.root);
    talk_unwinding = 0;
    talk_unwind_value = talk_unit();
}

static void talk_effects_release(void) {
    free(talk_frames);
    free(talk_handlers);
    free(talk_segments);
    talk_frames = NULL;
    talk_handlers = NULL;
    talk_segments = NULL;
    talk_depth = 0;
    talk_frame_capacity = 0;
    talk_handler_count = 0;
    talk_handler_capacity = 0;
    talk_segment_count = 0;
    talk_segment_capacity = 0;
}

/* ---- closures ------------------------------------------------------- */

static inline TalkValue talk_closure(uint32_t function, uint32_t captured) {
    TalkValue value = talk_agg(TALK_DYN, 0, function, captured);
    value.tag = TALK_CLOSURE;
    return value;
}

/* ---- integer operations -------------------------------------------- */

/* Talk `Int` wraps (the VM uses `i64::wrapping_*`); signed overflow is
 * undefined in C, so every wrapping operation goes through `uint64_t`. */
static inline int64_t talk_wrap(uint64_t bits) { return (int64_t)bits; }

static inline TalkValue talk_add(TalkValue a, TalkValue b) {
    return talk_int(talk_wrap((uint64_t)a.v.i + (uint64_t)b.v.i));
}

static inline TalkValue talk_sub(TalkValue a, TalkValue b) {
    return talk_int(talk_wrap((uint64_t)a.v.i - (uint64_t)b.v.i));
}

static inline TalkValue talk_mul(TalkValue a, TalkValue b) {
    return talk_int(talk_wrap((uint64_t)a.v.i * (uint64_t)b.v.i));
}

/* `wrapping_div`: division by zero traps, and INT64_MIN / -1 wraps to
 * INT64_MIN rather than trapping the process. */
static inline TalkValue talk_div(TalkValue a, TalkValue b) {
    if (b.v.i == 0) {
        talk_trap("division by zero");
    }
    if (a.v.i == INT64_MIN && b.v.i == -1) {
        return talk_int(INT64_MIN);
    }
    return talk_int(a.v.i / b.v.i);
}

static inline TalkValue talk_and(TalkValue a, TalkValue b) { return talk_int(a.v.i & b.v.i); }
static inline TalkValue talk_or(TalkValue a, TalkValue b) { return talk_int(a.v.i | b.v.i); }
static inline TalkValue talk_xor(TalkValue a, TalkValue b) { return talk_int(a.v.i ^ b.v.i); }
static inline TalkValue talk_not(TalkValue a) { return talk_int(~a.v.i); }

/* Shifts mask the amount to the operand width, as `wrapping_shl` does. */
static inline TalkValue talk_shl(TalkValue a, TalkValue b) {
    return talk_int(talk_wrap((uint64_t)a.v.i << ((uint64_t)b.v.i & 63u)));
}

/* Arithmetic shift right, matching `i64::wrapping_shr`. C leaves the sign
 * bit's treatment implementation-defined, so do it by hand. */
static inline TalkValue talk_shr(TalkValue a, TalkValue b) {
    unsigned amount = (unsigned)((uint64_t)b.v.i & 63u);
    uint64_t bits = (uint64_t)a.v.i >> amount;
    if (a.v.i < 0 && amount != 0) {
        bits |= ~(uint64_t)0 << (64u - amount);
    }
    return talk_int(talk_wrap(bits));
}

/* ---- cells ----------------------------------------------------------
 *
 * Assignment conversion for a captured mutable local (Kranz et al.,
 * ORBIT, 1986): the closure and the defining frame share one box through
 * a copyable handle. The VM keeps these in a slot arena it never
 * reclaims, and so does this -- a cell rides the aggregate arena.
 *
 * A cell carries its own tag rather than reusing `TALK_AGG` so the region
 * handle scan skips it, exactly as the VM's scan skips `Value::Cell`.
 */

static inline TalkValue talk_cell_new(TalkValue initial) {
    TalkValue cell = talk_agg(TALK_DYN, 0, 0, 1);
    cell.v.agg->fields[0] = initial;
    cell.tag = TALK_CELL;
    return cell;
}

static inline TalkValue talk_cell_get(TalkValue cell) { return cell.v.agg->fields[0]; }

static inline void talk_cell_set(TalkValue cell, TalkValue value) {
    cell.v.agg->fields[0] = value;
}

/* ---- existentials ---------------------------------------------------
 *
 * A protocol existential hides its payload behind witness closures at
 * fixed slots: slot 0 drop, slot 1 retain, requirements from 2. Payload
 * first, witnesses after, in one aggregate -- and tagged `TALK_AGG` so the
 * handle scan reaches through both, as the VM's does.
 */

static inline TalkValue talk_existential_payload(TalkValue existential) {
    return existential.v.agg->fields[0];
}

static inline TalkValue talk_existential_witness(TalkValue existential, uint32_t index) {
    return existential.v.agg->fields[index + 1];
}

/* An `InlineArray` read at a runtime index, bounds-checked as the VM's
 * `inline_get` is. One-slot elements read their slot directly. */
static inline TalkValue talk_get_element(TalkValue aggregate, TalkValue index) {
    if (index.v.i < 0 || (uint64_t)index.v.i >= aggregate.v.agg->len) {
        talk_trap("inline_get index out of range");
    }
    return aggregate.v.agg->fields[index.v.i];
}

/* The inline-element form: elements stride by their width and read as
 * spliced children, as the VM's `GetElement` does. */
static inline TalkValue talk_get_element_slice(TalkValue aggregate, TalkValue index,
                                               uint32_t stride, uint32_t layout,
                                               uint32_t symbol) {
    if (index.v.i < 0
        || (uint64_t)index.v.i * stride + stride > aggregate.v.agg->len) {
        talk_trap("inline_get index out of range");
    }
    return talk_rebox(
        layout, talk_slice(aggregate, (uint32_t)index.v.i * stride, stride, layout, symbol));
}

/* ---- float operations ----------------------------------------------- */

static inline TalkValue talk_float(double number) {
    TalkValue value;
    value.tag = TALK_FLOAT;
    value.v.f = number;
    return value;
}

/* Float constants travel as bit patterns so the emitter never has to
 * round-trip one through a decimal literal. */
static inline TalkValue talk_float_bits(uint64_t bits) {
    TalkValue value;
    value.tag = TALK_FLOAT;
    memcpy(&value.v.f, &bits, sizeof value.v.f);
    return value;
}

static inline TalkValue talk_float_add(TalkValue a, TalkValue b) {
    return talk_float(a.v.f + b.v.f);
}
static inline TalkValue talk_float_sub(TalkValue a, TalkValue b) {
    return talk_float(a.v.f - b.v.f);
}
static inline TalkValue talk_float_mul(TalkValue a, TalkValue b) {
    return talk_float(a.v.f * b.v.f);
}
static inline TalkValue talk_float_div(TalkValue a, TalkValue b) {
    return talk_float(a.v.f / b.v.f);
}

static inline TalkValue talk_float_cmp_eq(TalkValue a, TalkValue b) {
    return talk_bool(a.v.f == b.v.f);
}
static inline TalkValue talk_float_cmp_ne(TalkValue a, TalkValue b) {
    return talk_bool(a.v.f != b.v.f);
}
static inline TalkValue talk_float_cmp_lt(TalkValue a, TalkValue b) {
    return talk_bool(a.v.f < b.v.f);
}
static inline TalkValue talk_float_cmp_le(TalkValue a, TalkValue b) {
    return talk_bool(a.v.f <= b.v.f);
}
static inline TalkValue talk_float_cmp_gt(TalkValue a, TalkValue b) {
    return talk_bool(a.v.f > b.v.f);
}
static inline TalkValue talk_float_cmp_ge(TalkValue a, TalkValue b) {
    return talk_bool(a.v.f >= b.v.f);
}

static inline TalkValue talk_int_to_float(TalkValue a) { return talk_float((double)a.v.i); }

/* Rust's `as i64` saturates and maps NaN to zero, where C's cast would be
 * undefined outside the range. */
static inline TalkValue talk_float_to_int(TalkValue a) {
    double value = a.v.f;
    if (value != value) {
        return talk_int(0);
    }
    if (value >= 9223372036854775808.0) {
        return talk_int(INT64_MAX);
    }
    if (value <= -9223372036854775808.0) {
        return talk_int(INT64_MIN);
    }
    return talk_int((int64_t)value);
}

/* ---- byte operations ------------------------------------------------
 *
 * A Byte is held in the same payload word as an Int, normalized to
 * 0..=255, so the comparisons above serve both. Shifts mask the amount to
 * three bits, as `u8::wrapping_sh*` does.
 */

static inline TalkValue talk_byte(int64_t bits) {
    TalkValue value;
    value.tag = TALK_BYTE;
    value.v.i = bits & 0xFF;
    return value;
}

static inline TalkValue talk_byte_and(TalkValue a, TalkValue b) {
    return talk_byte(a.v.i & b.v.i);
}
static inline TalkValue talk_byte_or(TalkValue a, TalkValue b) {
    return talk_byte(a.v.i | b.v.i);
}
static inline TalkValue talk_byte_xor(TalkValue a, TalkValue b) {
    return talk_byte(a.v.i ^ b.v.i);
}
static inline TalkValue talk_byte_not(TalkValue a) { return talk_byte(~a.v.i); }

static inline TalkValue talk_byte_shl(TalkValue a, TalkValue b) {
    return talk_byte(a.v.i << ((uint64_t)b.v.i & 7u));
}

static inline TalkValue talk_byte_shr(TalkValue a, TalkValue b) {
    return talk_byte((a.v.i & 0xFF) >> ((uint64_t)b.v.i & 7u));
}

static inline TalkValue talk_byte_to_int(TalkValue a) { return talk_int(a.v.i & 0xFF); }

/* Narrowing traps outside the byte range rather than truncating, as the
 * VM's `itob` does. */
static inline TalkValue talk_int_to_byte(TalkValue a) {
    if (a.v.i < 0 || a.v.i > 255) {
        talk_trap("itob of a value outside 0..=255");
    }
    return talk_byte(a.v.i);
}

static inline TalkValue talk_cmp_eq(TalkValue a, TalkValue b) { return talk_bool(a.v.i == b.v.i); }
static inline TalkValue talk_cmp_ne(TalkValue a, TalkValue b) { return talk_bool(a.v.i != b.v.i); }
static inline TalkValue talk_cmp_lt(TalkValue a, TalkValue b) { return talk_bool(a.v.i < b.v.i); }
static inline TalkValue talk_cmp_le(TalkValue a, TalkValue b) { return talk_bool(a.v.i <= b.v.i); }
static inline TalkValue talk_cmp_gt(TalkValue a, TalkValue b) { return talk_bool(a.v.i > b.v.i); }
static inline TalkValue talk_cmp_ge(TalkValue a, TalkValue b) { return talk_bool(a.v.i >= b.v.i); }

/* The emitter appends the definition once every function id is known. */
static TalkValue talk_dispatch(uint32_t function, const TalkValue *env, const TalkValue *args);

/* ---- tasks (ADR 0058) ----------------------------------------------
 *
 * The structured executor's runtime half: `spawn` hands an `(A) -> T`
 * closure and its transferred argument to a persistent worker pool
 * under a fresh handle; `join` takes the output exactly once. The pool
 * holds at most `talk_task_width()` threads, fed from one FIFO; a
 * joiner that must wait HELPS instead — it dequeues and runs pending
 * tasks on its own thread — which balances uneven tasks and makes
 * nested scopes deadlock-free (a worker waiting on an inner scope's
 * join drains the queue it would otherwise starve). Every mutable
 * runtime area a task touches is `_Thread_local`, and a task installs
 * its own root handlers before any effectful code runs, so helping on
 * a thread with live frames below is sound: the task's nearest
 * handlers are its own.
 *
 * Without POSIX threads (and when thread creation fails) tasks run at
 * the spawn site; the ordering is unobservable to a correct program
 * because the `Send` boundary already excluded shared identity.
 *
 * The handle table is spawner-local: a handle never leaves the thread
 * that spawned it, which the structured stdlib scope guarantees. Task
 * records are individually allocated and freed at join.
 */

enum {
    TALK_TASK_QUEUED = 0,
    TALK_TASK_RUNNING = 1,
    TALK_TASK_READY = 2,
    TALK_TASK_JOINED = 3,
};

typedef struct {
    TalkValue arg;
    TalkValue worker;
    TalkValue output;
    int state;
} TalkTask;

static _Thread_local TalkTask **talk_tasks;
static _Thread_local size_t talk_task_count;
static _Thread_local size_t talk_task_capacity;

static int64_t talk_task_width(void) {
#if defined(TALK_HAS_POSIX_IO)
    long count = sysconf(_SC_NPROCESSORS_ONLN);
    return count > 0 ? (int64_t)count : 1;
#else
    return 1;
#endif
}

static void talk_task_run(TalkTask *task) {
    task->output =
        talk_dispatch(task->worker.v.agg->meta, task->worker.v.agg->fields, &task->arg);
}

#if defined(TALK_HAS_POSIX_IO)
static pthread_mutex_t talk_pool_lock = PTHREAD_MUTEX_INITIALIZER;
/* Signals queue growth to parked workers. */
static pthread_cond_t talk_pool_wake = PTHREAD_COND_INITIALIZER;
/* Signals any task completion to waiting joiners. */
static pthread_cond_t talk_pool_done = PTHREAD_COND_INITIALIZER;
static TalkTask **talk_pool_queue;
static size_t talk_pool_head;
static size_t talk_pool_len;
static size_t talk_pool_capacity;
static size_t talk_pool_threads;

/* Callers hold the pool lock. */
static TalkTask *talk_pool_dequeue(void) {
    if (talk_pool_len == 0) {
        return NULL;
    }
    TalkTask *task = talk_pool_queue[talk_pool_head];
    talk_pool_head = (talk_pool_head + 1) % talk_pool_capacity;
    talk_pool_len--;
    return task;
}

/* Run one task outside the lock; the caller holds it on entry and gets
 * it back on return. */
static void talk_pool_run_locked(TalkTask *task) {
    task->state = TALK_TASK_RUNNING;
    pthread_mutex_unlock(&talk_pool_lock);
    talk_task_run(task);
    pthread_mutex_lock(&talk_pool_lock);
    task->state = TALK_TASK_READY;
    pthread_cond_broadcast(&talk_pool_done);
}

static void *talk_pool_worker(void *unused) {
    (void)unused;
    char anchor;
    talk_stack_init((uintptr_t)&anchor);
    pthread_mutex_lock(&talk_pool_lock);
    for (;;) {
        TalkTask *task = talk_pool_dequeue();
        if (task == NULL) {
            pthread_cond_wait(&talk_pool_wake, &talk_pool_lock);
            continue;
        }
        talk_pool_run_locked(task);
    }
    return NULL; /* unreachable; satisfies -Werror=return-type */
}

/* Enqueue under the lock, growing the ring and the thread count up to
 * the pool width; returns 0 when no worker thread could be arranged
 * (the caller runs the task at the spawn site instead). */
static int talk_pool_submit(TalkTask *task) {
    pthread_mutex_lock(&talk_pool_lock);
    if (talk_pool_len == talk_pool_capacity) {
        size_t grown = talk_pool_capacity == 0 ? 16 : talk_pool_capacity * 2;
        TalkTask **queue = (TalkTask **)malloc(grown * sizeof(*queue));
        if (queue == NULL) {
            pthread_mutex_unlock(&talk_pool_lock);
            return 0;
        }
        for (size_t index = 0; index < talk_pool_len; index++) {
            queue[index] = talk_pool_queue[(talk_pool_head + index) % talk_pool_capacity];
        }
        free(talk_pool_queue);
        talk_pool_queue = queue;
        talk_pool_head = 0;
        talk_pool_capacity = grown;
    }
    talk_pool_queue[(talk_pool_head + talk_pool_len) % talk_pool_capacity] = task;
    talk_pool_len++;
    size_t width = (size_t)talk_task_width();
    if (talk_pool_threads < width && talk_pool_threads < talk_pool_len) {
        pthread_t thread;
        if (pthread_create(&thread, NULL, talk_pool_worker, NULL) == 0) {
            pthread_detach(thread);
            talk_pool_threads++;
        } else if (talk_pool_threads == 0) {
            /* No worker exists and none can start: undo and run inline. */
            talk_pool_len--;
            pthread_mutex_unlock(&talk_pool_lock);
            return 0;
        }
    }
    pthread_cond_signal(&talk_pool_wake);
    pthread_mutex_unlock(&talk_pool_lock);
    return 1;
}
#endif

static int64_t talk_task_spawn(TalkValue arg, TalkValue worker) {
    if (talk_task_count == talk_task_capacity) {
        size_t grown = talk_task_capacity == 0 ? 8 : talk_task_capacity * 2;
        TalkTask **tasks = (TalkTask **)realloc(talk_tasks, grown * sizeof(*tasks));
        if (tasks == NULL) {
            talk_trap("out of memory");
        }
        talk_tasks = tasks;
        talk_task_capacity = grown;
    }
    TalkTask *task = (TalkTask *)calloc(1, sizeof(TalkTask));
    if (task == NULL) {
        talk_trap("out of memory");
    }
    size_t handle = talk_task_count++;
    talk_tasks[handle] = task;
    task->arg = arg;
    task->worker = worker;
    task->state = TALK_TASK_QUEUED;
#if defined(TALK_HAS_POSIX_IO)
    if (talk_pool_submit(task)) {
        return (int64_t)handle;
    }
#endif
    /* No pool available: run at the spawn site. */
    talk_task_run(task);
    task->state = TALK_TASK_READY;
    return (int64_t)handle;
}

static TalkValue talk_task_join(TalkValue handle) {
    size_t index = (size_t)handle.v.i;
    if (handle.v.i < 0 || index >= talk_task_count || talk_tasks[index] == NULL) {
        talk_trap("task join on an invalid or already-joined handle");
    }
    TalkTask *task = talk_tasks[index];
    if (task->state == TALK_TASK_JOINED) {
        talk_trap("task join on an invalid or already-joined handle");
    }
#if defined(TALK_HAS_POSIX_IO)
    pthread_mutex_lock(&talk_pool_lock);
    for (;;) {
        if (task->state == TALK_TASK_READY) {
            break;
        }
        if (task->state == TALK_TASK_QUEUED) {
            /* Our task is still queued: pull work — possibly it — and
             * run it here rather than sleeping on a busy pool. */
            TalkTask *pulled = talk_pool_dequeue();
            if (pulled != NULL) {
                talk_pool_run_locked(pulled);
                continue;
            }
        }
        /* RUNNING elsewhere, or QUEUED with an inconsistent ring (not
         * possible): wait for a completion and re-check. */
        pthread_cond_wait(&talk_pool_done, &talk_pool_lock);
    }
    pthread_mutex_unlock(&talk_pool_lock);
#endif
    if (task->state != TALK_TASK_READY) {
        talk_trap("task join before its worker completed");
    }
    task->state = TALK_TASK_JOINED;
    TalkValue output = task->output;
    free(task);
    talk_tasks[index] = NULL;
    return output;
}

/* ---- channels (ADR 0059) -------------------------------------------
 *
 * Cross-worker transfer queues behind runtime-minted handles. One
 * synchronization point serves everything: the pool lock guards the
 * registry, and the pool's completion condition doubles as the wake
 * signal — a send or a close broadcasts it, and a parked receiver's
 * executor re-drains. Parking HELPS first (runs queued pool tasks on
 * this thread), so parked consumers cannot starve the producers they
 * wait on. Ops through `talk_chan_ctl`: 0 status (0 ready, 1 empty
 * and open, 2 closed and drained), 1 retain sender, 2 drop sender,
 * 3 drop receiver, 4 register external wait, 5 unregister, 6 park,
 * 7 create.
 */

typedef struct {
    TalkValue *queue;
    size_t head;
    size_t len;
    size_t capacity;
    /* 0 = unbounded; otherwise len + reserved never exceeds it. The
     * queue's malloc'd capacity above grows independently. */
    size_t bound;
    /* Send slots claimed by an in-flight SendFuture poll (ADR 0062).
     * Reserve and send happen inside one poll body, so a reservation
     * never outlives a poll -- but racing reservers must see each
     * other's claims, which is what makes the bound hard. */
    size_t reserved;
    uint32_t senders;
    int receiver_live;
    int live;
} TalkChannel;

static TalkChannel *talk_channels;
static size_t talk_channel_count;
static size_t talk_channel_capacity;
/* Channel handles this thread holds a live external-wait registration
 * on (pending receives per ADR 0059, pending bounded sends per
 * ADR 0062 -- talk_external_sends marks the direction). A park may
 * sleep only after confirming, under the pool lock, that no
 * registration is already satisfiable -- the wake may have raced the
 * caller's status poll, and its broadcast must not be lost. A
 * receive-wait is satisfied by a value or a close; a send-wait by room
 * or receiver death. */
static _Thread_local int64_t *talk_external_handles;
static _Thread_local unsigned char *talk_external_sends;
static _Thread_local size_t talk_external_waits;
static _Thread_local size_t talk_external_capacity;
/* Absolute monotonic-ms deadlines this thread's sleeping futures
 * registered (ADR 0063): each is a reason to park, and the park waits
 * only until the earliest of them. */
static _Thread_local int64_t *talk_deadlines;
static _Thread_local size_t talk_deadline_count;
static _Thread_local size_t talk_deadline_capacity;

/* Monotonic milliseconds from an arbitrary per-process anchor
 * (ADR 0063). Wall-clock time is host-effect territory; deadlines only
 * care about deltas. */
static int64_t talk_now_ms(void) {
#if defined(TALK_HAS_POSIX_IO)
    struct timespec now;
    clock_gettime(CLOCK_MONOTONIC, &now);
    return (int64_t)now.tv_sec * 1000 + now.tv_nsec / 1000000;
#else
    talk_trap("monotonic clock unavailable on this host");
    return 0;
#endif
}

static void talk_chan_lock(void) {
#if defined(TALK_HAS_POSIX_IO)
    pthread_mutex_lock(&talk_pool_lock);
#endif
}

static void talk_chan_unlock(void) {
#if defined(TALK_HAS_POSIX_IO)
    pthread_mutex_unlock(&talk_pool_lock);
#endif
}

/* Callers hold the lock. */
static TalkChannel *talk_chan(int64_t handle) {
    size_t index = (size_t)handle;
    if (handle < 0 || index >= talk_channel_count || !talk_channels[index].live) {
        talk_trap("channel operation on an invalid handle");
    }
    return &talk_channels[index];
}

static void talk_chan_send(TalkValue handle, TalkValue value) {
    talk_chan_lock();
    TalkChannel *channel = talk_chan(handle.v.i);
    if (channel->len == channel->capacity) {
        size_t grown = channel->capacity == 0 ? 8 : channel->capacity * 2;
        TalkValue *queue = (TalkValue *)malloc(grown * sizeof(*queue));
        if (queue == NULL) {
            talk_trap("out of memory");
        }
        for (size_t index = 0; index < channel->len; index++) {
            queue[index] = channel->queue[(channel->head + index) % channel->capacity];
        }
        free(channel->queue);
        channel->queue = queue;
        channel->head = 0;
        channel->capacity = grown;
    }
    channel->queue[(channel->head + channel->len) % channel->capacity] = value;
    channel->len++;
    /* A bounded send consumes the reservation its poll claimed. */
    if (channel->reserved > 0) {
        channel->reserved--;
    }
    talk_chan_unlock();
#if defined(TALK_HAS_POSIX_IO)
    pthread_cond_broadcast(&talk_pool_done);
#endif
}

static TalkValue talk_chan_take(TalkValue handle) {
    talk_chan_lock();
    TalkChannel *channel = talk_chan(handle.v.i);
    if (channel->len == 0) {
        talk_trap("take on an empty channel");
    }
    TalkValue value = channel->queue[channel->head];
    channel->head = (channel->head + 1) % channel->capacity;
    channel->len--;
    talk_chan_unlock();
#if defined(TALK_HAS_POSIX_IO)
    /* Room opened: parked bounded senders must observe it. */
    pthread_cond_broadcast(&talk_pool_done);
#endif
    return value;
}

static int64_t talk_chan_ctl(TalkValue handle, TalkValue op) {
    switch (op.v.i) {
    case 0: {
        talk_chan_lock();
        TalkChannel *channel = talk_chan(handle.v.i);
        int64_t status = channel->len > 0 ? 0 : (channel->senders == 0 ? 2 : 1);
        talk_chan_unlock();
        return status;
    }
    case 1:
    case 2:
    case 3: {
        talk_chan_lock();
        TalkChannel *channel = talk_chan(handle.v.i);
        int closed = 0;
        if (op.v.i == 1) {
            channel->senders++;
        } else if (op.v.i == 2) {
            if (channel->senders > 0) {
                channel->senders--;
            }
            closed = channel->senders == 0;
        } else {
            channel->receiver_live = 0;
        }
        if (channel->senders == 0 && !channel->receiver_live) {
            free(channel->queue);
            channel->queue = NULL;
            channel->live = 0;
        }
        talk_chan_unlock();
#if defined(TALK_HAS_POSIX_IO)
        if (closed) {
            pthread_cond_broadcast(&talk_pool_done);
        }
#endif
        return 0;
    }
    case 4:
    case 11:
        if (talk_external_waits == talk_external_capacity) {
            size_t grown = talk_external_capacity == 0 ? 4 : talk_external_capacity * 2;
            int64_t *handles =
                (int64_t *)realloc(talk_external_handles, grown * sizeof(*handles));
            unsigned char *sends =
                (unsigned char *)realloc(talk_external_sends, grown * sizeof(*sends));
            if (handles == NULL || sends == NULL) {
                talk_trap("out of memory");
            }
            talk_external_handles = handles;
            talk_external_sends = sends;
            talk_external_capacity = grown;
        }
        talk_external_sends[talk_external_waits] = op.v.i == 11;
        talk_external_handles[talk_external_waits++] = handle.v.i;
        return 0;
    case 8:
        return (int64_t)(talk_external_waits + talk_deadline_count);
    case 13:
        return talk_now_ms();
    case 14:
        if (talk_deadline_count == talk_deadline_capacity) {
            size_t grown = talk_deadline_capacity == 0 ? 4 : talk_deadline_capacity * 2;
            int64_t *deadlines =
                (int64_t *)realloc(talk_deadlines, grown * sizeof(*deadlines));
            if (deadlines == NULL) {
                talk_trap("out of memory");
            }
            talk_deadlines = deadlines;
            talk_deadline_capacity = grown;
        }
        talk_deadlines[talk_deadline_count++] = handle.v.i;
        return 0;
    case 15:
        for (size_t scan = 0; scan < talk_deadline_count; scan++) {
            if (talk_deadlines[scan] == handle.v.i) {
                talk_deadlines[scan] = talk_deadlines[--talk_deadline_count];
                break;
            }
        }
        return 0;
    case 9: {
        talk_chan_lock();
        TalkChannel *channel = talk_chan(handle.v.i);
        int64_t live = channel->receiver_live;
        talk_chan_unlock();
        return live;
    }
    case 10: {
        talk_chan_lock();
        TalkChannel *channel = talk_chan(handle.v.i);
        int64_t granted = 1;
        if (channel->bound > 0) {
            if (channel->len + channel->reserved < channel->bound) {
                channel->reserved++;
            } else {
                granted = 0;
            }
        }
        talk_chan_unlock();
        return granted;
    }
    case 17: {
        /* Non-reserving room probe (ADR 0067). */
        talk_chan_lock();
        TalkChannel *channel = talk_chan(handle.v.i);
        int64_t ready = !channel->receiver_live || channel->bound == 0
            || channel->len + channel->reserved < channel->bound;
        talk_chan_unlock();
        return ready;
    }
    case 5:
    case 12:
        for (size_t scan = 0; scan < talk_external_waits; scan++) {
            if (talk_external_handles[scan] == handle.v.i &&
                talk_external_sends[scan] == (op.v.i == 12)) {
                talk_external_waits--;
                talk_external_handles[scan] = talk_external_handles[talk_external_waits];
                talk_external_sends[scan] = talk_external_sends[talk_external_waits];
                break;
            }
        }
        return 0;
    case 6: {
        if (talk_external_waits == 0 && talk_deadline_count == 0) {
            return 0;
        }
#if defined(TALK_HAS_POSIX_IO)
        pthread_mutex_lock(&talk_pool_lock);
        int ready = 0;
        for (size_t scan = 0; scan < talk_external_waits; scan++) {
            int64_t entry = talk_external_handles[scan];
            size_t index = (size_t)entry;
            if (entry < 0 || index >= talk_channel_count ||
                !talk_channels[index].live) {
                ready = 1;
                break;
            }
            TalkChannel *waited = &talk_channels[index];
            if (talk_external_sends[scan]
                    ? (!waited->receiver_live ||
                       waited->len + waited->reserved < waited->bound)
                    : (waited->len > 0 || waited->senders == 0)) {
                ready = 1;
                break;
            }
        }
        int64_t earliest = 0;
        int deadline_set = 0;
        for (size_t scan = 0; scan < talk_deadline_count; scan++) {
            if (!deadline_set || talk_deadlines[scan] < earliest) {
                earliest = talk_deadlines[scan];
                deadline_set = 1;
            }
        }
        if (deadline_set && talk_now_ms() >= earliest) {
            /* The earliest deadline already passed: the timed wake. */
            ready = 1;
        }
        if (!ready) {
            /* No helping here, unlike a join: a helped task that parks
             * cannot return control to this frame, and an outer ready
             * registration then turns its inner park into a hot spin
             * (the 27GB arena balloon). Queued tasks belong to the pool
             * workers; a park just sleeps. */
            if (deadline_set) {
                /* A registered deadline bounds the sleep: wake at the
                 * earliest of it and any broadcast. */
                int64_t wait = earliest - talk_now_ms();
                if (wait > 0) {
                    struct timespec until;
                    clock_gettime(CLOCK_REALTIME, &until);
                    until.tv_sec += wait / 1000;
                    until.tv_nsec += (long)(wait % 1000) * 1000000;
                    if (until.tv_nsec >= 1000000000L) {
                        until.tv_sec += 1;
                        until.tv_nsec -= 1000000000L;
                    }
                    pthread_cond_timedwait(&talk_pool_done, &talk_pool_lock, &until);
                }
            } else {
                pthread_cond_wait(&talk_pool_done, &talk_pool_lock);
            }
        }
        pthread_mutex_unlock(&talk_pool_lock);
        return 0;
#else
        talk_trap("parked with no thread able to wake this task (deadlock)");
#endif
    }
    case 7: {
        talk_chan_lock();
        size_t index = talk_channel_count;
        for (size_t scan = 0; scan < talk_channel_count; scan++) {
            if (!talk_channels[scan].live) {
                index = scan;
                break;
            }
        }
        if (index == talk_channel_count) {
            if (talk_channel_count == talk_channel_capacity) {
                size_t grown = talk_channel_capacity == 0 ? 8 : talk_channel_capacity * 2;
                TalkChannel *channels =
                    (TalkChannel *)realloc(talk_channels, grown * sizeof(*channels));
                if (channels == NULL) {
                    talk_trap("out of memory");
                }
                talk_channels = channels;
                talk_channel_capacity = grown;
            }
            talk_channel_count++;
        }
        TalkChannel *channel = &talk_channels[index];
        channel->queue = NULL;
        channel->head = 0;
        channel->len = 0;
        channel->capacity = 0;
        channel->bound = handle.v.i > 0 ? (size_t)handle.v.i : 0;
        channel->reserved = 0;
        channel->senders = 1;
        channel->receiver_live = 1;
        channel->live = 1;
        talk_chan_unlock();
        return (int64_t)index;
    }
    default:
        talk_trap("unknown channel control operation");
    }
}

/* ---- heap objects and regions ---------------------------------------
 *
 * A `'heap` struct belongs to a region; linking objects merges their
 * regions, and a region dies when its external owner count reaches zero,
 * finalizing its members in reverse allocation order and then freeing
 * them as a unit (ADR 0044; Gay & Aiken, PLDI 2001).
 *
 * The VM names objects by index into an arena so a stale handle can be
 * rejected. Generated C uses machine pointers, consistent with buffers:
 * a use-after-teardown is undefined here rather than a clean trap. What
 * makes that safe in practice is the ordering the VM already relies on --
 * a region is marked `finalizing` the moment its count hits zero, before
 * the walk frees anything -- so a value holding two handles into the same
 * region takes the `finalizing` skip on the second, not freed memory.
 */

typedef struct TalkRegion TalkRegion;
typedef struct TalkObject TalkObject;

struct TalkRegion {
    /* Union-find parent; self for roots. */
    TalkRegion *parent;
    /* Live bindings referencing into this region (root-only). Internal
     * edges, including cycles, never touch it. */
    uint32_t owner_count;
    int finalizing;
    TalkObject **members;
    size_t member_count;
    size_t member_capacity;
    /* Roots absorbed by `union`, so teardown reclaims the whole tree. */
    TalkRegion **merged;
    size_t merged_count;
    size_t merged_capacity;
#if defined(TALK_LIBRARY)
    TalkRegion *lib_prev;
    TalkRegion *lib_next;
#endif
};

struct TalkObject {
    TalkRegion *region;
    /* Allocation order, for the reverse-order finalizer walk. */
    uint64_t ordinal;
    /* `TALK_UNIT` when the object has no `Deinit` hook. */
    TalkValue finalizer;
    int finalized;
    uint32_t field_count;
#if defined(TALK_LIBRARY)
    TalkObject *lib_prev;
    TalkObject *lib_next;
#endif
    TalkValue fields[];
};

/* Process-wide accounting is atomic so workers may allocate objects
 * concurrently. Region INTERNALS (owner counts, member lists, union-find
 * links) stay unsynchronized: a `'heap` value is neither Send nor Sync
 * under ADR 0050's structural rules, so a region is confined to the
 * worker that created it and the pending-finalizer walk below is
 * worker-local state. */
static _Atomic uint64_t talk_next_ordinal;
static _Atomic size_t talk_live_objects;
/* Regions whose count reached zero and whose walk has not finished. */
static _Thread_local TalkRegion **talk_pending;
static _Thread_local size_t talk_pending_count;
static _Thread_local size_t talk_pending_capacity;
/* Only the outermost release drains: a deinit body may release the last
 * handle of another region, and that walk nests behind this one. */
static _Thread_local int talk_draining;

static void *talk_grow(void *items, size_t *capacity, size_t needed, size_t size) {
    if (needed <= *capacity) {
        return items;
    }
    size_t grown = *capacity == 0 ? 4 : *capacity * 2;
    while (grown < needed) {
        grown *= 2;
    }
    void *resized = realloc(items, grown * size);
    if (resized == NULL) {
        talk_trap("out of memory");
    }
    *capacity = grown;
    return resized;
}

static TalkRegion *talk_find(TalkRegion *region) {
    TalkRegion *root = region;
    while (root->parent != root) {
        root = root->parent;
    }
    /* Path compression. */
    while (region->parent != root) {
        TalkRegion *next = region->parent;
        region->parent = root;
        region = next;
    }
    return root;
}

static void talk_region_push_member(TalkRegion *region, TalkObject *object) {
    region->members = (TalkObject **)talk_grow(region->members, &region->member_capacity,
                                               region->member_count + 1, sizeof(TalkObject *));
    region->members[region->member_count++] = object;
}

/* Merge two roots: counts sum, members merge small-to-large, and the
 * absorbed root is recorded so teardown frees the whole tree. */
static void talk_union(TalkRegion *a, TalkRegion *b) {
    a = talk_find(a);
    b = talk_find(b);
    if (a == b) {
        return;
    }
    TalkRegion *small = a->member_count < b->member_count ? a : b;
    TalkRegion *large = small == a ? b : a;
    small->parent = large;
    for (size_t index = 0; index < small->member_count; index++) {
        talk_region_push_member(large, small->members[index]);
    }
    free(small->members);
    small->members = NULL;
    small->member_count = 0;
    small->member_capacity = 0;
    large->owner_count += small->owner_count;
    small->owner_count = 0;
    large->merged = (TalkRegion **)talk_grow(large->merged, &large->merged_capacity,
                                             large->merged_count + small->merged_count + 1,
                                             sizeof(TalkRegion *));
    large->merged[large->merged_count++] = small;
    for (size_t index = 0; index < small->merged_count; index++) {
        large->merged[large->merged_count++] = small->merged[index];
    }
    free(small->merged);
    small->merged = NULL;
    small->merged_count = 0;
    small->merged_capacity = 0;
}

static TalkValue talk_object_new(uint32_t field_count) {
    TalkObject *object =
        (TalkObject *)calloc(1, sizeof(TalkObject) + (size_t)field_count * sizeof(TalkValue));
    TalkRegion *region = (TalkRegion *)calloc(1, sizeof(TalkRegion));
    if (object == NULL || region == NULL) {
        talk_trap("out of memory");
    }
    region->parent = region;
    /* The +1 belongs to whatever binding receives the rvalue. */
    region->owner_count = 1;
#if defined(TALK_LIBRARY)
    object->lib_next = talk_lib_objects;
    if (talk_lib_objects != NULL) {
        talk_lib_objects->lib_prev = object;
    }
    talk_lib_objects = object;
    region->lib_next = talk_lib_regions;
    if (talk_lib_regions != NULL) {
        talk_lib_regions->lib_prev = region;
    }
    talk_lib_regions = region;
#endif
    object->region = region;
    object->ordinal = atomic_fetch_add_explicit(&talk_next_ordinal, 1u, memory_order_relaxed);
    object->finalizer = talk_unit();
    object->field_count = field_count;
    talk_region_push_member(region, object);
    atomic_fetch_add_explicit(&talk_live_objects, 1u, memory_order_relaxed);
    TalkValue value;
    value.tag = TALK_OBJECT;
    value.v.obj = object;
    return value;
}

/* Every object handle reachable in a value. Cells and continuations hold
 * no reachable handles, matching the VM's scan. */
static void talk_scan_handles(TalkValue value, TalkObject ***out, size_t *count,
                              size_t *capacity) {
    switch (value.tag) {
    case TALK_OBJECT:
        *out = (TalkObject **)talk_grow(*out, capacity, *count + 1, sizeof(TalkObject *));
        (*out)[(*count)++] = value.v.obj;
        return;
    case TALK_AGG:
    case TALK_CLOSURE:
        for (uint32_t index = 0; index < value.v.agg->len; index++) {
            talk_scan_handles(value.v.agg->fields[index], out, count, capacity);
        }
        return;
    case TALK_NATIVE:
        talk_native_scan(value, out, count, capacity);
        return;
    default:
        return;
    }
}

#if defined(TALK_LIBRARY)
static void talk_lib_unlink_object(TalkObject *object) {
    if (object->lib_prev != NULL) {
        object->lib_prev->lib_next = object->lib_next;
    } else {
        talk_lib_objects = object->lib_next;
    }
    if (object->lib_next != NULL) {
        object->lib_next->lib_prev = object->lib_prev;
    }
}

static void talk_lib_unlink_region(TalkRegion *region) {
    if (region->lib_prev != NULL) {
        region->lib_prev->lib_next = region->lib_next;
    } else {
        talk_lib_regions = region->lib_next;
    }
    if (region->lib_next != NULL) {
        region->lib_next->lib_prev = region->lib_prev;
    }
}
#endif

static void talk_region_free(TalkRegion *root) {
    for (size_t index = 0; index < root->member_count; index++) {
#if defined(TALK_LIBRARY)
        talk_lib_unlink_object(root->members[index]);
#endif
        free(root->members[index]);
        atomic_fetch_sub_explicit(&talk_live_objects, 1u, memory_order_relaxed);
    }
    free(root->members);
    for (size_t index = 0; index < root->merged_count; index++) {
#if defined(TALK_LIBRARY)
        talk_lib_unlink_region(root->merged[index]);
#endif
        free(root->merged[index]);
    }
    free(root->merged);
#if defined(TALK_LIBRARY)
    talk_lib_unlink_region(root);
#endif
    free(root);
}

/* Run pending finalizer walks to completion: innermost region first,
 * highest ordinal first within a region, then bulk-free. */
static void talk_drain_finalizers(void) {
    if (talk_draining) {
        return;
    }
    talk_draining = 1;
    while (talk_pending_count > 0) {
        TalkRegion *root = talk_pending[talk_pending_count - 1];
        TalkObject *next = NULL;
        for (size_t index = 0; index < root->member_count; index++) {
            TalkObject *member = root->members[index];
            if (!member->finalized && member->finalizer.tag == TALK_CLOSURE
                && (next == NULL || member->ordinal > next->ordinal)) {
                next = member;
            }
        }
        if (next != NULL) {
            next->finalized = 1;
            TalkValue handle;
            handle.tag = TALK_OBJECT;
            handle.v.obj = next;
            TalkValue thunk = next->finalizer;
            talk_dispatch(thunk.v.agg->meta, thunk.v.agg->fields, &handle);
            continue;
        }
        talk_pending_count--;
        talk_region_free(root);
    }
    talk_draining = 0;
}

static void talk_region_acquire(TalkValue value) {
    TalkObject **handles = NULL;
    size_t count = 0, capacity = 0;
    talk_scan_handles(value, &handles, &count, &capacity);
    for (size_t index = 0; index < count; index++) {
        TalkRegion *root = talk_find(handles[index]->region);
        /* A deinit body may bind locals aliasing the dying region;
         * teardown proceeds regardless. */
        if (root->finalizing) {
            continue;
        }
        root->owner_count++;
    }
    free(handles);
}

static void talk_region_release(TalkValue value) {
    TalkObject **handles = NULL;
    size_t count = 0, capacity = 0;
    talk_scan_handles(value, &handles, &count, &capacity);
    for (size_t index = 0; index < count; index++) {
        TalkRegion *root = talk_find(handles[index]->region);
        if (root->finalizing) {
            continue;
        }
        if (root->owner_count == 0) {
            talk_trap("region released more times than acquired");
        }
        if (--root->owner_count > 0) {
            continue;
        }
        /* Marked before anything is freed, so a second handle into this
         * region takes the skip above rather than touching dead storage. */
        root->finalizing = 1;
        talk_pending = (TalkRegion **)talk_grow(talk_pending, &talk_pending_capacity,
                                                talk_pending_count + 1, sizeof(TalkRegion *));
        talk_pending[talk_pending_count++] = root;
    }
    free(handles);
    talk_drain_finalizers();
}

static void talk_object_set(TalkValue object, uint32_t index, TalkValue field) {
    TalkObject **handles = NULL;
    size_t count = 0, capacity = 0;
    talk_scan_handles(field, &handles, &count, &capacity);
    TalkRegion *target = talk_find(object.v.obj->region);
    if (count > 0 && target->finalizing) {
        talk_trap("cannot store an object during region teardown");
    }
    for (size_t at = 0; at < count; at++) {
        TalkRegion *root = talk_find(handles[at]->region);
        if (root->finalizing) {
            talk_trap("cannot store an object during region teardown");
        }
        talk_union(target, root);
    }
    free(handles);
    object.v.obj->fields[index] = field;
}

#if defined(TALK_LIBRARY)
/* Complete invocation cleanup (ADR 0048): every arena chunk, refcounted
 * allocation, object, and region returns to the host allocator, and
 * every mutable runtime global returns to its boot value, so a fresh
 * `init` behaves like a fresh process. Finalizers do not run -- no Talk
 * code may execute outside an invocation. */
static void talk_lib_reset(void) {
    talk_arena_release();
    talk_effects_release();
    while (talk_lib_allocations != NULL) {
        TalkHeader *header = talk_lib_allocations;
        talk_lib_allocations = header->lib_next;
        free(header);
    }
    while (talk_lib_objects != NULL) {
        TalkObject *object = talk_lib_objects;
        talk_lib_objects = object->lib_next;
        free(object);
    }
    while (talk_lib_regions != NULL) {
        TalkRegion *region = talk_lib_regions;
        talk_lib_regions = region->lib_next;
        free(region->members);
        free(region->merged);
        free(region);
    }
    free(talk_pending);
    talk_pending = NULL;
    talk_pending_count = 0;
    talk_pending_capacity = 0;
    talk_draining = 0;
    talk_live_allocations = 0;
    talk_live_objects = 0;
    talk_next_ordinal = 0;
    talk_next_frame_id = 1;
    talk_unwinding = 0;
    talk_unwind_depth = 0;
    talk_unwind_frame = 0;
    talk_unwind_value = talk_unit();
    talk_handler_floor = SIZE_MAX;
    talk_lib_boundary_armed = 0;
}
#endif

/* ---- host IO --------------------------------------------------------
 *
 * `op` indexes the runtime's operation table in core `IORequest`
 * declaration order. Core's `_io_host` compiles a dispatch over the whole
 * enum, so every one of these indices is emitted into every program that
 * prints -- but only a few are ever reached. The unimplemented ones
 * therefore trap at run time rather than rejecting the program at compile
 * time: the table is statically present and dynamically unreachable, and a
 * program that genuinely opens a socket should fail loudly rather than
 * silently do something else.
 */


enum {
    TALK_IO_READ = 0,
    TALK_IO_WRITE = 1,
    TALK_IO_OPEN = 2,
    TALK_IO_CLOSE = 3,
    TALK_IO_SLEEP = 4,
    TALK_IO_POLL = 5,
    TALK_IO_CTL = 6,
    TALK_IO_SOCKET = 7,
    TALK_IO_BIND = 8,
    TALK_IO_LISTEN = 9,
    TALK_IO_CONNECT = 10,
    TALK_IO_ACCEPT = 11,
    TALK_IO_CWD_LEN = 12,
    TALK_IO_CWD_COPY = 13,
    TALK_IO_GETENV_LEN = 14,
    TALK_IO_GETENV_COPY = 15,
    TALK_IO_ARGC = 16,
    TALK_IO_ARG_LEN = 17,
    TALK_IO_ARG_COPY = 18,
    TALK_IO_DIR_COUNT = 19,
    TALK_IO_DIR_ENTRY_KIND = 20,
    TALK_IO_DIR_ENTRY_LEN = 21,
    TALK_IO_DIR_ENTRY_COPY = 22,
    TALK_IO_EXIT = 23,
    TALK_IO_REALPATH_LEN = 24,
    TALK_IO_REALPATH_COPY = 25,
    TALK_IO_SEEK = 26,
    TALK_IO_FILE_SIZE = 27
};

/* Negated errno, as every operation returns (core/IO.tlk's constants). */
#define TALK_EIO (-5)
#define TALK_ENOENT (-2)
#define TALK_EINVAL (-22)
#define TALK_EPERM (-1)
#define TALK_DIR_DIRECTORY 1
#define TALK_DIR_FILE 2
#define TALK_DIR_SYMLINK 3

/* The process arguments, captured by the generated `main`. */
static int talk_argc;
static char **talk_argv;

#ifdef TALK_HAS_POSIX_IO
static int64_t talk_errno(void) { return -(int64_t)errno; }

/* Copy `bytes` into a caller buffer that must be large enough, returning
 * the length -- the shape every `*_copy` operation shares. */
static int64_t talk_copy_out(unsigned char *destination, const char *bytes, size_t available) {
    size_t length = strlen(bytes);
    if (available < length) {
        return TALK_EINVAL;
    }
    memcpy(destination, bytes, length);
    return (int64_t)length;
}

static int talk_name_order(const void *a, const void *b) {
    return strcmp(*(const char *const *)a, *(const char *const *)b);
}

/* Directory entries, sorted by name and excluding `.` and `..`, matching
 * `read_dir` plus the runtime's sort. Read fresh per call, as the VM
 * does. Caller frees with `talk_free_entries`. */
static int talk_read_entries(const char *path, char ***out, size_t *count) {
    DIR *directory = opendir(path);
    *count = 0;
    *out = NULL;
    if (directory == NULL) {
        /* Distinguished from an empty directory, which succeeds with no
         * entries and must not be reported as this errno. */
        return -1;
    }
    char **names = NULL;
    size_t capacity = 0;
    struct dirent *entry;
    while ((entry = readdir(directory)) != NULL) {
        if (strcmp(entry->d_name, ".") == 0 || strcmp(entry->d_name, "..") == 0) {
            continue;
        }
        if (*count == capacity) {
            capacity = capacity == 0 ? 16 : capacity * 2;
            char **grown = (char **)realloc(names, capacity * sizeof(*grown));
            if (grown == NULL) {
                break;
            }
            names = grown;
        }
        char *copy = (char *)malloc(strlen(entry->d_name) + 1);
        if (copy == NULL) {
            break;
        }
        strcpy(copy, entry->d_name);
        names[(*count)++] = copy;
    }
    closedir(directory);
    if (names != NULL) {
        qsort(names, *count, sizeof(*names), talk_name_order);
    }
    *out = names;
    return 0;
}

static void talk_free_entries(char **names, size_t count) {
    for (size_t index = 0; index < count; index++) {
        free(names[index]);
    }
    free(names);
}

/* Symlink first, then directory, then file -- the runtime's order, and
 * the reason this uses `lstat` rather than `stat`. */
static int64_t talk_entry_kind(const char *path, const char *name) {
    size_t length = strlen(path) + strlen(name) + 2;
    char *joined = (char *)malloc(length);
    if (joined == NULL) {
        return TALK_EIO;
    }
    snprintf(joined, length, "%s/%s", path, name);
    struct stat info;
    int failed = lstat(joined, &info);
    free(joined);
    if (failed != 0) {
        return talk_errno();
    }
    if (S_ISLNK(info.st_mode)) {
        return TALK_DIR_SYMLINK;
    }
    return S_ISDIR(info.st_mode) ? TALK_DIR_DIRECTORY : TALK_DIR_FILE;
}
#endif

static int64_t talk_io(uint8_t op, TalkValue a, TalkValue b, TalkValue c) {
#ifndef TALK_HAS_POSIX_IO
    /* Only stdio is portable; everything else needs the host. */
    if (op != TALK_IO_WRITE && op != TALK_IO_EXIT) {
        return TALK_EPERM;
    }
#endif
    switch (op) {
    case TALK_IO_WRITE: {
        int64_t fd = a.v.i;
        int64_t count = c.v.i;
        /* A negative count passes through untouched: callers feed a failed
         * read's errno straight into the next write. */
        if (count < 0) {
            return count;
        }
        size_t len = (size_t)count;
        if (fd == 1 || fd == 2) {
            FILE *stream = fd == 1 ? stdout : stderr;
            if (len > 0 && fwrite(b.v.ptr, 1, len, stream) != len) {
                return TALK_EIO;
            }
            /* stdout is flushed per write, as the runtime's is. */
            if (fd == 1 && fflush(stdout) != 0) {
                return TALK_EIO;
            }
            return count;
        }
#ifdef TALK_HAS_POSIX_IO
        {
            ssize_t written = write((int)fd, b.v.ptr, len);
            return written < 0 ? talk_errno() : (int64_t)written;
        }
#else
        return TALK_EIO;
#endif
    }
    case TALK_IO_EXIT:
#if defined(TALK_LIBRARY)
        if (talk_lib_boundary_armed) {
            talk_lib_exit_status = (int)a.v.i;
            snprintf(talk_lib_message, sizeof talk_lib_message,
                     "the program requested exit with status %d", (int)a.v.i);
            talk_lib_boundary_armed = 0;
            longjmp(talk_lib_boundary, 2);
        }
#endif
        talk_arena_release();
        talk_effects_release();
        exit((int)a.v.i);
#ifdef TALK_HAS_POSIX_IO
    case TALK_IO_READ: {
        int64_t count = c.v.i;
        if (count < 0) {
            return count;
        }
        ssize_t got = read((int)a.v.i, b.v.ptr, (size_t)count);
        return got < 0 ? talk_errno() : (int64_t)got;
    }
    case TALK_IO_OPEN: {
        /* The path is already NUL-terminated in managed bytes. */
        int fd = open((const char *)a.v.ptr, (int)b.v.i, (unsigned)c.v.i);
        return fd < 0 ? talk_errno() : (int64_t)fd;
    }
    case TALK_IO_CLOSE:
        return close((int)a.v.i) < 0 ? talk_errno() : 0;
    case TALK_IO_SLEEP: {
        int64_t milliseconds = a.v.i;
        if (milliseconds > 0) {
            struct timespec requested;
            requested.tv_sec = (time_t)(milliseconds / 1000);
            requested.tv_nsec = (long)(milliseconds % 1000) * 1000000L;
            nanosleep(&requested, NULL);
        }
        return 0;
    }
    case TALK_IO_POLL: {
        /* Records are 8 bytes: i32 fd, i16 events, i16 revents. Only
         * `revents` is written back. */
        int64_t count = b.v.i;
        if (count < 0) {
            return TALK_EINVAL;
        }
        struct pollfd *fds = (struct pollfd *)calloc((size_t)count + 1, sizeof(*fds));
        if (fds == NULL) {
            return TALK_EIO;
        }
        for (int64_t index = 0; index < count; index++) {
            const unsigned char *record = b.v.ptr == NULL ? NULL : a.v.ptr + index * 8;
            int32_t fd;
            int16_t events;
            memcpy(&fd, record, sizeof fd);
            memcpy(&events, record + 4, sizeof events);
            fds[index].fd = fd;
            fds[index].events = events;
        }
        int ready = poll(fds, (nfds_t)count, (int)c.v.i);
        for (int64_t index = 0; index < count; index++) {
            int16_t revents = (int16_t)fds[index].revents;
            memcpy(a.v.ptr + index * 8 + 6, &revents, sizeof revents);
        }
        free(fds);
        return ready < 0 ? talk_errno() : (int64_t)ready;
    }
    case TALK_IO_CTL: {
        int result = ioctl((int)a.v.i, (unsigned long)b.v.i, c.v.i);
        return result < 0 ? talk_errno() : (int64_t)result;
    }
    case TALK_IO_SOCKET: {
        int fd = socket((int)a.v.i, (int)b.v.i, (int)c.v.i);
        return fd < 0 ? talk_errno() : (int64_t)fd;
    }
    case TALK_IO_BIND: {
        /* SO_REUSEADDR first: restarting a server must not wait out
         * TIME_WAIT, as the runtime's bind does. */
        int enable = 1;
        setsockopt((int)a.v.i, SOL_SOCKET, SO_REUSEADDR, &enable, sizeof enable);
        struct sockaddr_in address;
        memset(&address, 0, sizeof address);
        address.sin_family = AF_INET;
        address.sin_addr.s_addr = htonl((uint32_t)b.v.i);
        address.sin_port = htons((uint16_t)c.v.i);
        int failed = bind((int)a.v.i, (const struct sockaddr *)&address, sizeof address);
        return failed < 0 ? talk_errno() : 0;
    }
    case TALK_IO_LISTEN:
        return listen((int)a.v.i, (int)b.v.i) < 0 ? talk_errno() : 0;
    case TALK_IO_CONNECT: {
        struct sockaddr_in address;
        memset(&address, 0, sizeof address);
        address.sin_family = AF_INET;
        address.sin_addr.s_addr = htonl((uint32_t)b.v.i);
        address.sin_port = htons((uint16_t)c.v.i);
        int failed = connect((int)a.v.i, (const struct sockaddr *)&address, sizeof address);
        return failed < 0 ? talk_errno() : 0;
    }
    case TALK_IO_ACCEPT: {
        int fd = accept((int)a.v.i, NULL, NULL);
        return fd < 0 ? talk_errno() : (int64_t)fd;
    }
    case TALK_IO_CWD_LEN: {
        char path[4096];
        return getcwd(path, sizeof path) == NULL ? TALK_EIO : (int64_t)strlen(path);
    }
    case TALK_IO_CWD_COPY: {
        char path[4096];
        if (getcwd(path, sizeof path) == NULL) {
            return TALK_EIO;
        }
        return talk_copy_out(a.v.ptr, path, strlen(path));
    }
    case TALK_IO_GETENV_LEN:
    case TALK_IO_GETENV_COPY: {
        int64_t name_length = b.v.i;
        if (name_length < 0) {
            return name_length;
        }
        char name[1024];
        if ((size_t)name_length >= sizeof name) {
            return TALK_EINVAL;
        }
        memcpy(name, a.v.ptr, (size_t)name_length);
        name[name_length] = '\0';
        const char *value = getenv(name);
        if (value == NULL) {
            return TALK_ENOENT;
        }
        if (op == TALK_IO_GETENV_LEN) {
            return (int64_t)strlen(value);
        }
        return talk_copy_out(c.v.ptr, value, strlen(value));
    }
    case TALK_IO_ARGC:
        return (int64_t)talk_argc;
    case TALK_IO_ARG_LEN: {
        int64_t index = a.v.i;
        if (index < 0) {
            return TALK_EINVAL;
        }
        if (index >= talk_argc) {
            return TALK_ENOENT;
        }
        return (int64_t)strlen(talk_argv[index]);
    }
    case TALK_IO_ARG_COPY: {
        int64_t index = a.v.i;
        if (index < 0) {
            return TALK_EINVAL;
        }
        if (index >= talk_argc) {
            return TALK_ENOENT;
        }
        return talk_copy_out(b.v.ptr, talk_argv[index], strlen(talk_argv[index]));
    }
    case TALK_IO_DIR_COUNT: {
        size_t count = 0;
        char **names = NULL;
        if (talk_read_entries((const char *)a.v.ptr, &names, &count) != 0) {
            return talk_errno();
        }
        talk_free_entries(names, count);
        return (int64_t)count;
    }
    case TALK_IO_DIR_ENTRY_KIND:
    case TALK_IO_DIR_ENTRY_LEN:
    case TALK_IO_DIR_ENTRY_COPY: {
        /* A negative index is a caller error, as it is in the runtime;
         * an index past the end is simply absent. */
        if (b.v.i < 0) {
            return TALK_EINVAL;
        }
        size_t count = 0;
        char **names = NULL;
        const char *path = (const char *)a.v.ptr;
        if (talk_read_entries(path, &names, &count) != 0) {
            return talk_errno();
        }
        int64_t index = b.v.i;
        if ((size_t)index >= count) {
            talk_free_entries(names, count);
            return TALK_ENOENT;
        }
        int64_t result;
        if (op == TALK_IO_DIR_ENTRY_KIND) {
            result = talk_entry_kind(path, names[index]);
        } else if (op == TALK_IO_DIR_ENTRY_LEN) {
            result = (int64_t)strlen(names[index]);
        } else {
            result = talk_copy_out(c.v.ptr, names[index], strlen(names[index]));
        }
        talk_free_entries(names, count);
        return result;
    }
    case TALK_IO_REALPATH_LEN:
    case TALK_IO_REALPATH_COPY: {
        char resolved[4096];
        if (realpath((const char *)a.v.ptr, resolved) == NULL) {
            return talk_errno();
        }
        if (op == TALK_IO_REALPATH_LEN) {
            return (int64_t)strlen(resolved);
        }
        return talk_copy_out(b.v.ptr, resolved, strlen(resolved));
    }
    case TALK_IO_SEEK: {
        off_t position = lseek((int)a.v.i, (off_t)b.v.i, (int)c.v.i);
        return position < 0 ? talk_errno() : (int64_t)position;
    }
    case TALK_IO_FILE_SIZE: {
        struct stat info;
        if (fstat((int)a.v.i, &info) != 0) {
            return talk_errno();
        }
        return (int64_t)info.st_size;
    }
#endif
    default:
        break;
    }
    return TALK_EPERM;
}

/* ---- result rendering ---------------------------------------------- */

/* Render a double the way the runtime does: Rust's `f64::to_string`,
 * which is the shortest decimal that round-trips, always in positional
 * notation, with a trailing ".0" added when the result has no point or
 * exponent.
 *
 * The shortest digit count comes from asking `printf` for successively
 * more significant digits until `strtod` reads the value back exactly;
 * the digits are then laid out positionally by hand, because `%g` would
 * switch to exponent form and `%f` cannot express "shortest".
 */
static void talk_render_double(double value, char *out, size_t capacity) {
    if (value != value) {
        snprintf(out, capacity, "NaN");
        return;
    }
    if (value > DBL_MAX || value < -DBL_MAX) {
        snprintf(out, capacity, value < 0 ? "-inf" : "inf");
        return;
    }

    char scientific[64];
    for (int digits = 0; digits <= 17; digits++) {
        snprintf(scientific, sizeof scientific, "%.*e", digits, value);
        if (strtod(scientific, NULL) == value) {
            break;
        }
    }

    const char *cursor = scientific;
    size_t at = 0;
    if (*cursor == '-') {
        out[at++] = '-';
        cursor++;
    }
    char mantissa[32];
    size_t length = 0;
    for (; *cursor != '\0' && *cursor != 'e'; cursor++) {
        if (*cursor != '.' && length + 1 < sizeof mantissa) {
            mantissa[length++] = *cursor;
        }
    }
    mantissa[length] = '\0';
    /* `value = 0.<mantissa> * 10^point`, so `point` is where the decimal
     * separator falls within the digit string. */
    long point = (*cursor == 'e' ? strtol(cursor + 1, NULL, 10) : 0) + 1;

    if (point <= 0) {
        at += (size_t)snprintf(out + at, capacity - at, "0.");
        for (long zero = 0; zero < -point && at + 1 < capacity; zero++) {
            out[at++] = '0';
        }
        snprintf(out + at, capacity - at, "%s", mantissa);
        return;
    }
    if ((size_t)point >= length) {
        at += (size_t)snprintf(out + at, capacity - at, "%s", mantissa);
        for (size_t zero = length; zero < (size_t)point && at + 1 < capacity; zero++) {
            out[at++] = '0';
        }
        /* Integral: the runtime appends the point itself. */
        snprintf(out + at, capacity - at, ".0");
        return;
    }
    snprintf(out + at, capacity - at, "%.*s.%s", (int)point, mantissa, mantissa + point);
}

/* ---- rendering a result -------------------------------------------
 *
 * The same shapes the runtime's `render_value` produces, so a program
 * whose result is a record, an enum case, or a string prints identically
 * whichever target ran it.
 *
 * Two values cannot match by construction: `RawPtr(n)` and `<object #n>`
 * print the runtime's simulated address and arena index. Object identity
 * is recovered from the allocation ordinal, which counts the same way;
 * a raw pointer's address cannot be, and is rendered as this target's.
 */

typedef struct {
    char *data;
    size_t len;
    size_t cap;
} TalkOut;

static void talk_out_push(TalkOut *out, const char *bytes, size_t len) {
    if (out->len + len + 1 > out->cap) {
        size_t grown = out->cap == 0 ? 128 : out->cap;
        while (grown < out->len + len + 1) {
            grown *= 2;
        }
        char *data = (char *)realloc(out->data, grown);
        if (data == NULL) {
            talk_trap("out of memory");
        }
        out->data = data;
        out->cap = grown;
    }
    memcpy(out->data + out->len, bytes, len);
    out->len += len;
    out->data[out->len] = '\0';
}

static void talk_out_text(TalkOut *out, const char *text) {
    talk_out_push(out, text, strlen(text));
}

static const TalkTypeInfo *talk_type_of(uint32_t symbol) {
    if (symbol == 0 || symbol >= talk_type_count) {
        return NULL;
    }
    return &talk_types[symbol];
}

/* The length of the well-formed UTF-8 sequence starting at `bytes`, or
 * zero with `*bad` set to the maximal invalid subpart -- the same split
 * Rust's `from_utf8_lossy` makes, so each invalid subpart becomes exactly
 * one replacement character. */
static size_t talk_utf8_step(const unsigned char *bytes, size_t available, size_t *bad) {
    unsigned char lead = bytes[0];
    if (lead < 0x80) {
        return 1;
    }
    unsigned char low = 0x80, high = 0xBF;
    size_t width;
    if (lead >= 0xC2 && lead <= 0xDF) {
        width = 2;
    } else if (lead >= 0xE0 && lead <= 0xEF) {
        width = 3;
        if (lead == 0xE0) {
            low = 0xA0;
        } else if (lead == 0xED) {
            /* Surrogates are not scalar values. */
            high = 0x9F;
        }
    } else if (lead >= 0xF0 && lead <= 0xF4) {
        width = 4;
        if (lead == 0xF0) {
            low = 0x90;
        } else if (lead == 0xF4) {
            high = 0x8F;
        }
    } else {
        *bad = 1;
        return 0;
    }
    for (size_t index = 1; index < width; index++) {
        if (index >= available) {
            /* Truncated at the end of input: the whole prefix is one
             * invalid subpart. */
            *bad = available;
            return 0;
        }
        unsigned char byte = bytes[index];
        unsigned char floor = index == 1 ? low : 0x80;
        unsigned char ceiling = index == 1 ? high : 0xBF;
        if (byte < floor || byte > ceiling) {
            *bad = index;
            return 0;
        }
    }
    return width;
}

/* The core String layout: `String { Storage { base }, byte_count, .. }`.
 *
 * Rendered the way the runtime renders it, which converts through
 * `String::from_utf8_lossy` first: a Talk string is bytes, and slicing
 * one mid-character can leave a sequence that is not valid UTF-8. Each
 * maximal invalid subpart becomes one U+FFFD rather than reaching the
 * output raw. */
static void talk_render_string(TalkOut *out, TalkAgg *string) {
    talk_out_text(out, "\"");
    if (string->len >= 2) {
        const unsigned char *base = string->fields[0].v.ptr;
        int64_t signed_count = string->fields[1].v.i;
        size_t count = signed_count > 0 ? (size_t)signed_count : 0;
        size_t index = 0;
        while (index < count) {
            size_t bad = 0;
            size_t width = talk_utf8_step(base + index, count - index, &bad);
            if (width == 0) {
                talk_out_text(out, "\xEF\xBF\xBD");
                index += bad;
                continue;
            }
            if (width == 1) {
                char byte = (char)base[index];
                switch (byte) {
                case '\\': talk_out_text(out, "\\\\"); break;
                case '"': talk_out_text(out, "\\\""); break;
                case '\n': talk_out_text(out, "\\n"); break;
                case '\t': talk_out_text(out, "\\t"); break;
                case '\r': talk_out_text(out, "\\r"); break;
                default: talk_out_push(out, &byte, 1); break;
                }
            } else {
                talk_out_push(out, (const char *)(base + index), width);
            }
            index += width;
        }
    }
    talk_out_text(out, "\"");
}

static void talk_render(TalkOut *out, TalkValue value) {
    char scratch[512];
    switch (value.tag) {
    case TALK_UNIT:
        talk_out_text(out, "()");
        return;
    case TALK_BOOL:
        talk_out_text(out, value.v.i ? "true" : "false");
        return;
    case TALK_INT:
    case TALK_BYTE:
        snprintf(scratch, sizeof scratch, "%" PRId64, value.v.i);
        talk_out_text(out, scratch);
        return;
    case TALK_FLOAT:
        talk_render_double(value.v.f, scratch, sizeof scratch);
        talk_out_text(out, scratch);
        return;
    case TALK_PTR:
        snprintf(scratch, sizeof scratch, "RawPtr(%" PRIuPTR ")", (uintptr_t)value.v.ptr);
        talk_out_text(out, scratch);
        return;
    case TALK_CLOSURE:
        talk_out_text(out, "<func>");
        return;
    case TALK_CELL:
        talk_out_text(out, "<cell>");
        return;
    case TALK_CONT:
        talk_out_text(out, "<continuation>");
        return;
    case TALK_OBJECT:
        /* Shallow: a structural walk would cycle through the graph. */
        snprintf(scratch, sizeof scratch, "<object #%" PRIu64 ">", value.v.obj->ordinal);
        talk_out_text(out, scratch);
        return;
    case TALK_NATIVE:
        /* Rendering is cold: convert to the tagged form the renderer
         * walks (identity from the box header, shape from the layout). */
        talk_render(out, talk_native_retag(value));
        return;
    case TALK_AGG:
        break;
    default:
        talk_out_text(out, "<value>");
        return;
    }

    TalkAgg *agg = value.v.agg;
    const TalkTypeInfo *info = talk_type_of(agg->symbol);
    if (info != NULL && info->kind == TALK_TYPE_STRING) {
        talk_render_string(out, agg);
        return;
    }
    if (info != NULL && info->kind == TALK_TYPE_EXISTENTIAL) {
        /* Through to the payload; the witnesses are representation. */
        if (agg->len > 0) {
            talk_render(out, agg->fields[0]);
        }
        return;
    }
    /* A layout-less container (or a table miss): render the slots as a
     * bare tuple — nothing user-visible reaches here. */
    if (agg->layout == TALK_DYN || agg->layout >= talk_layout_count) {
        talk_out_text(out, "(");
        for (uint32_t index = 0; index < agg->len; index++) {
            if (index > 0) {
                talk_out_text(out, ", ");
            }
            talk_render(out, agg->fields[index]);
        }
        talk_out_text(out, ")");
        return;
    }
    /* Structure comes from the layout table, names from the type table
     * (ADR 0046): members walk by field, not by slot, so spliced
     * children render whole. */
    const TalkLayoutInfo *shape = &talk_layouts[agg->layout];
    if (shape->is_sum) {
        uint32_t tag = (uint32_t)agg->fields[0].v.i;
        if (info != NULL) {
            talk_out_text(out, info->name);
            talk_out_text(out, ".");
            if (info->kind == TALK_TYPE_ENUM && tag < info->member_count) {
                talk_out_text(out, info->members[tag]);
            } else {
                snprintf(scratch, sizeof scratch, "case%" PRIu32, tag);
                talk_out_text(out, scratch);
            }
        } else {
            snprintf(scratch, sizeof scratch, "case%" PRIu32, tag);
            talk_out_text(out, scratch);
        }
        if (tag >= shape->variant_count) {
            return;
        }
        uint32_t first = shape->variant_starts[tag];
        uint32_t last = shape->variant_starts[tag + 1];
        if (first == last) {
            return;
        }
        talk_out_text(out, "(");
        for (uint32_t field = first; field < last; field++) {
            if (field > first) {
                talk_out_text(out, ", ");
            }
            talk_render(out, talk_field_at(value, &shape->fields[field]));
        }
        talk_out_text(out, ")");
        return;
    }
    if (info == NULL) {
        /* A tuple or anonymous product. */
        talk_out_text(out, "(");
        for (uint32_t field = 0; field < shape->field_count; field++) {
            if (field > 0) {
                talk_out_text(out, ", ");
            }
            talk_render(out, talk_field_at(value, &shape->fields[field]));
        }
        talk_out_text(out, ")");
        return;
    }
    talk_out_text(out, info->name);
    talk_out_text(out, "(");
    for (uint32_t field = 0; field < shape->field_count; field++) {
        if (field > 0) {
            talk_out_text(out, ", ");
        }
        if (field < info->member_count) {
            talk_out_text(out, info->members[field]);
            talk_out_text(out, ": ");
        }
        talk_render(out, talk_field_at(value, &shape->fields[field]));
    }
    talk_out_text(out, ")");
}

/* Matches how `talk run` renders a result: Unit prints nothing.
 *
 * A scalar result owns no buffers, so every allocation the run made must
 * be gone. `execute` in the Rust driver fails a run whose live-allocation
 * count exceeds its result's footprint; this is the same check, applied
 * when the result cannot be holding anything itself. */
static int talk_print(TalkValue value) {
    if (value.tag != TALK_UNIT) {
        TalkOut out = {NULL, 0, 0};
        talk_render(&out, value);
        printf("%s\n", out.data == NULL ? "" : out.data);
        free(out.data);
    }
    int owns_nothing = value.tag == TALK_UNIT || value.tag == TALK_BOOL
                       || value.tag == TALK_INT || value.tag == TALK_BYTE
                       || value.tag == TALK_FLOAT;
    size_t live_allocations = atomic_load_explicit(&talk_live_allocations, memory_order_relaxed);
    size_t live_objects = atomic_load_explicit(&talk_live_objects, memory_order_relaxed);
    if (owns_nothing && (live_allocations != 0 || live_objects != 0)) {
        fprintf(stderr, "talk: resource leak: %zu live allocations, %zu live objects at exit\n",
                live_allocations, live_objects);
        return 1;
    }
    return 0;
}
